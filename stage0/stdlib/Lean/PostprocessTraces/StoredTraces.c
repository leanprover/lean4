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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_EnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_pp_macroStack;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages(lean_object*, lean_object*, lean_object*);
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
v___x_141_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
v___x_146_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_146_, 10, v___x_144_);
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
lean_object* v___x_164_; lean_object* v_toCold_165_; lean_object* v_env_166_; lean_object* v_options_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_164_ = lean_st_ref_get(v___y_162_);
v_toCold_165_ = lean_ctor_get(v___y_161_, 0);
v_env_166_ = lean_ctor_get(v___x_164_, 0);
lean_inc_ref(v_env_166_);
lean_dec(v___x_164_);
v_options_167_ = lean_ctor_get(v_toCold_165_, 2);
v___x_168_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_169_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_167_);
v___x_170_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_170_, 0, v_env_166_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
lean_ctor_set(v___x_170_, 2, v___x_169_);
lean_ctor_set(v___x_170_, 3, v_options_167_);
v___x_171_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_msgData_160_);
v___x_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___boxed(lean_object* v_msgData_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0(v_msgData_173_, v___y_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(lean_object* v_msg_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v_ref_182_; lean_object* v___x_183_; lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_192_; 
v_ref_182_ = lean_ctor_get(v___y_179_, 2);
v___x_183_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0(v_msg_178_, v___y_179_, v___y_180_);
v_a_184_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_192_ == 0)
{
v___x_186_ = v___x_183_;
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_183_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_192_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_inc(v_ref_182_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v_ref_182_);
lean_ctor_set(v___x_188_, 1, v_a_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set_tag(v___x_186_, 1);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_190_ = v___x_186_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg___boxed(lean_object* v_msg_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v_msg_193_, v___y_194_, v___y_195_);
lean_dec(v___y_195_);
lean_dec_ref(v___y_194_);
return v_res_197_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_findStoredTrace___closed__1(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = ((lean_object*)(l_Lean_PostprocessTraces_findStoredTrace___closed__0));
v___x_200_ = l_Lean_stringToMessageData(v___x_199_);
return v___x_200_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_findStoredTrace___closed__3(void){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = ((lean_object*)(l_Lean_PostprocessTraces_findStoredTrace___closed__2));
v___x_203_ = l_Lean_stringToMessageData(v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace(lean_object* v_declName_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_208_; lean_object* v_env_209_; lean_object* v___x_210_; 
v___x_208_ = lean_st_ref_get(v_a_206_);
v_env_209_ = lean_ctor_get(v___x_208_, 0);
lean_inc_ref(v_env_209_);
lean_dec(v___x_208_);
v___x_210_ = l_Lean_PostprocessTraces_findStoredTrace_x3f(v_env_209_, v_declName_204_);
if (lean_obj_tag(v___x_210_) == 1)
{
lean_object* v_val_211_; lean_object* v___x_213_; uint8_t v_isShared_214_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_declName_204_);
v_val_211_ = lean_ctor_get(v___x_210_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_210_);
if (v_isSharedCheck_218_ == 0)
{
v___x_213_ = v___x_210_;
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
else
{
lean_inc(v_val_211_);
lean_dec(v___x_210_);
v___x_213_ = lean_box(0);
v_isShared_214_ = v_isSharedCheck_218_;
goto v_resetjp_212_;
}
v_resetjp_212_:
{
lean_object* v___x_216_; 
if (v_isShared_214_ == 0)
{
lean_ctor_set_tag(v___x_213_, 0);
v___x_216_ = v___x_213_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_val_211_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v___x_210_);
v___x_219_ = lean_obj_once(&l_Lean_PostprocessTraces_findStoredTrace___closed__1, &l_Lean_PostprocessTraces_findStoredTrace___closed__1_once, _init_l_Lean_PostprocessTraces_findStoredTrace___closed__1);
v___x_220_ = l_Lean_MessageData_ofName(v_declName_204_);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_obj_once(&l_Lean_PostprocessTraces_findStoredTrace___closed__3, &l_Lean_PostprocessTraces_findStoredTrace___closed__3_once, _init_l_Lean_PostprocessTraces_findStoredTrace___closed__3);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v___x_223_, v_a_205_, v_a_206_);
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace___boxed(lean_object* v_declName_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_PostprocessTraces_findStoredTrace(v_declName_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0(lean_object* v_00_u03b1_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v_msg_231_, v___y_232_, v___y_233_);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___boxed(lean_object* v_00_u03b1_236_, lean_object* v_msg_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0(v_00_u03b1_236_, v_msg_237_, v___y_238_, v___y_239_);
lean_dec(v___y_239_);
lean_dec_ref(v___y_238_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___lam__0(lean_object* v_declName_242_, lean_object* v_t_243_, lean_object* v_x_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_242_, v_t_243_, v_x_244_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__0(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_246_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0);
v___x_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
return v___x_247_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__1(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__0, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__0);
v___x_249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg(lean_object* v_declName_250_, lean_object* v_t_251_, lean_object* v_a_252_){
_start:
{
lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v_env_256_; lean_object* v_nextMacroScope_257_; lean_object* v_ngen_258_; lean_object* v_auxDeclNGen_259_; lean_object* v_traceState_260_; lean_object* v_recordedDeps_261_; lean_object* v_messages_262_; lean_object* v_infoState_263_; lean_object* v_snapshotTasks_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_279_; 
v___f_254_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_storeTraces___redArg___lam__0), 3, 2);
lean_closure_set(v___f_254_, 0, v_declName_250_);
lean_closure_set(v___f_254_, 1, v_t_251_);
v___x_255_ = lean_st_ref_take(v_a_252_);
v_env_256_ = lean_ctor_get(v___x_255_, 0);
v_nextMacroScope_257_ = lean_ctor_get(v___x_255_, 1);
v_ngen_258_ = lean_ctor_get(v___x_255_, 2);
v_auxDeclNGen_259_ = lean_ctor_get(v___x_255_, 3);
v_traceState_260_ = lean_ctor_get(v___x_255_, 4);
v_recordedDeps_261_ = lean_ctor_get(v___x_255_, 6);
v_messages_262_ = lean_ctor_get(v___x_255_, 7);
v_infoState_263_ = lean_ctor_get(v___x_255_, 8);
v_snapshotTasks_264_ = lean_ctor_get(v___x_255_, 9);
v_isSharedCheck_279_ = !lean_is_exclusive(v___x_255_);
if (v_isSharedCheck_279_ == 0)
{
lean_object* v_unused_280_; 
v_unused_280_ = lean_ctor_get(v___x_255_, 5);
lean_dec(v_unused_280_);
v___x_266_ = v___x_255_;
v_isShared_267_ = v_isSharedCheck_279_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_snapshotTasks_264_);
lean_inc(v_infoState_263_);
lean_inc(v_messages_262_);
lean_inc(v_recordedDeps_261_);
lean_inc(v_traceState_260_);
lean_inc(v_auxDeclNGen_259_);
lean_inc(v_ngen_258_);
lean_inc(v_nextMacroScope_257_);
lean_inc(v_env_256_);
lean_dec(v___x_255_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_279_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v_asyncMode_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_268_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt;
v_asyncMode_269_ = lean_ctor_get(v___x_268_, 2);
v___x_270_ = lean_box(0);
v___x_271_ = lean_box(0);
v___x_272_ = l_Lean_EnvExtension_modifyState___redArg(v___x_268_, v_env_256_, v___f_254_, v_asyncMode_269_, v___x_271_);
v___x_273_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__1, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__1_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__1);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 5, v___x_273_);
lean_ctor_set(v___x_266_, 0, v___x_272_);
v___x_275_ = v___x_266_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_278_; 
v_reuseFailAlloc_278_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_278_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_278_, 1, v_nextMacroScope_257_);
lean_ctor_set(v_reuseFailAlloc_278_, 2, v_ngen_258_);
lean_ctor_set(v_reuseFailAlloc_278_, 3, v_auxDeclNGen_259_);
lean_ctor_set(v_reuseFailAlloc_278_, 4, v_traceState_260_);
lean_ctor_set(v_reuseFailAlloc_278_, 5, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_278_, 6, v_recordedDeps_261_);
lean_ctor_set(v_reuseFailAlloc_278_, 7, v_messages_262_);
lean_ctor_set(v_reuseFailAlloc_278_, 8, v_infoState_263_);
lean_ctor_set(v_reuseFailAlloc_278_, 9, v_snapshotTasks_264_);
v___x_275_ = v_reuseFailAlloc_278_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_st_ref_put(v_a_252_, v___x_275_);
v___x_277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_270_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___boxed(lean_object* v_declName_281_, lean_object* v_t_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Lean_PostprocessTraces_storeTraces___redArg(v_declName_281_, v_t_282_, v_a_283_);
lean_dec(v_a_283_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces(lean_object* v_declName_286_, lean_object* v_t_287_, lean_object* v_a_288_, lean_object* v_a_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_PostprocessTraces_storeTraces___redArg(v_declName_286_, v_t_287_, v_a_289_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___boxed(lean_object* v_declName_292_, lean_object* v_t_293_, lean_object* v_a_294_, lean_object* v_a_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_PostprocessTraces_storeTraces(v_declName_292_, v_t_293_, v_a_294_, v_a_295_);
lean_dec(v_a_295_);
lean_dec_ref(v_a_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(size_t v_sz_298_, size_t v_i_299_, lean_object* v_bs_300_){
_start:
{
uint8_t v___x_301_; 
v___x_301_ = lean_usize_dec_lt(v_i_299_, v_sz_298_);
if (v___x_301_ == 0)
{
return v_bs_300_;
}
else
{
lean_object* v_v_302_; lean_object* v___x_303_; lean_object* v_bs_x27_304_; lean_object* v___x_305_; size_t v___x_306_; size_t v___x_307_; lean_object* v___x_308_; 
v_v_302_ = lean_array_uget(v_bs_300_, v_i_299_);
v___x_303_ = lean_unsigned_to_nat(0u);
v_bs_x27_304_ = lean_array_uset(v_bs_300_, v_i_299_, v___x_303_);
v___x_305_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData(v_v_302_);
v___x_306_ = ((size_t)1ULL);
v___x_307_ = lean_usize_add(v_i_299_, v___x_306_);
v___x_308_ = lean_array_uset(v_bs_x27_304_, v_i_299_, v___x_305_);
v_i_299_ = v___x_307_;
v_bs_300_ = v___x_308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0___boxed(lean_object* v_sz_310_, lean_object* v_i_311_, lean_object* v_bs_312_){
_start:
{
size_t v_sz_boxed_313_; size_t v_i_boxed_314_; lean_object* v_res_315_; 
v_sz_boxed_313_ = lean_unbox_usize(v_sz_310_);
lean_dec(v_sz_310_);
v_i_boxed_314_ = lean_unbox_usize(v_i_311_);
lean_dec(v_i_311_);
v_res_315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(v_sz_boxed_313_, v_i_boxed_314_, v_bs_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(lean_object* v_as_318_, size_t v_i_319_, size_t v_stop_320_, lean_object* v_b_321_){
_start:
{
lean_object* v___y_323_; uint8_t v___x_327_; 
v___x_327_ = lean_usize_dec_eq(v_i_319_, v_stop_320_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v_data_329_; lean_object* v___x_330_; 
v___x_328_ = lean_array_uget_borrowed(v_as_318_, v_i_319_);
v_data_329_ = lean_ctor_get(v___x_328_, 4);
lean_inc(v_data_329_);
v___x_330_ = l_Lean_Elab_PostprocessTraces_traceContainer_x3f(v_data_329_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___closed__0));
v___x_332_ = l_Array_append___redArg(v_b_321_, v___x_331_);
v___y_323_ = v___x_332_;
goto v___jp_322_;
}
else
{
lean_object* v_val_333_; lean_object* v_snd_334_; size_t v_sz_335_; size_t v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_val_333_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_val_333_);
lean_dec_ref_known(v___x_330_, 1);
v_snd_334_ = lean_ctor_get(v_val_333_, 1);
lean_inc(v_snd_334_);
lean_dec(v_val_333_);
v_sz_335_ = lean_array_size(v_snd_334_);
v___x_336_ = ((size_t)0ULL);
v___x_337_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(v_sz_335_, v___x_336_, v_snd_334_);
v___x_338_ = l_Array_append___redArg(v_b_321_, v___x_337_);
lean_dec_ref(v___x_337_);
v___y_323_ = v___x_338_;
goto v___jp_322_;
}
}
else
{
return v_b_321_;
}
v___jp_322_:
{
size_t v___x_324_; size_t v___x_325_; 
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_i_319_, v___x_324_);
v_i_319_ = v___x_325_;
v_b_321_ = v___y_323_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___boxed(lean_object* v_as_339_, lean_object* v_i_340_, lean_object* v_stop_341_, lean_object* v_b_342_){
_start:
{
size_t v_i_boxed_343_; size_t v_stop_boxed_344_; lean_object* v_res_345_; 
v_i_boxed_343_ = lean_unbox_usize(v_i_340_);
lean_dec(v_i_340_);
v_stop_boxed_344_ = lean_unbox_usize(v_stop_341_);
lean_dec(v_stop_341_);
v_res_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(v_as_339_, v_i_boxed_343_, v_stop_boxed_344_, v_b_342_);
lean_dec_ref(v_as_339_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_trees(lean_object* v_t_348_){
_start:
{
lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = ((lean_object*)(l_Lean_PostprocessTraces_StoredTrace_trees___closed__0));
v___x_351_ = lean_array_get_size(v_t_348_);
v___x_352_ = lean_nat_dec_lt(v___x_349_, v___x_351_);
if (v___x_352_ == 0)
{
return v___x_350_;
}
else
{
size_t v___x_353_; size_t v___x_354_; lean_object* v___x_355_; 
v___x_353_ = ((size_t)0ULL);
v___x_354_ = lean_usize_of_nat(v___x_351_);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(v_t_348_, v___x_353_, v___x_354_, v___x_350_);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_trees___boxed(lean_object* v_t_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_PostprocessTraces_StoredTrace_trees(v_t_356_);
lean_dec_ref(v_t_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(lean_object* v_post_358_, lean_object* v_as_359_, size_t v_i_360_, size_t v_stop_361_, lean_object* v_b_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_a_367_; uint8_t v___x_371_; 
v___x_371_ = lean_usize_dec_eq(v_i_360_, v_stop_361_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_372_ = lean_array_uget_borrowed(v_as_359_, v_i_360_);
lean_inc(v___x_372_);
lean_inc_ref(v_post_358_);
v___x_373_ = l_Lean_Elab_PostprocessTraces_postprocessMessage(v_post_358_, v___x_372_, v___y_363_, v___y_364_);
if (lean_obj_tag(v___x_373_) == 0)
{
lean_object* v_a_374_; 
v_a_374_ = lean_ctor_get(v___x_373_, 0);
lean_inc(v_a_374_);
lean_dec_ref_known(v___x_373_, 1);
if (lean_obj_tag(v_a_374_) == 0)
{
v_a_367_ = v_b_362_;
goto v___jp_366_;
}
else
{
lean_object* v_val_375_; lean_object* v___x_376_; 
v_val_375_ = lean_ctor_get(v_a_374_, 0);
lean_inc(v_val_375_);
lean_dec_ref_known(v_a_374_, 1);
v___x_376_ = lean_array_push(v_b_362_, v_val_375_);
v_a_367_ = v___x_376_;
goto v___jp_366_;
}
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_384_; 
lean_dec_ref(v_b_362_);
lean_dec_ref(v_post_358_);
v_a_377_ = lean_ctor_get(v___x_373_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_373_);
if (v_isSharedCheck_384_ == 0)
{
v___x_379_ = v___x_373_;
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_373_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_384_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v___x_382_; 
if (v_isShared_380_ == 0)
{
v___x_382_ = v___x_379_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v_a_377_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
else
{
lean_object* v___x_385_; 
lean_dec_ref(v_post_358_);
v___x_385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_385_, 0, v_b_362_);
return v___x_385_;
}
v___jp_366_:
{
size_t v___x_368_; size_t v___x_369_; 
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_add(v_i_360_, v___x_368_);
v_i_360_ = v___x_369_;
v_b_362_ = v_a_367_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0___boxed(lean_object* v_post_386_, lean_object* v_as_387_, lean_object* v_i_388_, lean_object* v_stop_389_, lean_object* v_b_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
size_t v_i_boxed_394_; size_t v_stop_boxed_395_; lean_object* v_res_396_; 
v_i_boxed_394_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_stop_boxed_395_ = lean_unbox_usize(v_stop_389_);
lean_dec(v_stop_389_);
v_res_396_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(v_post_386_, v_as_387_, v_i_boxed_394_, v_stop_boxed_395_, v_b_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec_ref(v_as_387_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(lean_object* v_post_399_, lean_object* v_as_400_, lean_object* v_start_401_, lean_object* v_stop_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0));
v___x_407_ = lean_nat_dec_lt(v_start_401_, v_stop_402_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; 
lean_dec_ref(v_post_399_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_406_);
return v___x_408_;
}
else
{
lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_409_ = lean_array_get_size(v_as_400_);
v___x_410_ = lean_nat_dec_le(v_stop_402_, v___x_409_);
if (v___x_410_ == 0)
{
uint8_t v___x_411_; 
v___x_411_ = lean_nat_dec_lt(v_start_401_, v___x_409_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_dec_ref(v_post_399_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v___x_406_);
return v___x_412_;
}
else
{
size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; 
v___x_413_ = lean_usize_of_nat(v_start_401_);
v___x_414_ = lean_usize_of_nat(v___x_409_);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(v_post_399_, v_as_400_, v___x_413_, v___x_414_, v___x_406_, v___y_403_, v___y_404_);
return v___x_415_;
}
}
else
{
size_t v___x_416_; size_t v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_usize_of_nat(v_start_401_);
v___x_417_ = lean_usize_of_nat(v_stop_402_);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(v_post_399_, v_as_400_, v___x_416_, v___x_417_, v___x_406_, v___y_403_, v___y_404_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___boxed(lean_object* v_post_419_, lean_object* v_as_420_, lean_object* v_start_421_, lean_object* v_stop_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(v_post_419_, v_as_420_, v_start_421_, v_stop_422_, v___y_423_, v___y_424_);
lean_dec(v___y_424_);
lean_dec_ref(v___y_423_);
lean_dec(v_stop_422_);
lean_dec(v_start_421_);
lean_dec_ref(v_as_420_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_postprocess(lean_object* v_t_427_, lean_object* v_post_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_array_get_size(v_t_427_);
v___x_434_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(v_post_428_, v_t_427_, v___x_432_, v___x_433_, v_a_429_, v_a_430_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_442_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_442_ == 0)
{
v___x_437_ = v___x_434_;
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
else
{
lean_inc(v_a_435_);
lean_dec(v___x_434_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_442_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_440_; 
if (v_isShared_438_ == 0)
{
v___x_440_ = v___x_437_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_a_435_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
return v___x_440_;
}
}
}
else
{
lean_object* v_a_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_450_; 
v_a_443_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_450_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_450_ == 0)
{
v___x_445_ = v___x_434_;
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_a_443_);
lean_dec(v___x_434_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_450_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_448_; 
if (v_isShared_446_ == 0)
{
v___x_448_ = v___x_445_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v_a_443_);
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
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_postprocess___boxed(lean_object* v_t_451_, lean_object* v_post_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Lean_PostprocessTraces_StoredTrace_postprocess(v_t_451_, v_post_452_, v_a_453_, v_a_454_);
lean_dec(v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec_ref(v_t_451_);
return v_res_456_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; 
v___x_457_ = lean_box(0);
v___x_458_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_459_, 0, v___x_458_);
lean_ctor_set(v___x_459_, 1, v___x_457_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg(){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0);
v___x_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___boxed(lean_object* v___y_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0(lean_object* v_00_u03b1_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_469_; 
v___x_469_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___boxed(lean_object* v_00_u03b1_470_, lean_object* v___y_471_, lean_object* v___y_472_, lean_object* v___y_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0(v_00_u03b1_470_, v___y_471_, v___y_472_);
lean_dec(v___y_472_);
lean_dec_ref(v___y_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(lean_object* v_as_475_, size_t v_i_476_, size_t v_stop_477_, lean_object* v_b_478_){
_start:
{
uint8_t v___x_479_; 
v___x_479_ = lean_usize_dec_eq(v_i_476_, v_stop_477_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; size_t v___x_482_; size_t v___x_483_; 
v___x_480_ = lean_array_uget_borrowed(v_as_475_, v_i_476_);
lean_inc(v___x_480_);
v___x_481_ = l_Lean_MessageLog_add(v___x_480_, v_b_478_);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_add(v_i_476_, v___x_482_);
v_i_476_ = v___x_483_;
v_b_478_ = v___x_481_;
goto _start;
}
else
{
return v_b_478_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5___boxed(lean_object* v_as_485_, lean_object* v_i_486_, lean_object* v_stop_487_, lean_object* v_b_488_){
_start:
{
size_t v_i_boxed_489_; size_t v_stop_boxed_490_; lean_object* v_res_491_; 
v_i_boxed_489_ = lean_unbox_usize(v_i_486_);
lean_dec(v_i_486_);
v_stop_boxed_490_ = lean_unbox_usize(v_stop_487_);
lean_dec(v_stop_487_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_as_485_, v_i_boxed_489_, v_stop_boxed_490_, v_b_488_);
lean_dec_ref(v_as_485_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(lean_object* v_as_492_, size_t v_i_493_, size_t v_stop_494_, lean_object* v_b_495_){
_start:
{
lean_object* v___y_497_; uint8_t v___x_501_; 
v___x_501_ = lean_usize_dec_eq(v_i_493_, v_stop_494_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_502_ = lean_array_uget_borrowed(v_as_492_, v_i_493_);
v___x_503_ = l_Lean_Message_isTrace(v___x_502_);
if (v___x_503_ == 0)
{
v___y_497_ = v_b_495_;
goto v___jp_496_;
}
else
{
lean_object* v___x_504_; 
lean_inc(v___x_502_);
v___x_504_ = lean_array_push(v_b_495_, v___x_502_);
v___y_497_ = v___x_504_;
goto v___jp_496_;
}
}
else
{
return v_b_495_;
}
v___jp_496_:
{
size_t v___x_498_; size_t v___x_499_; 
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_493_, v___x_498_);
v_i_493_ = v___x_499_;
v_b_495_ = v___y_497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4___boxed(lean_object* v_as_505_, lean_object* v_i_506_, lean_object* v_stop_507_, lean_object* v_b_508_){
_start:
{
size_t v_i_boxed_509_; size_t v_stop_boxed_510_; lean_object* v_res_511_; 
v_i_boxed_509_ = lean_unbox_usize(v_i_506_);
lean_dec(v_i_506_);
v_stop_boxed_510_ = lean_unbox_usize(v_stop_507_);
lean_dec(v_stop_507_);
v_res_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_as_505_, v_i_boxed_509_, v_stop_boxed_510_, v_b_508_);
lean_dec_ref(v_as_505_);
return v_res_511_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__7(lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
if (lean_obj_tag(v_a_512_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = l_List_reverse___redArg(v_a_513_);
return v___x_514_;
}
else
{
lean_object* v_head_515_; lean_object* v_tail_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_525_; 
v_head_515_ = lean_ctor_get(v_a_512_, 0);
v_tail_516_ = lean_ctor_get(v_a_512_, 1);
v_isSharedCheck_525_ = !lean_is_exclusive(v_a_512_);
if (v_isSharedCheck_525_ == 0)
{
v___x_518_ = v_a_512_;
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_tail_516_);
lean_inc(v_head_515_);
lean_dec(v_a_512_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_525_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_522_; 
v___x_520_ = l_Lean_mkLevelParam(v_head_515_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 1, v_a_513_);
lean_ctor_set(v___x_518_, 0, v___x_520_);
v___x_522_ = v___x_518_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_a_513_);
v___x_522_ = v_reuseFailAlloc_524_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
v_a_512_ = v_tail_516_;
v_a_513_ = v___x_522_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__0));
v___x_528_ = l_Lean_stringToMessageData(v___x_527_);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; 
v___x_530_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__2));
v___x_531_ = l_Lean_stringToMessageData(v___x_530_);
return v___x_531_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_533_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__4));
v___x_534_ = l_Lean_stringToMessageData(v___x_533_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7(void){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
v___x_536_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__6));
v___x_537_ = l_Lean_stringToMessageData(v___x_536_);
return v___x_537_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9(void){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__8));
v___x_540_ = l_Lean_stringToMessageData(v___x_539_);
return v___x_540_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__10));
v___x_543_ = l_Lean_stringToMessageData(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13(void){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__12));
v___x_546_ = l_Lean_stringToMessageData(v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(lean_object* v_msg_547_, lean_object* v_declHint_548_, lean_object* v___y_549_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_env_553_; uint8_t v___x_554_; 
v___x_551_ = lean_box(0);
v___x_552_ = lean_st_ref_get(v___y_549_);
v_env_553_ = lean_ctor_get(v___x_552_, 0);
lean_inc_ref(v_env_553_);
lean_dec(v___x_552_);
v___x_554_ = l_Lean_Name_isAnonymous(v_declHint_548_);
if (v___x_554_ == 0)
{
uint8_t v_isExporting_555_; 
v_isExporting_555_ = lean_ctor_get_uint8(v_env_553_, sizeof(void*)*8);
if (v_isExporting_555_ == 0)
{
lean_object* v___x_556_; 
lean_dec_ref(v_env_553_);
lean_dec(v_declHint_548_);
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v_msg_547_);
return v___x_556_;
}
else
{
lean_object* v___x_557_; uint8_t v___x_558_; 
lean_inc_ref(v_env_553_);
v___x_557_ = l_Lean_Environment_setExporting(v_env_553_, v___x_554_);
lean_inc(v_declHint_548_);
lean_inc_ref(v___x_557_);
v___x_558_ = l_Lean_Environment_contains(v___x_557_, v_declHint_548_, v_isExporting_555_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; 
lean_dec_ref(v___x_557_);
lean_dec_ref(v_env_553_);
lean_dec(v_declHint_548_);
v___x_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_559_, 0, v_msg_547_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v_c_565_; lean_object* v___x_566_; 
v___x_560_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_561_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
v___x_562_ = l_Lean_Options_empty;
v___x_563_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_563_, 0, v___x_557_);
lean_ctor_set(v___x_563_, 1, v___x_560_);
lean_ctor_set(v___x_563_, 2, v___x_561_);
lean_ctor_set(v___x_563_, 3, v___x_562_);
lean_inc(v_declHint_548_);
v___x_564_ = l_Lean_MessageData_ofConstName(v_declHint_548_, v___x_554_);
v_c_565_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_565_, 0, v___x_563_);
lean_ctor_set(v_c_565_, 1, v___x_564_);
v___x_566_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_553_, v_declHint_548_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec_ref(v_env_553_);
lean_dec(v_declHint_548_);
v___x_567_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_568_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v_c_565_);
v___x_569_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3);
v___x_570_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_569_);
v___x_571_ = l_Lean_MessageData_note(v___x_570_);
v___x_572_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_572_, 0, v_msg_547_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
else
{
lean_object* v_val_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_608_; 
v_val_574_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_608_ == 0)
{
v___x_576_ = v___x_566_;
v_isShared_577_ = v_isSharedCheck_608_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_val_574_);
lean_dec(v___x_566_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_608_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v_mod_580_; uint8_t v___x_581_; 
v___x_578_ = l_Lean_Environment_header(v_env_553_);
lean_dec_ref(v_env_553_);
v___x_579_ = l_Lean_EnvironmentHeader_moduleNames(v___x_578_);
v_mod_580_ = lean_array_get(v___x_551_, v___x_579_, v_val_574_);
lean_dec(v_val_574_);
lean_dec_ref(v___x_579_);
v___x_581_ = l_Lean_isPrivateName(v_declHint_548_);
lean_dec(v_declHint_548_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v___x_582_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5);
v___x_583_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v_c_565_);
v___x_584_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7);
v___x_585_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_585_, 0, v___x_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v___x_586_ = l_Lean_MessageData_ofName(v_mod_580_);
v___x_587_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_585_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
v___x_588_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9);
v___x_589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = l_Lean_MessageData_note(v___x_589_);
v___x_591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_591_, 0, v_msg_547_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
lean_ctor_set(v___x_576_, 0, v___x_591_);
v___x_593_ = v___x_576_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_606_; 
v___x_595_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v_c_565_);
v___x_597_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11);
v___x_598_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_596_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
v___x_599_ = l_Lean_MessageData_ofName(v_mod_580_);
v___x_600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_598_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
v___x_601_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13);
v___x_602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_600_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
v___x_603_ = l_Lean_MessageData_note(v___x_602_);
v___x_604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_604_, 0, v_msg_547_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
if (v_isShared_577_ == 0)
{
lean_ctor_set_tag(v___x_576_, 0);
lean_ctor_set(v___x_576_, 0, v___x_604_);
v___x_606_ = v___x_576_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_609_; 
lean_dec_ref(v_env_553_);
lean_dec(v_declHint_548_);
v___x_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_609_, 0, v_msg_547_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___boxed(lean_object* v_msg_610_, lean_object* v_declHint_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_610_, v_declHint_611_, v___y_612_);
lean_dec(v___y_612_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(lean_object* v_msg_615_, lean_object* v_declHint_616_, lean_object* v___y_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; lean_object* v_a_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_630_; 
v___x_620_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_615_, v_declHint_616_, v___y_618_);
v_a_621_ = lean_ctor_get(v___x_620_, 0);
v_isSharedCheck_630_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_630_ == 0)
{
v___x_623_ = v___x_620_;
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_a_621_);
lean_dec(v___x_620_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_630_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_628_; 
v___x_625_ = l_Lean_unknownIdentifierMessageTag;
v___x_626_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_a_621_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_626_);
v___x_628_ = v___x_623_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15___boxed(lean_object* v_msg_631_, lean_object* v_declHint_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(v_msg_631_, v_declHint_632_, v___y_633_, v___y_634_);
lean_dec(v___y_634_);
lean_dec_ref(v___y_633_);
return v_res_636_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(lean_object* v_opts_637_, lean_object* v_opt_638_){
_start:
{
lean_object* v_name_639_; lean_object* v_defValue_640_; lean_object* v_map_641_; lean_object* v___x_642_; 
v_name_639_ = lean_ctor_get(v_opt_638_, 0);
v_defValue_640_ = lean_ctor_get(v_opt_638_, 1);
v_map_641_ = lean_ctor_get(v_opts_637_, 0);
v___x_642_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_641_, v_name_639_);
if (lean_obj_tag(v___x_642_) == 0)
{
uint8_t v___x_643_; 
v___x_643_ = lean_unbox(v_defValue_640_);
return v___x_643_;
}
else
{
lean_object* v_val_644_; 
v_val_644_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v___x_642_, 1);
if (lean_obj_tag(v_val_644_) == 1)
{
uint8_t v_v_645_; 
v_v_645_ = lean_ctor_get_uint8(v_val_644_, 0);
lean_dec_ref_known(v_val_644_, 0);
return v_v_645_;
}
else
{
uint8_t v___x_646_; 
lean_dec(v_val_644_);
v___x_646_ = lean_unbox(v_defValue_640_);
return v___x_646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21___boxed(lean_object* v_opts_647_, lean_object* v_opt_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(v_opts_647_, v_opt_648_);
lean_dec_ref(v_opt_648_);
lean_dec_ref(v_opts_647_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_651_ = lean_box(1);
v___x_652_ = l_Lean_MessageData_ofFormat(v___x_651_);
return v___x_652_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__2));
v___x_657_ = l_Lean_MessageData_ofFormat(v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object* v_x_658_, lean_object* v_x_659_){
_start:
{
if (lean_obj_tag(v_x_659_) == 0)
{
return v_x_658_;
}
else
{
lean_object* v_head_660_; lean_object* v_tail_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_683_; 
v_head_660_ = lean_ctor_get(v_x_659_, 0);
v_tail_661_ = lean_ctor_get(v_x_659_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_659_);
if (v_isSharedCheck_683_ == 0)
{
v___x_663_ = v_x_659_;
v_isShared_664_ = v_isSharedCheck_683_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_tail_661_);
lean_inc(v_head_660_);
lean_dec(v_x_659_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_683_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v_before_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_681_; 
v_before_665_ = lean_ctor_get(v_head_660_, 0);
v_isSharedCheck_681_ = !lean_is_exclusive(v_head_660_);
if (v_isSharedCheck_681_ == 0)
{
lean_object* v_unused_682_; 
v_unused_682_ = lean_ctor_get(v_head_660_, 1);
lean_dec(v_unused_682_);
v___x_667_ = v_head_660_;
v_isShared_668_ = v_isSharedCheck_681_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_before_665_);
lean_dec(v_head_660_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_681_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_669_; lean_object* v___x_671_; 
v___x_669_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0);
if (v_isShared_668_ == 0)
{
lean_ctor_set_tag(v___x_667_, 7);
lean_ctor_set(v___x_667_, 1, v___x_669_);
lean_ctor_set(v___x_667_, 0, v_x_658_);
v___x_671_ = v___x_667_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_x_658_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_669_);
v___x_671_ = v_reuseFailAlloc_680_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_674_; 
v___x_672_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3);
if (v_isShared_664_ == 0)
{
lean_ctor_set_tag(v___x_663_, 7);
lean_ctor_set(v___x_663_, 1, v___x_672_);
lean_ctor_set(v___x_663_, 0, v___x_671_);
v___x_674_ = v___x_663_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_679_, 1, v___x_672_);
v___x_674_ = v_reuseFailAlloc_679_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = l_Lean_MessageData_ofSyntax(v_before_665_);
v___x_676_ = l_Lean_indentD(v___x_675_);
v___x_677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_674_);
lean_ctor_set(v___x_677_, 1, v___x_676_);
v_x_658_ = v___x_677_;
v_x_659_ = v_tail_661_;
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
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__1));
v___x_688_ = l_Lean_MessageData_ofFormat(v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(lean_object* v_msgData_689_, lean_object* v_macroStack_690_, lean_object* v___y_691_){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v_scopes_695_; lean_object* v___x_696_; lean_object* v_opts_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_693_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_694_ = lean_st_ref_get(v___y_691_);
v_scopes_695_ = lean_ctor_get(v___x_694_, 2);
lean_inc(v_scopes_695_);
lean_dec(v___x_694_);
v___x_696_ = l_List_head_x21___redArg(v___x_693_, v_scopes_695_);
lean_dec(v_scopes_695_);
v_opts_697_ = lean_ctor_get(v___x_696_, 1);
lean_inc_ref(v_opts_697_);
lean_dec(v___x_696_);
v___x_698_ = l_Lean_Elab_pp_macroStack;
v___x_699_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(v_opts_697_, v___x_698_);
lean_dec_ref(v_opts_697_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v_macroStack_690_);
v___x_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_700_, 0, v_msgData_689_);
return v___x_700_;
}
else
{
if (lean_obj_tag(v_macroStack_690_) == 0)
{
lean_object* v___x_701_; 
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v_msgData_689_);
return v___x_701_;
}
else
{
lean_object* v_head_702_; lean_object* v_after_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_718_; 
v_head_702_ = lean_ctor_get(v_macroStack_690_, 0);
lean_inc(v_head_702_);
v_after_703_ = lean_ctor_get(v_head_702_, 1);
v_isSharedCheck_718_ = !lean_is_exclusive(v_head_702_);
if (v_isSharedCheck_718_ == 0)
{
lean_object* v_unused_719_; 
v_unused_719_ = lean_ctor_get(v_head_702_, 0);
lean_dec(v_unused_719_);
v___x_705_ = v_head_702_;
v_isShared_706_ = v_isSharedCheck_718_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_after_703_);
lean_dec(v_head_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_718_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0);
if (v_isShared_706_ == 0)
{
lean_ctor_set_tag(v___x_705_, 7);
lean_ctor_set(v___x_705_, 1, v___x_707_);
lean_ctor_set(v___x_705_, 0, v_msgData_689_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_msgData_689_);
lean_ctor_set(v_reuseFailAlloc_717_, 1, v___x_707_);
v___x_709_ = v_reuseFailAlloc_717_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v_msgData_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
v___x_710_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = l_Lean_MessageData_ofSyntax(v_after_703_);
v___x_713_ = l_Lean_indentD(v___x_712_);
v_msgData_714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_714_, 0, v___x_711_);
lean_ctor_set(v_msgData_714_, 1, v___x_713_);
v___x_715_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22(v_msgData_714_, v_macroStack_690_);
v___x_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_716_, 0, v___x_715_);
return v___x_716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_msgData_720_, lean_object* v_macroStack_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_msgData_720_, v_macroStack_721_, v___y_722_);
lean_dec(v___y_722_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(lean_object* v_msgData_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___x_728_; lean_object* v_env_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v_scopes_732_; lean_object* v___x_733_; lean_object* v_opts_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_728_ = lean_st_ref_get(v___y_726_);
v_env_729_ = lean_ctor_get(v___x_728_, 0);
lean_inc_ref(v_env_729_);
lean_dec(v___x_728_);
v___x_730_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_731_ = lean_st_ref_get(v___y_726_);
v_scopes_732_ = lean_ctor_get(v___x_731_, 2);
lean_inc(v_scopes_732_);
lean_dec(v___x_731_);
v___x_733_ = l_List_head_x21___redArg(v___x_730_, v_scopes_732_);
lean_dec(v_scopes_732_);
v_opts_734_ = lean_ctor_get(v___x_733_, 1);
lean_inc_ref(v_opts_734_);
lean_dec(v___x_733_);
v___x_735_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_736_ = lean_unsigned_to_nat(32u);
v___x_737_ = lean_mk_empty_array_with_capacity(v___x_736_);
lean_dec_ref(v___x_737_);
v___x_738_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
v___x_739_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_739_, 0, v_env_729_);
lean_ctor_set(v___x_739_, 1, v___x_735_);
lean_ctor_set(v___x_739_, 2, v___x_738_);
lean_ctor_set(v___x_739_, 3, v_opts_734_);
v___x_740_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v_msgData_725_);
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg___boxed(lean_object* v_msgData_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msgData_742_, v___y_743_);
lean_dec(v___y_743_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(lean_object* v_msg_746_, lean_object* v___y_747_, lean_object* v___y_748_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = l_Lean_Elab_Command_getRef___redArg(v___y_747_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v_macroStack_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v_a_755_; lean_object* v___x_756_; lean_object* v_a_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_765_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
v_macroStack_752_ = lean_ctor_get(v___y_747_, 4);
v___x_753_ = l_Lean_Elab_getBetterRef(v_a_751_, v_macroStack_752_);
lean_dec(v_a_751_);
v___x_754_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msg_746_, v___y_748_);
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
lean_dec_ref(v___x_754_);
lean_inc(v_macroStack_752_);
v___x_756_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_a_755_, v_macroStack_752_, v___y_748_);
v_a_757_ = lean_ctor_get(v___x_756_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_756_);
if (v_isSharedCheck_765_ == 0)
{
v___x_759_ = v___x_756_;
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_a_757_);
lean_dec(v___x_756_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_765_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_763_; 
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_753_);
lean_ctor_set(v___x_761_, 1, v_a_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set_tag(v___x_759_, 1);
lean_ctor_set(v___x_759_, 0, v___x_761_);
v___x_763_ = v___x_759_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v_msg_746_);
v_a_766_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_750_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_750_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_msg_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(lean_object* v_ref_779_, lean_object* v_msg_780_, lean_object* v___y_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_Elab_Command_getRef___redArg(v___y_781_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v_fileName_786_; lean_object* v_fileMap_787_; lean_object* v_currRecDepth_788_; lean_object* v_cmdPos_789_; lean_object* v_macroStack_790_; lean_object* v_quotContext_x3f_791_; lean_object* v_currMacroScope_792_; lean_object* v_snap_x3f_793_; lean_object* v_cancelTk_x3f_794_; uint8_t v_suppressElabErrors_795_; lean_object* v_ref_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v_fileName_786_ = lean_ctor_get(v___y_781_, 0);
v_fileMap_787_ = lean_ctor_get(v___y_781_, 1);
v_currRecDepth_788_ = lean_ctor_get(v___y_781_, 2);
v_cmdPos_789_ = lean_ctor_get(v___y_781_, 3);
v_macroStack_790_ = lean_ctor_get(v___y_781_, 4);
v_quotContext_x3f_791_ = lean_ctor_get(v___y_781_, 5);
v_currMacroScope_792_ = lean_ctor_get(v___y_781_, 6);
v_snap_x3f_793_ = lean_ctor_get(v___y_781_, 8);
v_cancelTk_x3f_794_ = lean_ctor_get(v___y_781_, 9);
v_suppressElabErrors_795_ = lean_ctor_get_uint8(v___y_781_, sizeof(void*)*10);
v_ref_796_ = l_Lean_replaceRef(v_ref_779_, v_a_785_);
lean_dec(v_a_785_);
lean_inc(v_cancelTk_x3f_794_);
lean_inc(v_snap_x3f_793_);
lean_inc(v_currMacroScope_792_);
lean_inc(v_quotContext_x3f_791_);
lean_inc(v_macroStack_790_);
lean_inc(v_cmdPos_789_);
lean_inc(v_currRecDepth_788_);
lean_inc_ref(v_fileMap_787_);
lean_inc_ref(v_fileName_786_);
v___x_797_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_797_, 0, v_fileName_786_);
lean_ctor_set(v___x_797_, 1, v_fileMap_787_);
lean_ctor_set(v___x_797_, 2, v_currRecDepth_788_);
lean_ctor_set(v___x_797_, 3, v_cmdPos_789_);
lean_ctor_set(v___x_797_, 4, v_macroStack_790_);
lean_ctor_set(v___x_797_, 5, v_quotContext_x3f_791_);
lean_ctor_set(v___x_797_, 6, v_currMacroScope_792_);
lean_ctor_set(v___x_797_, 7, v_ref_796_);
lean_ctor_set(v___x_797_, 8, v_snap_x3f_793_);
lean_ctor_set(v___x_797_, 9, v_cancelTk_x3f_794_);
lean_ctor_set_uint8(v___x_797_, sizeof(void*)*10, v_suppressElabErrors_795_);
v___x_798_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_780_, v___x_797_, v___y_782_);
lean_dec_ref_known(v___x_797_, 10);
return v___x_798_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec_ref(v_msg_780_);
v_a_799_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_784_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_784_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg___boxed(lean_object* v_ref_807_, lean_object* v_msg_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_807_, v_msg_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v_ref_807_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(lean_object* v_ref_813_, lean_object* v_msg_814_, lean_object* v_declHint_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v___x_819_; lean_object* v_a_820_; lean_object* v___x_821_; 
v___x_819_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(v_msg_814_, v_declHint_815_, v___y_816_, v___y_817_);
v_a_820_ = lean_ctor_get(v___x_819_, 0);
lean_inc(v_a_820_);
lean_dec_ref(v___x_819_);
v___x_821_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_813_, v_a_820_, v___y_816_, v___y_817_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg___boxed(lean_object* v_ref_822_, lean_object* v_msg_823_, lean_object* v_declHint_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_822_, v_msg_823_, v_declHint_824_, v___y_825_, v___y_826_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v_ref_822_);
return v_res_828_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__0));
v___x_831_ = l_Lean_stringToMessageData(v___x_830_);
return v___x_831_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__2));
v___x_834_ = l_Lean_stringToMessageData(v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(lean_object* v_ref_835_, lean_object* v_constName_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; uint8_t v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_840_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1);
v___x_841_ = 0;
lean_inc(v_constName_836_);
v___x_842_ = l_Lean_MessageData_ofConstName(v_constName_836_, v___x_841_);
v___x_843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_840_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3);
v___x_845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_843_);
lean_ctor_set(v___x_845_, 1, v___x_844_);
v___x_846_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_835_, v___x_845_, v_constName_836_, v___y_837_, v___y_838_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_ref_847_, lean_object* v_constName_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_ref_847_, v_constName_848_, v___y_849_, v___y_850_);
lean_dec(v___y_850_);
lean_dec_ref(v___y_849_);
lean_dec(v_ref_847_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(lean_object* v_constName_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Lean_Elab_Command_getRef___redArg(v___y_854_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_a_858_, v_constName_853_, v___y_854_, v___y_855_);
lean_dec(v_a_858_);
return v___x_859_;
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec(v_constName_853_);
v_a_860_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_857_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_857_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_constName_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(lean_object* v_constName_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; lean_object* v_env_878_; uint8_t v___x_879_; lean_object* v___x_880_; 
v___x_877_ = lean_st_ref_get(v___y_875_);
v_env_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc_ref(v_env_878_);
lean_dec(v___x_877_);
v___x_879_ = 0;
lean_inc(v_constName_873_);
v___x_880_ = l_Lean_Environment_findConstVal_x3f(v_env_878_, v_constName_873_, v___x_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v___x_881_; 
v___x_881_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_873_, v___y_874_, v___y_875_);
return v___x_881_;
}
else
{
lean_object* v_val_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec(v_constName_873_);
v_val_882_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_880_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_val_882_);
lean_dec(v___x_880_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
lean_ctor_set_tag(v___x_884_, 0);
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_val_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6___boxed(lean_object* v_constName_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(v_constName_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(lean_object* v_constName_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
lean_inc(v_constName_895_);
v___x_899_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(v_constName_895_, v___y_896_, v___y_897_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_911_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_911_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_911_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_911_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_levelParams_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v_levelParams_904_ = lean_ctor_get(v_a_900_, 1);
lean_inc(v_levelParams_904_);
lean_dec(v_a_900_);
v___x_905_ = lean_box(0);
v___x_906_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__7(v_levelParams_904_, v___x_905_);
v___x_907_ = l_Lean_mkConst(v_constName_895_, v___x_906_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_907_);
v___x_909_ = v___x_902_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_constName_895_);
v_a_912_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_899_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_899_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5___boxed(lean_object* v_constName_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(v_constName_920_, v___y_921_, v___y_922_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(lean_object* v_t_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v_infoState_929_; uint8_t v_enabled_930_; 
v___x_928_ = lean_st_ref_get(v___y_926_);
v_infoState_929_ = lean_ctor_get(v___x_928_, 8);
lean_inc_ref(v_infoState_929_);
lean_dec(v___x_928_);
v_enabled_930_ = lean_ctor_get_uint8(v_infoState_929_, sizeof(void*)*3);
lean_dec_ref(v_infoState_929_);
if (v_enabled_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec_ref(v_t_925_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; lean_object* v_infoState_934_; lean_object* v_env_935_; lean_object* v_messages_936_; lean_object* v_scopes_937_; lean_object* v_usedQuotCtxts_938_; lean_object* v_nextMacroScope_939_; lean_object* v_maxRecDepth_940_; lean_object* v_ngen_941_; lean_object* v_auxDeclNGen_942_; lean_object* v_traceState_943_; lean_object* v_snapshotTasks_944_; lean_object* v_prevLinterStates_945_; lean_object* v_codeQualityEntryTasks_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_968_; 
v___x_933_ = lean_st_ref_take(v___y_926_);
v_infoState_934_ = lean_ctor_get(v___x_933_, 8);
v_env_935_ = lean_ctor_get(v___x_933_, 0);
v_messages_936_ = lean_ctor_get(v___x_933_, 1);
v_scopes_937_ = lean_ctor_get(v___x_933_, 2);
v_usedQuotCtxts_938_ = lean_ctor_get(v___x_933_, 3);
v_nextMacroScope_939_ = lean_ctor_get(v___x_933_, 4);
v_maxRecDepth_940_ = lean_ctor_get(v___x_933_, 5);
v_ngen_941_ = lean_ctor_get(v___x_933_, 6);
v_auxDeclNGen_942_ = lean_ctor_get(v___x_933_, 7);
v_traceState_943_ = lean_ctor_get(v___x_933_, 9);
v_snapshotTasks_944_ = lean_ctor_get(v___x_933_, 10);
v_prevLinterStates_945_ = lean_ctor_get(v___x_933_, 11);
v_codeQualityEntryTasks_946_ = lean_ctor_get(v___x_933_, 12);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_968_ == 0)
{
v___x_948_ = v___x_933_;
v_isShared_949_ = v_isSharedCheck_968_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_codeQualityEntryTasks_946_);
lean_inc(v_prevLinterStates_945_);
lean_inc(v_snapshotTasks_944_);
lean_inc(v_traceState_943_);
lean_inc(v_infoState_934_);
lean_inc(v_auxDeclNGen_942_);
lean_inc(v_ngen_941_);
lean_inc(v_maxRecDepth_940_);
lean_inc(v_nextMacroScope_939_);
lean_inc(v_usedQuotCtxts_938_);
lean_inc(v_scopes_937_);
lean_inc(v_messages_936_);
lean_inc(v_env_935_);
lean_dec(v___x_933_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_968_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
uint8_t v_enabled_950_; lean_object* v_assignment_951_; lean_object* v_lazyAssignment_952_; lean_object* v_trees_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_967_; 
v_enabled_950_ = lean_ctor_get_uint8(v_infoState_934_, sizeof(void*)*3);
v_assignment_951_ = lean_ctor_get(v_infoState_934_, 0);
v_lazyAssignment_952_ = lean_ctor_get(v_infoState_934_, 1);
v_trees_953_ = lean_ctor_get(v_infoState_934_, 2);
v_isSharedCheck_967_ = !lean_is_exclusive(v_infoState_934_);
if (v_isSharedCheck_967_ == 0)
{
v___x_955_ = v_infoState_934_;
v_isShared_956_ = v_isSharedCheck_967_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_trees_953_);
lean_inc(v_lazyAssignment_952_);
lean_inc(v_assignment_951_);
lean_dec(v_infoState_934_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_967_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_960_; 
v___x_957_ = lean_box(0);
v___x_958_ = l_Lean_PersistentArray_push___redArg(v_trees_953_, v_t_925_);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 2, v___x_958_);
v___x_960_ = v___x_955_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_assignment_951_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_lazyAssignment_952_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v___x_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_966_, sizeof(void*)*3, v_enabled_950_);
v___x_960_ = v_reuseFailAlloc_966_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
lean_object* v___x_962_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 8, v___x_960_);
v___x_962_ = v___x_948_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_env_935_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_messages_936_);
lean_ctor_set(v_reuseFailAlloc_965_, 2, v_scopes_937_);
lean_ctor_set(v_reuseFailAlloc_965_, 3, v_usedQuotCtxts_938_);
lean_ctor_set(v_reuseFailAlloc_965_, 4, v_nextMacroScope_939_);
lean_ctor_set(v_reuseFailAlloc_965_, 5, v_maxRecDepth_940_);
lean_ctor_set(v_reuseFailAlloc_965_, 6, v_ngen_941_);
lean_ctor_set(v_reuseFailAlloc_965_, 7, v_auxDeclNGen_942_);
lean_ctor_set(v_reuseFailAlloc_965_, 8, v___x_960_);
lean_ctor_set(v_reuseFailAlloc_965_, 9, v_traceState_943_);
lean_ctor_set(v_reuseFailAlloc_965_, 10, v_snapshotTasks_944_);
lean_ctor_set(v_reuseFailAlloc_965_, 11, v_prevLinterStates_945_);
lean_ctor_set(v_reuseFailAlloc_965_, 12, v_codeQualityEntryTasks_946_);
v___x_962_ = v_reuseFailAlloc_965_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_963_ = lean_st_ref_put(v___y_926_, v___x_962_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_957_);
return v___x_964_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_t_969_, lean_object* v___y_970_, lean_object* v___y_971_){
_start:
{
lean_object* v_res_972_; 
v_res_972_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v_t_969_, v___y_970_);
lean_dec(v___y_970_);
return v_res_972_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_973_ = lean_unsigned_to_nat(32u);
v___x_974_ = lean_mk_empty_array_with_capacity(v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1(void){
_start:
{
size_t v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_976_ = ((size_t)5ULL);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_unsigned_to_nat(32u);
v___x_979_ = lean_mk_empty_array_with_capacity(v___x_978_);
v___x_980_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0);
v___x_981_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_981_, 0, v___x_980_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
lean_ctor_set(v___x_981_, 2, v___x_977_);
lean_ctor_set(v___x_981_, 3, v___x_977_);
lean_ctor_set_usize(v___x_981_, 4, v___x_976_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(lean_object* v_t_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; lean_object* v_infoState_987_; uint8_t v_enabled_988_; 
v___x_986_ = lean_st_ref_get(v___y_984_);
v_infoState_987_ = lean_ctor_get(v___x_986_, 8);
lean_inc_ref(v_infoState_987_);
lean_dec(v___x_986_);
v_enabled_988_ = lean_ctor_get_uint8(v_infoState_987_, sizeof(void*)*3);
lean_dec_ref(v_infoState_987_);
if (v_enabled_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec_ref(v_t_982_);
v___x_989_ = lean_box(0);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1);
v___x_992_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_992_, 0, v_t_982_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
v___x_993_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v___x_992_, v___y_984_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___boxed(lean_object* v_t_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(v_t_994_, v___y_995_, v___y_996_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(lean_object* v_stx_999_, lean_object* v_n_1000_, lean_object* v_expectedType_x3f_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(v_n_1000_, v___y_1002_, v___y_1003_);
if (lean_obj_tag(v___x_1005_) == 0)
{
lean_object* v_a_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; uint8_t v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v_a_1006_ = lean_ctor_get(v___x_1005_, 0);
lean_inc(v_a_1006_);
lean_dec_ref_known(v___x_1005_, 1);
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
lean_ctor_set(v___x_1008_, 1, v_stx_999_);
v___x_1009_ = l_Lean_LocalContext_empty;
v___x_1010_ = 0;
v___x_1011_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1011_, 0, v___x_1008_);
lean_ctor_set(v___x_1011_, 1, v___x_1009_);
lean_ctor_set(v___x_1011_, 2, v_expectedType_x3f_1001_);
lean_ctor_set(v___x_1011_, 3, v_a_1006_);
lean_ctor_set_uint8(v___x_1011_, sizeof(void*)*4, v___x_1010_);
lean_ctor_set_uint8(v___x_1011_, sizeof(void*)*4 + 1, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
v___x_1013_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(v___x_1012_, v___y_1002_, v___y_1003_);
return v___x_1013_;
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_dec(v_expectedType_x3f_1001_);
lean_dec(v_stx_999_);
v_a_1014_ = lean_ctor_get(v___x_1005_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1005_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1005_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1005_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3___boxed(lean_object* v_stx_1022_, lean_object* v_n_1023_, lean_object* v_expectedType_x3f_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(v_stx_1022_, v_n_1023_, v_expectedType_x3f_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
return v_res_1028_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__0));
v___x_1031_ = l_Lean_stringToMessageData(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__2));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1(lean_object* v_declName_1035_, lean_object* v_docString_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v___y_1041_; lean_object* v___x_1067_; lean_object* v_env_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_st_ref_get(v___y_1038_);
v_env_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc_ref(v_env_1068_);
lean_dec(v___x_1067_);
v___x_1069_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1068_, v_declName_1035_);
lean_dec_ref(v_env_1068_);
if (lean_obj_tag(v___x_1069_) == 0)
{
v___y_1041_ = v___y_1038_;
goto v___jp_1040_;
}
else
{
uint8_t v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref_known(v___x_1069_, 1);
lean_dec_ref(v_docString_1036_);
v___x_1070_ = 0;
v___x_1071_ = lean_obj_once(&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1, &l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1_once, _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1);
v___x_1072_ = l_Lean_MessageData_ofConstName(v_declName_1035_, v___x_1070_);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = lean_obj_once(&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3, &l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3_once, _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1073_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v___x_1075_, v___y_1037_, v___y_1038_);
return v___x_1076_;
}
v___jp_1040_:
{
lean_object* v___x_1042_; lean_object* v_env_1043_; lean_object* v_nextMacroScope_1044_; lean_object* v_ngen_1045_; lean_object* v_auxDeclNGen_1046_; lean_object* v_traceState_1047_; lean_object* v_recordedDeps_1048_; lean_object* v_messages_1049_; lean_object* v_infoState_1050_; lean_object* v_snapshotTasks_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1065_; 
v___x_1042_ = lean_st_ref_take(v___y_1041_);
v_env_1043_ = lean_ctor_get(v___x_1042_, 0);
v_nextMacroScope_1044_ = lean_ctor_get(v___x_1042_, 1);
v_ngen_1045_ = lean_ctor_get(v___x_1042_, 2);
v_auxDeclNGen_1046_ = lean_ctor_get(v___x_1042_, 3);
v_traceState_1047_ = lean_ctor_get(v___x_1042_, 4);
v_recordedDeps_1048_ = lean_ctor_get(v___x_1042_, 6);
v_messages_1049_ = lean_ctor_get(v___x_1042_, 7);
v_infoState_1050_ = lean_ctor_get(v___x_1042_, 8);
v_snapshotTasks_1051_ = lean_ctor_get(v___x_1042_, 9);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1065_ == 0)
{
lean_object* v_unused_1066_; 
v_unused_1066_ = lean_ctor_get(v___x_1042_, 5);
lean_dec(v_unused_1066_);
v___x_1053_ = v___x_1042_;
v_isShared_1054_ = v_isSharedCheck_1065_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_snapshotTasks_1051_);
lean_inc(v_infoState_1050_);
lean_inc(v_messages_1049_);
lean_inc(v_recordedDeps_1048_);
lean_inc(v_traceState_1047_);
lean_inc(v_auxDeclNGen_1046_);
lean_inc(v_ngen_1045_);
lean_inc(v_nextMacroScope_1044_);
lean_inc(v_env_1043_);
lean_dec(v___x_1042_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1065_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1055_ = lean_box(0);
v___x_1056_ = l_Lean_docStringExt;
v___x_1057_ = l_String_removeLeadingSpaces(v_docString_1036_);
v___x_1058_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1056_, v_env_1043_, v_declName_1035_, v___x_1057_);
v___x_1059_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__1, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__1_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__1);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 5, v___x_1059_);
lean_ctor_set(v___x_1053_, 0, v___x_1058_);
v___x_1061_ = v___x_1053_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1064_, 1, v_nextMacroScope_1044_);
lean_ctor_set(v_reuseFailAlloc_1064_, 2, v_ngen_1045_);
lean_ctor_set(v_reuseFailAlloc_1064_, 3, v_auxDeclNGen_1046_);
lean_ctor_set(v_reuseFailAlloc_1064_, 4, v_traceState_1047_);
lean_ctor_set(v_reuseFailAlloc_1064_, 5, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1064_, 6, v_recordedDeps_1048_);
lean_ctor_set(v_reuseFailAlloc_1064_, 7, v_messages_1049_);
lean_ctor_set(v_reuseFailAlloc_1064_, 8, v_infoState_1050_);
lean_ctor_set(v_reuseFailAlloc_1064_, 9, v_snapshotTasks_1051_);
v___x_1061_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = lean_st_ref_put(v___y_1041_, v___x_1061_);
v___x_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1063_, 0, v___x_1055_);
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
lean_object* v___x_1112_; lean_object* v_env_1113_; lean_object* v_messages_1114_; lean_object* v_scopes_1115_; lean_object* v_usedQuotCtxts_1116_; lean_object* v_nextMacroScope_1117_; lean_object* v_maxRecDepth_1118_; lean_object* v_ngen_1119_; lean_object* v_auxDeclNGen_1120_; lean_object* v_infoState_1121_; lean_object* v_traceState_1122_; lean_object* v_snapshotTasks_1123_; lean_object* v_prevLinterStates_1124_; lean_object* v_codeQualityEntryTasks_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1137_; 
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
v_prevLinterStates_1124_ = lean_ctor_get(v___x_1112_, 11);
v_codeQualityEntryTasks_1125_ = lean_ctor_get(v___x_1112_, 12);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1127_ = v___x_1112_;
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1125_);
lean_inc(v_prevLinterStates_1124_);
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
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1137_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v___x_1129_ = lean_box(0);
v___x_1130_ = l_Lean_declRangeExt;
v___x_1131_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1130_, v_env_1113_, v_declName_1107_, v_declRanges_1108_);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1131_);
v___x_1133_ = v___x_1127_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_messages_1114_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_scopes_1115_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_usedQuotCtxts_1116_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_nextMacroScope_1117_);
lean_ctor_set(v_reuseFailAlloc_1136_, 5, v_maxRecDepth_1118_);
lean_ctor_set(v_reuseFailAlloc_1136_, 6, v_ngen_1119_);
lean_ctor_set(v_reuseFailAlloc_1136_, 7, v_auxDeclNGen_1120_);
lean_ctor_set(v_reuseFailAlloc_1136_, 8, v_infoState_1121_);
lean_ctor_set(v_reuseFailAlloc_1136_, 9, v_traceState_1122_);
lean_ctor_set(v_reuseFailAlloc_1136_, 10, v_snapshotTasks_1123_);
lean_ctor_set(v_reuseFailAlloc_1136_, 11, v_prevLinterStates_1124_);
lean_ctor_set(v_reuseFailAlloc_1136_, 12, v_codeQualityEntryTasks_1125_);
v___x_1133_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1134_ = lean_st_ref_put(v___y_1109_, v___x_1133_);
v___x_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1129_);
return v___x_1135_;
}
}
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec_ref(v_declRanges_1108_);
lean_dec(v_declName_1107_);
v___x_1138_ = lean_box(0);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg___boxed(lean_object* v_declName_1140_, lean_object* v_declRanges_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1140_, v_declRanges_1141_, v___y_1142_);
lean_dec(v___y_1142_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(lean_object* v_declName_1145_, lean_object* v_rangeStx_1146_, lean_object* v_selectionRangeStx_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1168_; 
v___x_1151_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_rangeStx_1146_, v___y_1148_);
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1168_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1168_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
if (lean_obj_tag(v_a_1152_) == 1)
{
lean_object* v_val_1156_; lean_object* v_a_1158_; lean_object* v___x_1161_; lean_object* v_a_1162_; 
lean_del_object(v___x_1154_);
v_val_1156_ = lean_ctor_get(v_a_1152_, 0);
lean_inc(v_val_1156_);
lean_dec_ref_known(v_a_1152_, 1);
v___x_1161_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_selectionRangeStx_1147_, v___y_1148_);
v_a_1162_ = lean_ctor_get(v___x_1161_, 0);
lean_inc(v_a_1162_);
lean_dec_ref(v___x_1161_);
if (lean_obj_tag(v_a_1162_) == 0)
{
lean_inc(v_val_1156_);
v_a_1158_ = v_val_1156_;
goto v___jp_1157_;
}
else
{
lean_object* v_val_1163_; 
v_val_1163_ = lean_ctor_get(v_a_1162_, 0);
lean_inc(v_val_1163_);
lean_dec_ref_known(v_a_1162_, 1);
v_a_1158_ = v_val_1163_;
goto v___jp_1157_;
}
v___jp_1157_:
{
lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1159_, 0, v_val_1156_);
lean_ctor_set(v___x_1159_, 1, v_a_1158_);
v___x_1160_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1145_, v___x_1159_, v___y_1149_);
return v___x_1160_;
}
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_dec(v_a_1152_);
lean_dec(v_declName_1145_);
v___x_1164_ = lean_box(0);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1164_);
v___x_1166_ = v___x_1154_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2___boxed(lean_object* v_declName_1169_, lean_object* v_rangeStx_1170_, lean_object* v_selectionRangeStx_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(v_declName_1169_, v_rangeStx_1170_, v_selectionRangeStx_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v_selectionRangeStx_1171_);
lean_dec(v_rangeStx_1170_);
return v_res_1175_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3(void){
_start:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1182_ = lean_box(0);
v___x_1183_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2));
v___x_1184_ = l_Lean_mkConst(v___x_1183_, v___x_1182_);
return v___x_1184_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6(void){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = lean_box(0);
v___x_1191_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5));
v___x_1192_ = l_Lean_mkConst(v___x_1191_, v___x_1190_);
return v___x_1192_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7(void){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6);
v___x_1194_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3);
v___x_1195_ = l_Lean_Expr_app___override(v___x_1194_, v___x_1193_);
return v___x_1195_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_box(0);
v___x_1202_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9));
v___x_1203_ = l_Lean_mkConst(v___x_1202_, v___x_1201_);
return v___x_1203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs(lean_object* v_x_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = ((lean_object*)(l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3));
lean_inc(v_x_1209_);
v___x_1214_ = l_Lean_Syntax_isOfKind(v_x_1209_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_dec(v_x_1209_);
v___x_1215_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v_id_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_env_1223_; lean_object* v___x_1224_; 
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_unsigned_to_nat(1u);
v_id_1218_ = l_Lean_Syntax_getArg(v_x_1209_, v___x_1217_);
v___x_1219_ = lean_unsigned_to_nat(3u);
v___x_1220_ = l_Lean_Syntax_getArg(v_x_1209_, v___x_1219_);
lean_dec(v_x_1209_);
v___x_1221_ = lean_box(0);
v___x_1222_ = lean_st_ref_get(v_a_1211_);
v_env_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc_ref(v_env_1223_);
lean_dec(v___x_1222_);
v___x_1224_ = l_Lean_Elab_Command_getScope___redArg(v_a_1211_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v_currNamespace_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___y_1231_; lean_object* v___x_1234_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v_currNamespace_1226_ = lean_ctor_get(v_a_1225_, 2);
lean_inc(v_currNamespace_1226_);
lean_dec(v_a_1225_);
v___x_1227_ = l_Lean_TSyntax_getId(v_id_1218_);
lean_inc(v___x_1227_);
v___x_1228_ = l_Lean_Name_append(v_currNamespace_1226_, v___x_1227_);
v___x_1229_ = l_Lean_mkPrivateName(v_env_1223_, v___x_1228_);
lean_dec_ref(v_env_1223_);
v___x_1234_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_1220_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v___x_1236_; lean_object* v_env_1237_; lean_object* v_messages_1238_; lean_object* v_scopes_1239_; lean_object* v_usedQuotCtxts_1240_; lean_object* v_nextMacroScope_1241_; lean_object* v_maxRecDepth_1242_; lean_object* v_ngen_1243_; lean_object* v_auxDeclNGen_1244_; lean_object* v_infoState_1245_; lean_object* v_traceState_1246_; lean_object* v_snapshotTasks_1247_; lean_object* v_prevLinterStates_1248_; lean_object* v_codeQualityEntryTasks_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1322_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref_known(v___x_1234_, 1);
v___x_1236_ = lean_st_ref_take(v_a_1211_);
v_env_1237_ = lean_ctor_get(v___x_1236_, 0);
v_messages_1238_ = lean_ctor_get(v___x_1236_, 1);
v_scopes_1239_ = lean_ctor_get(v___x_1236_, 2);
v_usedQuotCtxts_1240_ = lean_ctor_get(v___x_1236_, 3);
v_nextMacroScope_1241_ = lean_ctor_get(v___x_1236_, 4);
v_maxRecDepth_1242_ = lean_ctor_get(v___x_1236_, 5);
v_ngen_1243_ = lean_ctor_get(v___x_1236_, 6);
v_auxDeclNGen_1244_ = lean_ctor_get(v___x_1236_, 7);
v_infoState_1245_ = lean_ctor_get(v___x_1236_, 8);
v_traceState_1246_ = lean_ctor_get(v___x_1236_, 9);
v_snapshotTasks_1247_ = lean_ctor_get(v___x_1236_, 10);
v_prevLinterStates_1248_ = lean_ctor_get(v___x_1236_, 11);
v_codeQualityEntryTasks_1249_ = lean_ctor_get(v___x_1236_, 12);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1251_ = v___x_1236_;
v_isShared_1252_ = v_isSharedCheck_1322_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1249_);
lean_inc(v_prevLinterStates_1248_);
lean_inc(v_snapshotTasks_1247_);
lean_inc(v_traceState_1246_);
lean_inc(v_infoState_1245_);
lean_inc(v_auxDeclNGen_1244_);
lean_inc(v_ngen_1243_);
lean_inc(v_maxRecDepth_1242_);
lean_inc(v_nextMacroScope_1241_);
lean_inc(v_usedQuotCtxts_1240_);
lean_inc(v_scopes_1239_);
lean_inc(v_messages_1238_);
lean_inc(v_env_1237_);
lean_dec(v___x_1236_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1322_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___y_1254_; lean_object* v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = lean_array_get_size(v_a_1235_);
v___x_1314_ = lean_nat_dec_lt(v___x_1216_, v___x_1313_);
if (v___x_1314_ == 0)
{
v___y_1254_ = v_messages_1238_;
goto v___jp_1253_;
}
else
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_nat_dec_le(v___x_1313_, v___x_1313_);
if (v___x_1315_ == 0)
{
if (v___x_1314_ == 0)
{
v___y_1254_ = v_messages_1238_;
goto v___jp_1253_;
}
else
{
size_t v___x_1316_; size_t v___x_1317_; lean_object* v___x_1318_; 
v___x_1316_ = ((size_t)0ULL);
v___x_1317_ = lean_usize_of_nat(v___x_1313_);
v___x_1318_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_a_1235_, v___x_1316_, v___x_1317_, v_messages_1238_);
v___y_1254_ = v___x_1318_;
goto v___jp_1253_;
}
}
else
{
size_t v___x_1319_; size_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = ((size_t)0ULL);
v___x_1320_ = lean_usize_of_nat(v___x_1313_);
v___x_1321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_a_1235_, v___x_1319_, v___x_1320_, v_messages_1238_);
v___y_1254_ = v___x_1321_;
goto v___jp_1253_;
}
}
v___jp_1253_:
{
lean_object* v___x_1256_; 
if (v_isShared_1252_ == 0)
{
lean_ctor_set(v___x_1251_, 1, v___y_1254_);
v___x_1256_ = v___x_1251_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_env_1237_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___y_1254_);
lean_ctor_set(v_reuseFailAlloc_1312_, 2, v_scopes_1239_);
lean_ctor_set(v_reuseFailAlloc_1312_, 3, v_usedQuotCtxts_1240_);
lean_ctor_set(v_reuseFailAlloc_1312_, 4, v_nextMacroScope_1241_);
lean_ctor_set(v_reuseFailAlloc_1312_, 5, v_maxRecDepth_1242_);
lean_ctor_set(v_reuseFailAlloc_1312_, 6, v_ngen_1243_);
lean_ctor_set(v_reuseFailAlloc_1312_, 7, v_auxDeclNGen_1244_);
lean_ctor_set(v_reuseFailAlloc_1312_, 8, v_infoState_1245_);
lean_ctor_set(v_reuseFailAlloc_1312_, 9, v_traceState_1246_);
lean_ctor_set(v_reuseFailAlloc_1312_, 10, v_snapshotTasks_1247_);
lean_ctor_set(v_reuseFailAlloc_1312_, 11, v_prevLinterStates_1248_);
lean_ctor_set(v_reuseFailAlloc_1312_, 12, v_codeQualityEntryTasks_1249_);
v___x_1256_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1257_ = lean_st_ref_put(v_a_1211_, v___x_1256_);
v___x_1258_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7);
lean_inc_n(v___x_1229_, 3);
v___x_1259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1229_);
lean_ctor_set(v___x_1259_, 1, v___x_1221_);
lean_ctor_set(v___x_1259_, 2, v___x_1258_);
v___x_1260_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10);
v___x_1261_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v___x_1229_);
v___x_1262_ = l_Lean_Expr_app___override(v___x_1260_, v___x_1261_);
v___x_1263_ = lean_box(1);
v___x_1264_ = 1;
v___x_1265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1229_);
lean_ctor_set(v___x_1265_, 1, v___x_1221_);
v___x_1266_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1266_, 0, v___x_1259_);
lean_ctor_set(v___x_1266_, 1, v___x_1262_);
lean_ctor_set(v___x_1266_, 2, v___x_1263_);
lean_ctor_set(v___x_1266_, 3, v___x_1265_);
lean_ctor_set_uint8(v___x_1266_, sizeof(void*)*4, v___x_1264_);
v___x_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
v___x_1268_ = lean_box(v___x_1214_);
v___x_1269_ = lean_box(v___x_1214_);
v___x_1270_ = lean_alloc_closure((void*)(l_Lean_addAndCompile___boxed), 6, 3);
lean_closure_set(v___x_1270_, 0, v___x_1267_);
lean_closure_set(v___x_1270_, 1, v___x_1268_);
lean_closure_set(v___x_1270_, 2, v___x_1269_);
v___x_1271_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1270_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_fileName_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec_ref_known(v___x_1271_, 1);
v_fileName_1272_ = lean_ctor_get(v_a_1210_, 0);
v___x_1273_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__11));
v___x_1274_ = lean_string_append(v___x_1273_, v_fileName_1272_);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__12));
v___x_1276_ = lean_string_append(v___x_1274_, v___x_1275_);
v___x_1277_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1227_, v___x_1214_);
v___x_1278_ = lean_string_append(v___x_1276_, v___x_1277_);
v___x_1279_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__13));
v___x_1280_ = lean_string_append(v___x_1278_, v___x_1279_);
v___x_1281_ = lean_string_append(v___x_1280_, v___x_1277_);
v___x_1282_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__14));
v___x_1283_ = lean_string_append(v___x_1281_, v___x_1282_);
v___x_1284_ = lean_string_append(v___x_1283_, v___x_1277_);
lean_dec_ref(v___x_1277_);
v___x_1285_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__15));
v___x_1286_ = lean_string_append(v___x_1284_, v___x_1285_);
lean_inc(v___x_1229_);
v___x_1287_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___boxed), 5, 2);
lean_closure_set(v___x_1287_, 0, v___x_1229_);
lean_closure_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1287_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v___x_1289_; 
lean_dec_ref_known(v___x_1288_, 1);
v___x_1289_ = l_Lean_Elab_Command_getRef___redArg(v_a_1210_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1291_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
lean_inc(v___x_1229_);
v___x_1291_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(v___x_1229_, v_a_1290_, v_id_1218_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1290_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
lean_dec_ref_known(v___x_1291_, 1);
v___x_1292_ = lean_box(0);
lean_inc(v___x_1229_);
v___x_1293_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(v_id_1218_, v___x_1229_, v___x_1292_, v_a_1210_, v_a_1211_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v___x_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
lean_dec_ref_known(v___x_1293_, 1);
v___x_1294_ = lean_array_get_size(v_a_1235_);
v___x_1295_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0));
v___x_1296_ = lean_nat_dec_lt(v___x_1216_, v___x_1294_);
if (v___x_1296_ == 0)
{
lean_dec(v_a_1235_);
v___y_1231_ = v___x_1295_;
goto v___jp_1230_;
}
else
{
uint8_t v___x_1297_; 
v___x_1297_ = lean_nat_dec_le(v___x_1294_, v___x_1294_);
if (v___x_1297_ == 0)
{
if (v___x_1296_ == 0)
{
lean_dec(v_a_1235_);
v___y_1231_ = v___x_1295_;
goto v___jp_1230_;
}
else
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = ((size_t)0ULL);
v___x_1299_ = lean_usize_of_nat(v___x_1294_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_a_1235_, v___x_1298_, v___x_1299_, v___x_1295_);
lean_dec(v_a_1235_);
v___y_1231_ = v___x_1300_;
goto v___jp_1230_;
}
}
else
{
size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = lean_usize_of_nat(v___x_1294_);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_a_1235_, v___x_1301_, v___x_1302_, v___x_1295_);
lean_dec(v_a_1235_);
v___y_1231_ = v___x_1303_;
goto v___jp_1230_;
}
}
}
else
{
lean_dec(v_a_1235_);
lean_dec(v___x_1229_);
return v___x_1293_;
}
}
else
{
lean_dec(v_a_1235_);
lean_dec(v___x_1229_);
lean_dec(v_id_1218_);
return v___x_1291_;
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_a_1235_);
lean_dec(v___x_1229_);
lean_dec(v_id_1218_);
v_a_1304_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1289_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1289_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_dec(v_a_1235_);
lean_dec(v___x_1229_);
lean_dec(v_id_1218_);
return v___x_1288_;
}
}
else
{
lean_dec(v_a_1235_);
lean_dec(v___x_1229_);
lean_dec(v___x_1227_);
lean_dec(v_id_1218_);
return v___x_1271_;
}
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v___x_1229_);
lean_dec(v___x_1227_);
lean_dec(v_id_1218_);
v_a_1323_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1234_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1234_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
v___jp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_storeTraces___boxed), 5, 2);
lean_closure_set(v___x_1232_, 0, v___x_1229_);
lean_closure_set(v___x_1232_, 1, v___y_1231_);
v___x_1233_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1232_, v_a_1210_, v_a_1211_);
return v___x_1233_;
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v_env_1223_);
lean_dec(v___x_1220_);
lean_dec(v_id_1218_);
v_a_1331_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1224_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1224_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___boxed(lean_object* v_x_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Lean_Elab_PostprocessTraces_elabStoreTraceAs(v_x_1339_, v_a_1340_, v_a_1341_);
lean_dec(v_a_1341_);
lean_dec_ref(v_a_1340_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2(lean_object* v_stx_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_stx_1344_, v___y_1345_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___boxed(lean_object* v_stx_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2(v_stx_1349_, v___y_1350_, v___y_1351_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
lean_dec(v_stx_1349_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3(lean_object* v_declName_1354_, lean_object* v_declRanges_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1354_, v_declRanges_1355_, v___y_1357_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___boxed(lean_object* v_declName_1360_, lean_object* v_declRanges_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3(v_declName_1360_, v_declRanges_1361_, v___y_1362_, v___y_1363_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9(lean_object* v_t_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v_t_1366_, v___y_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___boxed(lean_object* v_t_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9(v_t_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1375_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9(lean_object* v_00_u03b1_1376_, lean_object* v_constName_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1381_; 
v___x_1381_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_1377_, v___y_1378_, v___y_1379_);
return v___x_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1382_, lean_object* v_constName_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9(v_00_u03b1_1382_, v_constName_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1388_, lean_object* v_ref_1389_, lean_object* v_constName_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_ref_1389_, v_constName_1390_, v___y_1391_, v___y_1392_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1395_, lean_object* v_ref_1396_, lean_object* v_constName_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12(v_00_u03b1_1395_, v_ref_1396_, v_constName_1397_, v___y_1398_, v___y_1399_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v_ref_1396_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14(lean_object* v_00_u03b1_1402_, lean_object* v_ref_1403_, lean_object* v_msg_1404_, lean_object* v_declHint_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_1403_, v_msg_1404_, v_declHint_1405_, v___y_1406_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_ref_1411_, lean_object* v_msg_1412_, lean_object* v_declHint_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14(v_00_u03b1_1410_, v_ref_1411_, v_msg_1412_, v_declHint_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v_ref_1411_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16(lean_object* v_msg_1418_, lean_object* v_declHint_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_1418_, v_declHint_1419_, v___y_1421_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___boxed(lean_object* v_msg_1424_, lean_object* v_declHint_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16(v_msg_1424_, v_declHint_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16(lean_object* v_00_u03b1_1430_, lean_object* v_ref_1431_, lean_object* v_msg_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_1431_, v_msg_1432_, v___y_1433_, v___y_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_ref_1438_, lean_object* v_msg_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16(v_00_u03b1_1437_, v_ref_1438_, v_msg_1439_, v___y_1440_, v___y_1441_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
lean_dec(v_ref_1438_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19(lean_object* v_msgData_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msgData_1444_, v___y_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___boxed(lean_object* v_msgData_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19(v_msgData_1449_, v___y_1450_, v___y_1451_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1454_, lean_object* v_msg_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_1455_, v___y_1456_, v___y_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1460_, lean_object* v_msg_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18(v_00_u03b1_1460_, v_msg_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20(lean_object* v_msgData_1466_, lean_object* v_macroStack_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_msgData_1466_, v_macroStack_1467_, v___y_1469_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___boxed(lean_object* v_msgData_1472_, lean_object* v_macroStack_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v_res_1477_; 
v_res_1477_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20(v_msgData_1472_, v_macroStack_1473_, v___y_1474_, v___y_1475_);
lean_dec(v___y_1475_);
lean_dec_ref(v___y_1474_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace_spec__0(lean_object* v_a_1478_, lean_object* v_a_1479_){
_start:
{
if (lean_obj_tag(v_a_1478_) == 0)
{
lean_object* v___x_1480_; 
v___x_1480_ = l_List_reverse___redArg(v_a_1479_);
return v___x_1480_;
}
else
{
lean_object* v_head_1481_; lean_object* v_tail_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1503_; 
v_head_1481_ = lean_ctor_get(v_a_1478_, 0);
v_tail_1482_ = lean_ctor_get(v_a_1478_, 1);
v_isSharedCheck_1503_ = !lean_is_exclusive(v_a_1478_);
if (v_isSharedCheck_1503_ == 0)
{
v___x_1484_ = v_a_1478_;
v_isShared_1485_ = v_isSharedCheck_1503_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_tail_1482_);
lean_inc(v_head_1481_);
lean_dec(v_a_1478_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1503_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v_fst_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1501_; 
v_fst_1486_ = lean_ctor_get(v_head_1481_, 0);
v_isSharedCheck_1501_ = !lean_is_exclusive(v_head_1481_);
if (v_isSharedCheck_1501_ == 0)
{
lean_object* v_unused_1502_; 
v_unused_1502_ = lean_ctor_get(v_head_1481_, 1);
lean_dec(v_unused_1502_);
v___x_1488_ = v_head_1481_;
v_isShared_1489_ = v_isSharedCheck_1501_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_fst_1486_);
lean_dec(v_head_1481_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1501_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1490_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3);
v___x_1491_ = l_Lean_privateToUserName(v_fst_1486_);
v___x_1492_ = l_Lean_MessageData_ofName(v___x_1491_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set_tag(v___x_1488_, 7);
lean_ctor_set(v___x_1488_, 1, v___x_1492_);
lean_ctor_set(v___x_1488_, 0, v___x_1490_);
v___x_1494_ = v___x_1488_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1500_; 
v_reuseFailAlloc_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1490_);
lean_ctor_set(v_reuseFailAlloc_1500_, 1, v___x_1492_);
v___x_1494_ = v_reuseFailAlloc_1500_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1490_);
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 1, v_a_1479_);
lean_ctor_set(v___x_1484_, 0, v___x_1495_);
v___x_1497_ = v___x_1484_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_a_1479_);
v___x_1497_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
v_a_1478_ = v_tail_1482_;
v_a_1479_ = v___x_1497_;
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
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__0));
v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__2));
v___x_1509_ = l_Lean_stringToMessageData(v___x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__4));
v___x_1512_ = l_Lean_stringToMessageData(v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__6));
v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
return v___x_1515_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__8));
v___x_1518_ = l_Lean_stringToMessageData(v___x_1517_);
return v___x_1518_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__11));
v___x_1523_ = l_Lean_MessageData_ofFormat(v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__13));
v___x_1526_ = l_Lean_stringToMessageData(v___x_1525_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(lean_object* v_id_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1531_ = lean_box(0);
lean_inc(v_id_1527_);
v___x_1532_ = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed), 5, 2);
lean_closure_set(v___x_1532_, 0, v_id_1527_);
lean_closure_set(v___x_1532_, 1, v___x_1531_);
v___x_1533_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1532_, v_a_1528_, v_a_1529_);
if (lean_obj_tag(v___x_1533_) == 0)
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1571_; 
v_a_1534_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1536_ = v___x_1533_;
v_isShared_1537_ = v_isSharedCheck_1571_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v___x_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1571_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; lean_object* v_env_1539_; lean_object* v___x_1540_; 
v___x_1538_ = lean_st_ref_get(v_a_1529_);
v_env_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc_ref(v_env_1539_);
lean_dec(v___x_1538_);
v___x_1540_ = l_Lean_PostprocessTraces_findStoredTrace_x3f(v_env_1539_, v_a_1534_);
lean_dec(v_a_1534_);
if (lean_obj_tag(v___x_1540_) == 1)
{
lean_object* v_val_1541_; lean_object* v___x_1543_; 
lean_dec(v_id_1527_);
v_val_1541_ = lean_ctor_get(v___x_1540_, 0);
lean_inc(v_val_1541_);
lean_dec_ref_known(v___x_1540_, 1);
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 0, v_val_1541_);
v___x_1543_ = v___x_1536_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_val_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
else
{
lean_object* v___x_1545_; lean_object* v___y_1547_; lean_object* v_env_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; uint8_t v___x_1565_; 
lean_dec(v___x_1540_);
lean_del_object(v___x_1536_);
v___x_1545_ = lean_st_ref_get(v_a_1529_);
v_env_1561_ = lean_ctor_get(v___x_1545_, 0);
lean_inc_ref(v_env_1561_);
lean_dec(v___x_1545_);
v___x_1562_ = l_Lean_PostprocessTraces_allStoredTraces(v_env_1561_);
v___x_1563_ = lean_box(0);
v___x_1564_ = l_List_mapTR_loop___at___00__private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace_spec__0(v___x_1562_, v___x_1563_);
v___x_1565_ = l_List_isEmpty___redArg(v___x_1564_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1566_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9);
v___x_1567_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12);
v___x_1568_ = l_Lean_MessageData_joinSep(v___x_1564_, v___x_1567_);
v___x_1569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1566_);
lean_ctor_set(v___x_1569_, 1, v___x_1568_);
v___y_1547_ = v___x_1569_;
goto v___jp_1546_;
}
else
{
lean_object* v___x_1570_; 
lean_dec(v___x_1564_);
v___x_1570_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14);
v___y_1547_ = v___x_1570_;
goto v___jp_1546_;
}
v___jp_1546_:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1548_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1);
v___x_1549_ = l_Lean_TSyntax_getId(v_id_1527_);
v___x_1550_ = l_Lean_MessageData_ofName(v___x_1549_);
lean_inc_ref(v___x_1550_);
v___x_1551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1551_, 0, v___x_1548_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
v___x_1552_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3);
v___x_1553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1551_);
lean_ctor_set(v___x_1553_, 1, v___x_1552_);
v___x_1554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
lean_ctor_set(v___x_1554_, 1, v___y_1547_);
v___x_1555_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5);
v___x_1556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1554_);
lean_ctor_set(v___x_1556_, 1, v___x_1555_);
v___x_1557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v___x_1550_);
v___x_1558_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7);
v___x_1559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1557_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_id_1527_, v___x_1559_, v_a_1528_, v_a_1529_);
lean_dec(v_id_1527_);
return v___x_1560_;
}
}
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec(v_id_1527_);
v_a_1572_ = lean_ctor_get(v___x_1533_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1533_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1533_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1533_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___boxed(lean_object* v_id_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(v_id_1580_, v_a_1581_, v_a_1582_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
return v_res_1584_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0(uint8_t v_suppressElabErrors_1586_, lean_object* v_x_1587_){
_start:
{
if (lean_obj_tag(v_x_1587_) == 1)
{
lean_object* v_pre_1588_; 
v_pre_1588_ = lean_ctor_get(v_x_1587_, 0);
if (lean_obj_tag(v_pre_1588_) == 0)
{
lean_object* v_str_1589_; lean_object* v___x_1590_; uint8_t v___x_1591_; 
v_str_1589_ = lean_ctor_get(v_x_1587_, 1);
v___x_1590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___closed__0));
v___x_1591_ = lean_string_dec_eq(v_str_1589_, v___x_1590_);
if (v___x_1591_ == 0)
{
return v___x_1591_;
}
else
{
return v_suppressElabErrors_1586_;
}
}
else
{
uint8_t v___x_1592_; 
v___x_1592_ = 0;
return v___x_1592_;
}
}
else
{
uint8_t v___x_1593_; 
v___x_1593_ = 0;
return v___x_1593_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_1594_, lean_object* v_x_1595_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1596_; uint8_t v_res_1597_; lean_object* v_r_1598_; 
v_suppressElabErrors_boxed_1596_ = lean_unbox(v_suppressElabErrors_1594_);
v_res_1597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0(v_suppressElabErrors_boxed_1596_, v_x_1595_);
lean_dec(v_x_1595_);
v_r_1598_ = lean_box(v_res_1597_);
return v_r_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v_as_1601_, size_t v_sz_1602_, size_t v_i_1603_, lean_object* v_b_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_a_1609_; uint8_t v___x_1613_; 
v___x_1613_ = lean_usize_dec_lt(v_i_1603_, v_sz_1602_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
v___x_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1614_, 0, v_b_1604_);
return v___x_1614_;
}
else
{
lean_object* v_fileName_1615_; lean_object* v_fileMap_1616_; uint8_t v_suppressElabErrors_1617_; lean_object* v_a_1618_; lean_object* v_data_1619_; lean_object* v___x_1620_; uint8_t v___x_1621_; lean_object* v___x_1622_; lean_object* v___y_1624_; 
v_fileName_1615_ = lean_ctor_get(v___y_1605_, 0);
v_fileMap_1616_ = lean_ctor_get(v___y_1605_, 1);
v_suppressElabErrors_1617_ = lean_ctor_get_uint8(v___y_1605_, sizeof(void*)*10);
v_a_1618_ = lean_array_uget_borrowed(v_as_1601_, v_i_1603_);
v_data_1619_ = lean_ctor_get(v_a_1618_, 4);
v___x_1620_ = lean_box(0);
v___x_1621_ = 0;
lean_inc(v_data_1619_);
lean_inc_ref(v_fileMap_1616_);
lean_inc_ref(v_fileName_1615_);
v___x_1622_ = l_Lean_Elab_mkMessageCore(v_fileName_1615_, v_fileMap_1616_, v_data_1619_, v___x_1621_, v___y_1599_, v___y_1600_);
if (v_suppressElabErrors_1617_ == 0)
{
v___y_1624_ = v___y_1606_;
goto v___jp_1623_;
}
else
{
lean_object* v_data_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; uint8_t v___x_1690_; 
v_data_1687_ = lean_ctor_get(v___x_1622_, 4);
lean_inc(v_data_1687_);
v___x_1688_ = lean_box(v_suppressElabErrors_1617_);
v___f_1689_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1689_, 0, v___x_1688_);
v___x_1690_ = l_Lean_MessageData_hasTag(v___f_1689_, v_data_1687_);
if (v___x_1690_ == 0)
{
lean_dec_ref(v___x_1622_);
v_a_1609_ = v___x_1620_;
goto v___jp_1608_;
}
else
{
v___y_1624_ = v___y_1606_;
goto v___jp_1623_;
}
}
v___jp_1623_:
{
lean_object* v___x_1625_; 
v___x_1625_ = l_Lean_Elab_Command_getScope___redArg(v___y_1624_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v_currNamespace_1627_; lean_object* v___x_1628_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v___x_1625_, 1);
v_currNamespace_1627_ = lean_ctor_get(v_a_1626_, 2);
lean_inc(v_currNamespace_1627_);
lean_dec(v_a_1626_);
v___x_1628_ = l_Lean_Elab_Command_getScope___redArg(v___y_1624_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v_openDecls_1630_; lean_object* v_fileName_1631_; lean_object* v_pos_1632_; lean_object* v_endPos_1633_; uint8_t v_keepFullRange_1634_; uint8_t v_severity_1635_; uint8_t v_isSilent_1636_; lean_object* v_caption_1637_; lean_object* v_data_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1670_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v___x_1628_, 1);
v_openDecls_1630_ = lean_ctor_get(v_a_1629_, 3);
lean_inc(v_openDecls_1630_);
lean_dec(v_a_1629_);
v_fileName_1631_ = lean_ctor_get(v___x_1622_, 0);
v_pos_1632_ = lean_ctor_get(v___x_1622_, 1);
v_endPos_1633_ = lean_ctor_get(v___x_1622_, 2);
v_keepFullRange_1634_ = lean_ctor_get_uint8(v___x_1622_, sizeof(void*)*5);
v_severity_1635_ = lean_ctor_get_uint8(v___x_1622_, sizeof(void*)*5 + 1);
v_isSilent_1636_ = lean_ctor_get_uint8(v___x_1622_, sizeof(void*)*5 + 2);
v_caption_1637_ = lean_ctor_get(v___x_1622_, 3);
v_data_1638_ = lean_ctor_get(v___x_1622_, 4);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1640_ = v___x_1622_;
v_isShared_1641_ = v_isSharedCheck_1670_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_data_1638_);
lean_inc(v_caption_1637_);
lean_inc(v_endPos_1633_);
lean_inc(v_pos_1632_);
lean_inc(v_fileName_1631_);
lean_dec(v___x_1622_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1670_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1645_; 
v___x_1642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1642_, 0, v_currNamespace_1627_);
lean_ctor_set(v___x_1642_, 1, v_openDecls_1630_);
v___x_1643_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v_data_1638_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 4, v___x_1643_);
v___x_1645_ = v___x_1640_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_fileName_1631_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_pos_1632_);
lean_ctor_set(v_reuseFailAlloc_1669_, 2, v_endPos_1633_);
lean_ctor_set(v_reuseFailAlloc_1669_, 3, v_caption_1637_);
lean_ctor_set(v_reuseFailAlloc_1669_, 4, v___x_1643_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*5, v_keepFullRange_1634_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*5 + 1, v_severity_1635_);
lean_ctor_set_uint8(v_reuseFailAlloc_1669_, sizeof(void*)*5 + 2, v_isSilent_1636_);
v___x_1645_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
lean_object* v___x_1646_; lean_object* v_env_1647_; lean_object* v_messages_1648_; lean_object* v_scopes_1649_; lean_object* v_usedQuotCtxts_1650_; lean_object* v_nextMacroScope_1651_; lean_object* v_maxRecDepth_1652_; lean_object* v_ngen_1653_; lean_object* v_auxDeclNGen_1654_; lean_object* v_infoState_1655_; lean_object* v_traceState_1656_; lean_object* v_snapshotTasks_1657_; lean_object* v_prevLinterStates_1658_; lean_object* v_codeQualityEntryTasks_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1668_; 
v___x_1646_ = lean_st_ref_take(v___y_1624_);
v_env_1647_ = lean_ctor_get(v___x_1646_, 0);
v_messages_1648_ = lean_ctor_get(v___x_1646_, 1);
v_scopes_1649_ = lean_ctor_get(v___x_1646_, 2);
v_usedQuotCtxts_1650_ = lean_ctor_get(v___x_1646_, 3);
v_nextMacroScope_1651_ = lean_ctor_get(v___x_1646_, 4);
v_maxRecDepth_1652_ = lean_ctor_get(v___x_1646_, 5);
v_ngen_1653_ = lean_ctor_get(v___x_1646_, 6);
v_auxDeclNGen_1654_ = lean_ctor_get(v___x_1646_, 7);
v_infoState_1655_ = lean_ctor_get(v___x_1646_, 8);
v_traceState_1656_ = lean_ctor_get(v___x_1646_, 9);
v_snapshotTasks_1657_ = lean_ctor_get(v___x_1646_, 10);
v_prevLinterStates_1658_ = lean_ctor_get(v___x_1646_, 11);
v_codeQualityEntryTasks_1659_ = lean_ctor_get(v___x_1646_, 12);
v_isSharedCheck_1668_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1661_ = v___x_1646_;
v_isShared_1662_ = v_isSharedCheck_1668_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1659_);
lean_inc(v_prevLinterStates_1658_);
lean_inc(v_snapshotTasks_1657_);
lean_inc(v_traceState_1656_);
lean_inc(v_infoState_1655_);
lean_inc(v_auxDeclNGen_1654_);
lean_inc(v_ngen_1653_);
lean_inc(v_maxRecDepth_1652_);
lean_inc(v_nextMacroScope_1651_);
lean_inc(v_usedQuotCtxts_1650_);
lean_inc(v_scopes_1649_);
lean_inc(v_messages_1648_);
lean_inc(v_env_1647_);
lean_dec(v___x_1646_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1668_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = l_Lean_MessageLog_add(v___x_1645_, v_messages_1648_);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v___x_1663_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_env_1647_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1667_, 2, v_scopes_1649_);
lean_ctor_set(v_reuseFailAlloc_1667_, 3, v_usedQuotCtxts_1650_);
lean_ctor_set(v_reuseFailAlloc_1667_, 4, v_nextMacroScope_1651_);
lean_ctor_set(v_reuseFailAlloc_1667_, 5, v_maxRecDepth_1652_);
lean_ctor_set(v_reuseFailAlloc_1667_, 6, v_ngen_1653_);
lean_ctor_set(v_reuseFailAlloc_1667_, 7, v_auxDeclNGen_1654_);
lean_ctor_set(v_reuseFailAlloc_1667_, 8, v_infoState_1655_);
lean_ctor_set(v_reuseFailAlloc_1667_, 9, v_traceState_1656_);
lean_ctor_set(v_reuseFailAlloc_1667_, 10, v_snapshotTasks_1657_);
lean_ctor_set(v_reuseFailAlloc_1667_, 11, v_prevLinterStates_1658_);
lean_ctor_set(v_reuseFailAlloc_1667_, 12, v_codeQualityEntryTasks_1659_);
v___x_1665_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; 
v___x_1666_ = lean_st_ref_put(v___y_1624_, v___x_1665_);
v_a_1609_ = v___x_1620_;
goto v___jp_1608_;
}
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_dec(v_currNamespace_1627_);
lean_dec_ref(v___x_1622_);
v_a_1671_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1628_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1628_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_dec_ref(v___x_1622_);
v_a_1679_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1625_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1625_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
}
v___jp_1608_:
{
size_t v___x_1610_; size_t v___x_1611_; 
v___x_1610_ = ((size_t)1ULL);
v___x_1611_ = lean_usize_add(v_i_1603_, v___x_1610_);
v_i_1603_ = v___x_1611_;
v_b_1604_ = v_a_1609_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___boxed(lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v_as_1693_, lean_object* v_sz_1694_, lean_object* v_i_1695_, lean_object* v_b_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
size_t v_sz_boxed_1700_; size_t v_i_boxed_1701_; lean_object* v_res_1702_; 
v_sz_boxed_1700_ = lean_unbox_usize(v_sz_1694_);
lean_dec(v_sz_1694_);
v_i_boxed_1701_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(v___y_1691_, v___y_1692_, v_as_1693_, v_sz_boxed_1700_, v_i_boxed_1701_, v_b_1696_, v___y_1697_, v___y_1698_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec_ref(v_as_1693_);
lean_dec(v___y_1692_);
lean_dec(v___y_1691_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces(lean_object* v_x_1703_, lean_object* v_a_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v___x_1707_; uint8_t v___x_1708_; 
v___x_1707_ = ((lean_object*)(l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1));
lean_inc(v_x_1703_);
v___x_1708_ = l_Lean_Syntax_isOfKind(v_x_1703_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_object* v___x_1709_; 
lean_dec(v_x_1703_);
v___x_1709_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_1709_;
}
else
{
lean_object* v___x_1710_; lean_object* v_id_1711_; lean_object* v___x_1712_; lean_object* v_post_1713_; lean_object* v___x_1714_; 
v___x_1710_ = lean_unsigned_to_nat(1u);
v_id_1711_ = l_Lean_Syntax_getArg(v_x_1703_, v___x_1710_);
v___x_1712_ = lean_unsigned_to_nat(2u);
v_post_1713_ = l_Lean_Syntax_getArg(v_x_1703_, v___x_1712_);
lean_dec(v_x_1703_);
v___x_1714_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(v_id_1711_, v_a_1704_, v_a_1705_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1716_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1713_, v_a_1704_, v_a_1705_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v___x_1718_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_StoredTrace_postprocess___boxed), 5, 2);
lean_closure_set(v___x_1718_, 0, v_a_1715_);
lean_closure_set(v___x_1718_, 1, v_a_1717_);
v___x_1719_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1718_, v_a_1704_, v_a_1705_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = l_Lean_Elab_Command_getRef___redArg(v_a_1704_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___y_1724_; lean_object* v___y_1725_; uint8_t v___x_1738_; lean_object* v___y_1740_; lean_object* v___x_1743_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1738_ = 0;
v___x_1743_ = l_Lean_Syntax_getPos_x3f(v_a_1722_, v___x_1738_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_unsigned_to_nat(0u);
v___y_1740_ = v___x_1744_;
goto v___jp_1739_;
}
else
{
lean_object* v_val_1745_; 
v_val_1745_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1745_);
lean_dec_ref_known(v___x_1743_, 1);
v___y_1740_ = v_val_1745_;
goto v___jp_1739_;
}
v___jp_1723_:
{
lean_object* v___x_1726_; size_t v_sz_1727_; size_t v___x_1728_; lean_object* v___x_1729_; 
v___x_1726_ = lean_box(0);
v_sz_1727_ = lean_array_size(v_a_1720_);
v___x_1728_ = ((size_t)0ULL);
v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(v___y_1724_, v___y_1725_, v_a_1720_, v_sz_1727_, v___x_1728_, v___x_1726_, v_a_1704_, v_a_1705_);
lean_dec(v_a_1720_);
lean_dec(v___y_1725_);
lean_dec(v___y_1724_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1736_ == 0)
{
lean_object* v_unused_1737_; 
v_unused_1737_ = lean_ctor_get(v___x_1729_, 0);
lean_dec(v_unused_1737_);
v___x_1731_ = v___x_1729_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_dec(v___x_1729_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 0, v___x_1726_);
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1726_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
else
{
return v___x_1729_;
}
}
v___jp_1739_:
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_Syntax_getTailPos_x3f(v_a_1722_, v___x_1738_);
lean_dec(v_a_1722_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_inc(v___y_1740_);
v___y_1724_ = v___y_1740_;
v___y_1725_ = v___y_1740_;
goto v___jp_1723_;
}
else
{
lean_object* v_val_1742_; 
v_val_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_val_1742_);
lean_dec_ref_known(v___x_1741_, 1);
v___y_1724_ = v___y_1740_;
v___y_1725_ = v_val_1742_;
goto v___jp_1723_;
}
}
}
else
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
lean_dec(v_a_1720_);
v_a_1746_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v___x_1721_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v___x_1721_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v___x_1719_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v___x_1719_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1760_, 0, v_a_1754_);
v___x_1759_ = v_reuseFailAlloc_1760_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
return v___x_1759_;
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1715_);
v_a_1762_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1716_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1716_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_post_1713_);
v_a_1770_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1714_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1714_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces___boxed(lean_object* v_x_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces(v_x_1778_, v_a_1779_, v_a_1780_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
return v_res_1782_;
}
}
lean_object* runtime_initialize_Lean_CoreM(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PostprocessTraces_StoredTraces(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
