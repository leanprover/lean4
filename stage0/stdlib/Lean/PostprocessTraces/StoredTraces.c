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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
lean_object* l_Lean_DeclarationRange_ofStringPositions(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedDeclarationRanges_default;
extern lean_object* l_Lean_declRangeExt;
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__1_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__1_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__1_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__2_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__1_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__2_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__2_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__3_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__2_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__3_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__3_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__4_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__3_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 174, 235, 17, 5, 20, 197, 19)}};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__4_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__4_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__5_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "StoredTraces"};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__5_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__5_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__6_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__4_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__5_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(143, 140, 81, 237, 236, 170, 11, 110)}};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__6_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__6_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__7_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__6_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(34, 130, 249, 220, 32, 191, 165, 90)}};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__7_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__7_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__8_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__7_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(3, 89, 114, 131, 249, 230, 156, 240)}};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__8_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__8_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__9_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__8_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),((lean_object*)&l_Lean_PostprocessTraces_storeTracesAsCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(128, 162, 58, 245, 173, 21, 89, 88)}};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__9_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__9_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__10_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "storedTracesExt"};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__10_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__10_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__11_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__9_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__10_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(76, 236, 246, 31, 123, 104, 193, 42)}};
static const lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__11_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__11_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2__value;
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
lean_object* v___f_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; 
v___f_130_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__0_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_));
v___x_131_ = lean_box(0);
v___x_132_ = lean_box(2);
v___x_133_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn___closed__11_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_));
v___x_134_ = 0;
v___x_135_ = l_Lean_registerEnvExtension___redArg(v___f_130_, v___x_131_, v___x_132_, v___x_133_, v___x_134_, v___x_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2____boxed(lean_object* v_a_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_initFn_00___x40_Lean_PostprocessTraces_StoredTraces_3838848863____hygCtx___hyg_2_();
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace_x3f(lean_object* v_env_138_, lean_object* v_declName_139_){
_start:
{
lean_object* v___x_140_; lean_object* v_asyncMode_141_; lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_140_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt;
v_asyncMode_141_ = lean_ctor_get(v___x_140_, 2);
v___x_142_ = lean_box(1);
v___x_143_ = lean_box(0);
v___x_144_ = 0;
v___x_145_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_142_, v___x_140_, v_env_138_, v_asyncMode_141_, v___x_143_, v___x_144_);
v___x_146_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_145_, v_declName_139_);
lean_dec(v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace_x3f___boxed(lean_object* v_env_147_, lean_object* v_declName_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean_PostprocessTraces_findStoredTrace_x3f(v_env_147_, v_declName_148_);
lean_dec(v_declName_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0(lean_object* v_init_150_, lean_object* v_x_151_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v_k_152_; lean_object* v_v_153_; lean_object* v_l_154_; lean_object* v_r_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; 
v_k_152_ = lean_ctor_get(v_x_151_, 1);
v_v_153_ = lean_ctor_get(v_x_151_, 2);
v_l_154_ = lean_ctor_get(v_x_151_, 3);
v_r_155_ = lean_ctor_get(v_x_151_, 4);
v___x_156_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0(v_init_150_, v_r_155_);
lean_inc(v_v_153_);
lean_inc(v_k_152_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v_k_152_);
lean_ctor_set(v___x_157_, 1, v_v_153_);
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v___x_156_);
v_init_150_ = v___x_158_;
v_x_151_ = v_l_154_;
goto _start;
}
else
{
return v_init_150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0___boxed(lean_object* v_init_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0(v_init_160_, v_x_161_);
lean_dec(v_x_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_allStoredTraces(lean_object* v_env_163_){
_start:
{
lean_object* v___x_164_; lean_object* v_asyncMode_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_164_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt;
v_asyncMode_165_ = lean_ctor_get(v___x_164_, 2);
v___x_166_ = lean_box(1);
v___x_167_ = lean_box(0);
v___x_168_ = 0;
v___x_169_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_166_, v___x_164_, v_env_163_, v_asyncMode_165_, v___x_167_, v___x_168_);
v___x_170_ = lean_box(0);
v___x_171_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_PostprocessTraces_allStoredTraces_spec__0(v___x_170_, v___x_169_);
lean_dec(v___x_169_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_172_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_175_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_176_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1);
v___x_177_ = lean_unsigned_to_nat(0u);
v___x_178_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
lean_ctor_set(v___x_178_, 2, v___x_177_);
lean_ctor_set(v___x_178_, 3, v___x_177_);
lean_ctor_set(v___x_178_, 4, v___x_176_);
lean_ctor_set(v___x_178_, 5, v___x_176_);
lean_ctor_set(v___x_178_, 6, v___x_176_);
lean_ctor_set(v___x_178_, 7, v___x_176_);
lean_ctor_set(v___x_178_, 8, v___x_176_);
lean_ctor_set(v___x_178_, 9, v___x_176_);
lean_ctor_set(v___x_178_, 10, v___x_176_);
lean_ctor_set(v___x_178_, 11, v___x_175_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(32u);
v___x_180_ = lean_mk_empty_array_with_capacity(v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4(void){
_start:
{
size_t v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_182_ = ((size_t)5ULL);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_unsigned_to_nat(32u);
v___x_185_ = lean_mk_empty_array_with_capacity(v___x_184_);
v___x_186_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__3);
v___x_187_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v___x_185_);
lean_ctor_set(v___x_187_, 2, v___x_183_);
lean_ctor_set(v___x_187_, 3, v___x_183_);
lean_ctor_set_usize(v___x_187_, 4, v___x_182_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_188_ = lean_box(1);
v___x_189_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__4);
v___x_190_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__1);
v___x_191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_189_);
lean_ctor_set(v___x_191_, 2, v___x_188_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0(lean_object* v_msgData_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
lean_object* v___x_196_; lean_object* v_toCold_197_; lean_object* v_env_198_; lean_object* v_options_199_; uint8_t v___x_200_; lean_object* v_env_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_196_ = lean_st_ref_get(v___y_194_);
v_toCold_197_ = lean_ctor_get(v___y_193_, 0);
v_env_198_ = lean_ctor_get(v___x_196_, 0);
lean_inc_ref(v_env_198_);
lean_dec(v___x_196_);
v_options_199_ = lean_ctor_get(v_toCold_197_, 2);
v___x_200_ = 0;
v_env_201_ = l_Lean_Environment_setRecordingDeps(v_env_198_, v___x_200_);
v___x_202_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_203_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
lean_inc_ref(v_options_199_);
v___x_204_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_204_, 0, v_env_201_);
lean_ctor_set(v___x_204_, 1, v___x_202_);
lean_ctor_set(v___x_204_, 2, v___x_203_);
lean_ctor_set(v___x_204_, 3, v_options_199_);
v___x_205_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
lean_ctor_set(v___x_205_, 1, v_msgData_192_);
v___x_206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___boxed(lean_object* v_msgData_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0(v_msgData_207_, v___y_208_, v___y_209_);
lean_dec(v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(lean_object* v_msg_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_ref_216_; lean_object* v___x_217_; lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_226_; 
v_ref_216_ = lean_ctor_get(v___y_213_, 2);
v___x_217_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0(v_msg_212_, v___y_213_, v___y_214_);
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_226_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_226_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_226_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; lean_object* v___x_224_; 
lean_inc(v_ref_216_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_ref_216_);
lean_ctor_set(v___x_222_, 1, v_a_218_);
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 1);
lean_ctor_set(v___x_220_, 0, v___x_222_);
v___x_224_ = v___x_220_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg___boxed(lean_object* v_msg_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v_msg_227_, v___y_228_, v___y_229_);
lean_dec(v___y_229_);
lean_dec_ref(v___y_228_);
return v_res_231_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_findStoredTrace___closed__1(void){
_start:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_233_ = ((lean_object*)(l_Lean_PostprocessTraces_findStoredTrace___closed__0));
v___x_234_ = l_Lean_stringToMessageData(v___x_233_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_findStoredTrace___closed__3(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_236_ = ((lean_object*)(l_Lean_PostprocessTraces_findStoredTrace___closed__2));
v___x_237_ = l_Lean_stringToMessageData(v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace(lean_object* v_declName_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v___x_242_; lean_object* v_env_243_; lean_object* v___x_244_; 
v___x_242_ = lean_st_ref_get(v_a_240_);
v_env_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc_ref(v_env_243_);
lean_dec(v___x_242_);
v___x_244_ = l_Lean_PostprocessTraces_findStoredTrace_x3f(v_env_243_, v_declName_238_);
if (lean_obj_tag(v___x_244_) == 1)
{
lean_object* v_val_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec(v_declName_238_);
v_val_245_ = lean_ctor_get(v___x_244_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_244_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_244_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_val_245_);
lean_dec(v___x_244_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 0);
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_val_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
lean_dec(v___x_244_);
v___x_253_ = lean_obj_once(&l_Lean_PostprocessTraces_findStoredTrace___closed__1, &l_Lean_PostprocessTraces_findStoredTrace___closed__1_once, _init_l_Lean_PostprocessTraces_findStoredTrace___closed__1);
v___x_254_ = l_Lean_MessageData_ofName(v_declName_238_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_obj_once(&l_Lean_PostprocessTraces_findStoredTrace___closed__3, &l_Lean_PostprocessTraces_findStoredTrace___closed__3_once, _init_l_Lean_PostprocessTraces_findStoredTrace___closed__3);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v___x_257_, v_a_239_, v_a_240_);
return v___x_258_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_findStoredTrace___boxed(lean_object* v_declName_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lean_PostprocessTraces_findStoredTrace(v_declName_259_, v_a_260_, v_a_261_);
lean_dec(v_a_261_);
lean_dec_ref(v_a_260_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0(lean_object* v_00_u03b1_264_, lean_object* v_msg_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v_msg_265_, v___y_266_, v___y_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___boxed(lean_object* v_00_u03b1_270_, lean_object* v_msg_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0(v_00_u03b1_270_, v_msg_271_, v___y_272_, v___y_273_);
lean_dec(v___y_273_);
lean_dec_ref(v___y_272_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___lam__0(lean_object* v_declName_276_, lean_object* v_t_277_, lean_object* v_x_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_declName_276_, v_t_277_, v_x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__0(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__0);
v___x_281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__1(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__0, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__0_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__0);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg(lean_object* v_declName_284_, lean_object* v_t_285_, lean_object* v_a_286_){
_start:
{
lean_object* v___f_288_; lean_object* v___x_289_; lean_object* v_env_290_; lean_object* v_nextMacroScope_291_; lean_object* v_ngen_292_; lean_object* v_auxDeclNGen_293_; lean_object* v_traceState_294_; lean_object* v_recordedDeps_295_; lean_object* v_messages_296_; lean_object* v_infoState_297_; lean_object* v_snapshotTasks_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_319_; 
v___f_288_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_storeTraces___redArg___lam__0), 3, 2);
lean_closure_set(v___f_288_, 0, v_declName_284_);
lean_closure_set(v___f_288_, 1, v_t_285_);
v___x_289_ = lean_st_ref_take(v_a_286_);
v_env_290_ = lean_ctor_get(v___x_289_, 0);
v_nextMacroScope_291_ = lean_ctor_get(v___x_289_, 1);
v_ngen_292_ = lean_ctor_get(v___x_289_, 2);
v_auxDeclNGen_293_ = lean_ctor_get(v___x_289_, 3);
v_traceState_294_ = lean_ctor_get(v___x_289_, 4);
v_recordedDeps_295_ = lean_ctor_get(v___x_289_, 6);
v_messages_296_ = lean_ctor_get(v___x_289_, 7);
v_infoState_297_ = lean_ctor_get(v___x_289_, 8);
v_snapshotTasks_298_ = lean_ctor_get(v___x_289_, 9);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_319_ == 0)
{
lean_object* v_unused_320_; 
v_unused_320_ = lean_ctor_get(v___x_289_, 5);
lean_dec(v_unused_320_);
v___x_300_ = v___x_289_;
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_snapshotTasks_298_);
lean_inc(v_infoState_297_);
lean_inc(v_messages_296_);
lean_inc(v_recordedDeps_295_);
lean_inc(v_traceState_294_);
lean_inc(v_auxDeclNGen_293_);
lean_inc(v_ngen_292_);
lean_inc(v_nextMacroScope_291_);
lean_inc(v_env_290_);
lean_dec(v___x_289_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_319_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v_asyncMode_303_; uint8_t v_logWrites_304_; lean_object* v___x_305_; lean_object* v___y_307_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_302_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_PostprocessTraces_storedTracesExt;
v_asyncMode_303_ = lean_ctor_get(v___x_302_, 2);
v_logWrites_304_ = lean_ctor_get_uint8(v___x_302_, sizeof(void*)*6);
v___x_305_ = lean_box(0);
v___x_314_ = lean_box(0);
v___x_315_ = 1;
if (v_logWrites_304_ == 0)
{
lean_object* v___x_316_; 
v___x_316_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_302_, v_env_290_, v___f_288_, v_asyncMode_303_, v___x_314_, v___x_315_);
v___y_307_ = v___x_316_;
goto v___jp_306_;
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_302_, v_env_290_);
lean_dec_ref(v_env_290_);
v___x_318_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_302_, v___x_317_, v___f_288_, v_asyncMode_303_, v___x_314_, v___x_315_);
v___y_307_ = v___x_318_;
goto v___jp_306_;
}
v___jp_306_:
{
lean_object* v___x_308_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__1, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__1_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__1);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 5, v___x_308_);
lean_ctor_set(v___x_300_, 0, v___y_307_);
v___x_310_ = v___x_300_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v___y_307_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v_nextMacroScope_291_);
lean_ctor_set(v_reuseFailAlloc_313_, 2, v_ngen_292_);
lean_ctor_set(v_reuseFailAlloc_313_, 3, v_auxDeclNGen_293_);
lean_ctor_set(v_reuseFailAlloc_313_, 4, v_traceState_294_);
lean_ctor_set(v_reuseFailAlloc_313_, 5, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_313_, 6, v_recordedDeps_295_);
lean_ctor_set(v_reuseFailAlloc_313_, 7, v_messages_296_);
lean_ctor_set(v_reuseFailAlloc_313_, 8, v_infoState_297_);
lean_ctor_set(v_reuseFailAlloc_313_, 9, v_snapshotTasks_298_);
v___x_310_ = v_reuseFailAlloc_313_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = lean_st_ref_put(v_a_286_, v___x_310_);
v___x_312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_312_, 0, v___x_305_);
return v___x_312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___redArg___boxed(lean_object* v_declName_321_, lean_object* v_t_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_PostprocessTraces_storeTraces___redArg(v_declName_321_, v_t_322_, v_a_323_);
lean_dec(v_a_323_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces(lean_object* v_declName_326_, lean_object* v_t_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = l_Lean_PostprocessTraces_storeTraces___redArg(v_declName_326_, v_t_327_, v_a_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_storeTraces___boxed(lean_object* v_declName_332_, lean_object* v_t_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_PostprocessTraces_storeTraces(v_declName_332_, v_t_333_, v_a_334_, v_a_335_);
lean_dec(v_a_335_);
lean_dec_ref(v_a_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(size_t v_sz_338_, size_t v_i_339_, lean_object* v_bs_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = lean_usize_dec_lt(v_i_339_, v_sz_338_);
if (v___x_341_ == 0)
{
return v_bs_340_;
}
else
{
lean_object* v_v_342_; lean_object* v___x_343_; lean_object* v_bs_x27_344_; lean_object* v___x_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v_v_342_ = lean_array_uget(v_bs_340_, v_i_339_);
v___x_343_ = lean_unsigned_to_nat(0u);
v_bs_x27_344_ = lean_array_uset(v_bs_340_, v_i_339_, v___x_343_);
v___x_345_ = l_Lean_PostprocessTraces_TraceTree_ofMessageData(v_v_342_);
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_add(v_i_339_, v___x_346_);
v___x_348_ = lean_array_uset(v_bs_x27_344_, v_i_339_, v___x_345_);
v_i_339_ = v___x_347_;
v_bs_340_ = v___x_348_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0___boxed(lean_object* v_sz_350_, lean_object* v_i_351_, lean_object* v_bs_352_){
_start:
{
size_t v_sz_boxed_353_; size_t v_i_boxed_354_; lean_object* v_res_355_; 
v_sz_boxed_353_ = lean_unbox_usize(v_sz_350_);
lean_dec(v_sz_350_);
v_i_boxed_354_ = lean_unbox_usize(v_i_351_);
lean_dec(v_i_351_);
v_res_355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(v_sz_boxed_353_, v_i_boxed_354_, v_bs_352_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(lean_object* v_as_358_, size_t v_i_359_, size_t v_stop_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___y_363_; uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_eq(v_i_359_, v_stop_360_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v_data_369_; lean_object* v___x_370_; 
v___x_368_ = lean_array_uget_borrowed(v_as_358_, v_i_359_);
v_data_369_ = lean_ctor_get(v___x_368_, 4);
lean_inc(v_data_369_);
v___x_370_ = l_Lean_Elab_PostprocessTraces_traceContainer_x3f(v_data_369_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___closed__0));
v___x_372_ = l_Array_append___redArg(v_b_361_, v___x_371_);
v___y_363_ = v___x_372_;
goto v___jp_362_;
}
else
{
lean_object* v_val_373_; lean_object* v_snd_374_; size_t v_sz_375_; size_t v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v_val_373_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_val_373_);
lean_dec_ref_known(v___x_370_, 1);
v_snd_374_ = lean_ctor_get(v_val_373_, 1);
lean_inc(v_snd_374_);
lean_dec(v_val_373_);
v_sz_375_ = lean_array_size(v_snd_374_);
v___x_376_ = ((size_t)0ULL);
v___x_377_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__0(v_sz_375_, v___x_376_, v_snd_374_);
v___x_378_ = l_Array_append___redArg(v_b_361_, v___x_377_);
lean_dec_ref(v___x_377_);
v___y_363_ = v___x_378_;
goto v___jp_362_;
}
}
else
{
return v_b_361_;
}
v___jp_362_:
{
size_t v___x_364_; size_t v___x_365_; 
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_359_, v___x_364_);
v_i_359_ = v___x_365_;
v_b_361_ = v___y_363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1___boxed(lean_object* v_as_379_, lean_object* v_i_380_, lean_object* v_stop_381_, lean_object* v_b_382_){
_start:
{
size_t v_i_boxed_383_; size_t v_stop_boxed_384_; lean_object* v_res_385_; 
v_i_boxed_383_ = lean_unbox_usize(v_i_380_);
lean_dec(v_i_380_);
v_stop_boxed_384_ = lean_unbox_usize(v_stop_381_);
lean_dec(v_stop_381_);
v_res_385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(v_as_379_, v_i_boxed_383_, v_stop_boxed_384_, v_b_382_);
lean_dec_ref(v_as_379_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_trees(lean_object* v_t_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_389_ = lean_unsigned_to_nat(0u);
v___x_390_ = ((lean_object*)(l_Lean_PostprocessTraces_StoredTrace_trees___closed__0));
v___x_391_ = lean_array_get_size(v_t_388_);
v___x_392_ = lean_nat_dec_lt(v___x_389_, v___x_391_);
if (v___x_392_ == 0)
{
return v___x_390_;
}
else
{
size_t v___x_393_; size_t v___x_394_; lean_object* v___x_395_; 
v___x_393_ = ((size_t)0ULL);
v___x_394_ = lean_usize_of_nat(v___x_391_);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PostprocessTraces_StoredTrace_trees_spec__1(v_t_388_, v___x_393_, v___x_394_, v___x_390_);
return v___x_395_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_trees___boxed(lean_object* v_t_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_PostprocessTraces_StoredTrace_trees(v_t_396_);
lean_dec_ref(v_t_396_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(lean_object* v_post_398_, lean_object* v_as_399_, size_t v_i_400_, size_t v_stop_401_, lean_object* v_b_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_a_407_; uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_eq(v_i_400_, v_stop_401_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_array_uget_borrowed(v_as_399_, v_i_400_);
lean_inc(v___x_412_);
lean_inc_ref(v_post_398_);
v___x_413_ = l_Lean_Elab_PostprocessTraces_postprocessMessage(v_post_398_, v___x_412_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_a_414_; 
v_a_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_a_414_);
lean_dec_ref_known(v___x_413_, 1);
if (lean_obj_tag(v_a_414_) == 0)
{
v_a_407_ = v_b_402_;
goto v___jp_406_;
}
else
{
lean_object* v_val_415_; lean_object* v___x_416_; 
v_val_415_ = lean_ctor_get(v_a_414_, 0);
lean_inc(v_val_415_);
lean_dec_ref_known(v_a_414_, 1);
v___x_416_ = lean_array_push(v_b_402_, v_val_415_);
v_a_407_ = v___x_416_;
goto v___jp_406_;
}
}
else
{
lean_object* v_a_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_424_; 
lean_dec_ref(v_b_402_);
lean_dec_ref(v_post_398_);
v_a_417_ = lean_ctor_get(v___x_413_, 0);
v_isSharedCheck_424_ = !lean_is_exclusive(v___x_413_);
if (v_isSharedCheck_424_ == 0)
{
v___x_419_ = v___x_413_;
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_a_417_);
lean_dec(v___x_413_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_424_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_422_; 
if (v_isShared_420_ == 0)
{
v___x_422_ = v___x_419_;
goto v_reusejp_421_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_a_417_);
v___x_422_ = v_reuseFailAlloc_423_;
goto v_reusejp_421_;
}
v_reusejp_421_:
{
return v___x_422_;
}
}
}
}
else
{
lean_object* v___x_425_; 
lean_dec_ref(v_post_398_);
v___x_425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_425_, 0, v_b_402_);
return v___x_425_;
}
v___jp_406_:
{
size_t v___x_408_; size_t v___x_409_; 
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_add(v_i_400_, v___x_408_);
v_i_400_ = v___x_409_;
v_b_402_ = v_a_407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0___boxed(lean_object* v_post_426_, lean_object* v_as_427_, lean_object* v_i_428_, lean_object* v_stop_429_, lean_object* v_b_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_){
_start:
{
size_t v_i_boxed_434_; size_t v_stop_boxed_435_; lean_object* v_res_436_; 
v_i_boxed_434_ = lean_unbox_usize(v_i_428_);
lean_dec(v_i_428_);
v_stop_boxed_435_ = lean_unbox_usize(v_stop_429_);
lean_dec(v_stop_429_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(v_post_426_, v_as_427_, v_i_boxed_434_, v_stop_boxed_435_, v_b_430_, v___y_431_, v___y_432_);
lean_dec(v___y_432_);
lean_dec_ref(v___y_431_);
lean_dec_ref(v_as_427_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(lean_object* v_post_439_, lean_object* v_as_440_, lean_object* v_start_441_, lean_object* v_stop_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0));
v___x_447_ = lean_nat_dec_lt(v_start_441_, v_stop_442_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; 
lean_dec_ref(v_post_439_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_446_);
return v___x_448_;
}
else
{
lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_449_ = lean_array_get_size(v_as_440_);
v___x_450_ = lean_nat_dec_le(v_stop_442_, v___x_449_);
if (v___x_450_ == 0)
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_lt(v_start_441_, v___x_449_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; 
lean_dec_ref(v_post_439_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_446_);
return v___x_452_;
}
else
{
size_t v___x_453_; size_t v___x_454_; lean_object* v___x_455_; 
v___x_453_ = lean_usize_of_nat(v_start_441_);
v___x_454_ = lean_usize_of_nat(v___x_449_);
v___x_455_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(v_post_439_, v_as_440_, v___x_453_, v___x_454_, v___x_446_, v___y_443_, v___y_444_);
return v___x_455_;
}
}
else
{
size_t v___x_456_; size_t v___x_457_; lean_object* v___x_458_; 
v___x_456_ = lean_usize_of_nat(v_start_441_);
v___x_457_ = lean_usize_of_nat(v_stop_442_);
v___x_458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0_spec__0(v_post_439_, v_as_440_, v___x_456_, v___x_457_, v___x_446_, v___y_443_, v___y_444_);
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___boxed(lean_object* v_post_459_, lean_object* v_as_460_, lean_object* v_start_461_, lean_object* v_stop_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(v_post_459_, v_as_460_, v_start_461_, v_stop_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v_stop_462_);
lean_dec(v_start_461_);
lean_dec_ref(v_as_460_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_postprocess(lean_object* v_t_467_, lean_object* v_post_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = lean_unsigned_to_nat(0u);
v___x_473_ = lean_array_get_size(v_t_467_);
v___x_474_ = l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0(v_post_468_, v_t_467_, v___x_472_, v___x_473_, v_a_469_, v_a_470_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_474_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_474_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PostprocessTraces_StoredTrace_postprocess___boxed(lean_object* v_t_491_, lean_object* v_post_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_PostprocessTraces_StoredTrace_postprocess(v_t_491_, v_post_492_, v_a_493_, v_a_494_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
lean_dec_ref(v_t_491_);
return v_res_496_;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_box(0);
v___x_498_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg(){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___closed__0);
v___x_502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_502_, 0, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg___boxed(lean_object* v___y_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0(lean_object* v_00_u03b1_505_, lean_object* v___y_506_, lean_object* v___y_507_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___boxed(lean_object* v_00_u03b1_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0(v_00_u03b1_510_, v___y_511_, v___y_512_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(lean_object* v_as_515_, size_t v_i_516_, size_t v_stop_517_, lean_object* v_b_518_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = lean_usize_dec_eq(v_i_516_, v_stop_517_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; size_t v___x_522_; size_t v___x_523_; 
v___x_520_ = lean_array_uget_borrowed(v_as_515_, v_i_516_);
lean_inc(v___x_520_);
v___x_521_ = l_Lean_MessageLog_add(v___x_520_, v_b_518_);
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_add(v_i_516_, v___x_522_);
v_i_516_ = v___x_523_;
v_b_518_ = v___x_521_;
goto _start;
}
else
{
return v_b_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5___boxed(lean_object* v_as_525_, lean_object* v_i_526_, lean_object* v_stop_527_, lean_object* v_b_528_){
_start:
{
size_t v_i_boxed_529_; size_t v_stop_boxed_530_; lean_object* v_res_531_; 
v_i_boxed_529_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_stop_boxed_530_ = lean_unbox_usize(v_stop_527_);
lean_dec(v_stop_527_);
v_res_531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_as_525_, v_i_boxed_529_, v_stop_boxed_530_, v_b_528_);
lean_dec_ref(v_as_525_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(lean_object* v_as_532_, size_t v_i_533_, size_t v_stop_534_, lean_object* v_b_535_){
_start:
{
lean_object* v___y_537_; uint8_t v___x_541_; 
v___x_541_ = lean_usize_dec_eq(v_i_533_, v_stop_534_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_542_ = lean_array_uget_borrowed(v_as_532_, v_i_533_);
v___x_543_ = l_Lean_Message_isTrace(v___x_542_);
if (v___x_543_ == 0)
{
v___y_537_ = v_b_535_;
goto v___jp_536_;
}
else
{
lean_object* v___x_544_; 
lean_inc(v___x_542_);
v___x_544_ = lean_array_push(v_b_535_, v___x_542_);
v___y_537_ = v___x_544_;
goto v___jp_536_;
}
}
else
{
return v_b_535_;
}
v___jp_536_:
{
size_t v___x_538_; size_t v___x_539_; 
v___x_538_ = ((size_t)1ULL);
v___x_539_ = lean_usize_add(v_i_533_, v___x_538_);
v_i_533_ = v___x_539_;
v_b_535_ = v___y_537_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4___boxed(lean_object* v_as_545_, lean_object* v_i_546_, lean_object* v_stop_547_, lean_object* v_b_548_){
_start:
{
size_t v_i_boxed_549_; size_t v_stop_boxed_550_; lean_object* v_res_551_; 
v_i_boxed_549_ = lean_unbox_usize(v_i_546_);
lean_dec(v_i_546_);
v_stop_boxed_550_ = lean_unbox_usize(v_stop_547_);
lean_dec(v_stop_547_);
v_res_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_as_545_, v_i_boxed_549_, v_stop_boxed_550_, v_b_548_);
lean_dec_ref(v_as_545_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__7(lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
if (lean_obj_tag(v_a_552_) == 0)
{
lean_object* v___x_554_; 
v___x_554_ = l_List_reverse___redArg(v_a_553_);
return v___x_554_;
}
else
{
lean_object* v_head_555_; lean_object* v_tail_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_565_; 
v_head_555_ = lean_ctor_get(v_a_552_, 0);
v_tail_556_ = lean_ctor_get(v_a_552_, 1);
v_isSharedCheck_565_ = !lean_is_exclusive(v_a_552_);
if (v_isSharedCheck_565_ == 0)
{
v___x_558_ = v_a_552_;
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_tail_556_);
lean_inc(v_head_555_);
lean_dec(v_a_552_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_565_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = l_Lean_mkLevelParam(v_head_555_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v_a_553_);
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_564_, 1, v_a_553_);
v___x_562_ = v_reuseFailAlloc_564_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
v_a_552_ = v_tail_556_;
v_a_553_ = v___x_562_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1(void){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__0));
v___x_568_ = l_Lean_stringToMessageData(v___x_567_);
return v___x_568_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3(void){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__2));
v___x_571_ = l_Lean_stringToMessageData(v___x_570_);
return v___x_571_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_573_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__4));
v___x_574_ = l_Lean_stringToMessageData(v___x_573_);
return v___x_574_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_576_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__6));
v___x_577_ = l_Lean_stringToMessageData(v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_579_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__8));
v___x_580_ = l_Lean_stringToMessageData(v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_582_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__10));
v___x_583_ = l_Lean_stringToMessageData(v___x_582_);
return v___x_583_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_585_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__12));
v___x_586_ = l_Lean_stringToMessageData(v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(lean_object* v_msg_587_, lean_object* v_declHint_588_, lean_object* v___y_589_){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v_env_593_; uint8_t v___x_594_; 
v___x_591_ = lean_box(0);
v___x_592_ = lean_st_ref_get(v___y_589_);
v_env_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc_ref(v_env_593_);
lean_dec(v___x_592_);
v___x_594_ = l_Lean_Name_isAnonymous(v_declHint_588_);
if (v___x_594_ == 0)
{
uint8_t v_isExporting_595_; 
v_isExporting_595_ = lean_ctor_get_uint8(v_env_593_, sizeof(void*)*13);
if (v_isExporting_595_ == 0)
{
lean_object* v___x_596_; 
lean_dec_ref(v_env_593_);
lean_dec(v_declHint_588_);
v___x_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_596_, 0, v_msg_587_);
return v___x_596_;
}
else
{
lean_object* v___x_597_; uint8_t v___x_598_; 
lean_inc_ref(v_env_593_);
v___x_597_ = l_Lean_Environment_setExporting(v_env_593_, v___x_594_);
lean_inc(v_declHint_588_);
lean_inc_ref(v___x_597_);
v___x_598_ = l_Lean_Environment_contains(v___x_597_, v_declHint_588_, v_isExporting_595_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
lean_dec_ref(v___x_597_);
lean_dec_ref(v_env_593_);
lean_dec(v_declHint_588_);
v___x_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_599_, 0, v_msg_587_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_c_605_; lean_object* v___x_606_; 
v___x_600_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_601_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
v___x_602_ = l_Lean_Options_empty;
v___x_603_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_603_, 0, v___x_597_);
lean_ctor_set(v___x_603_, 1, v___x_600_);
lean_ctor_set(v___x_603_, 2, v___x_601_);
lean_ctor_set(v___x_603_, 3, v___x_602_);
lean_inc(v_declHint_588_);
v___x_604_ = l_Lean_MessageData_ofConstName(v_declHint_588_, v___x_594_);
v_c_605_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_605_, 0, v___x_603_);
lean_ctor_set(v_c_605_, 1, v___x_604_);
v___x_606_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_593_, v_declHint_588_);
if (lean_obj_tag(v___x_606_) == 0)
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec_ref(v_env_593_);
lean_dec(v_declHint_588_);
v___x_607_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_c_605_);
v___x_609_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3);
v___x_610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_608_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
v___x_611_ = l_Lean_MessageData_note(v___x_610_);
v___x_612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_612_, 0, v_msg_587_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___x_612_);
return v___x_613_;
}
else
{
lean_object* v_val_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_648_; 
v_val_614_ = lean_ctor_get(v___x_606_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_648_ == 0)
{
v___x_616_ = v___x_606_;
v_isShared_617_ = v_isSharedCheck_648_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_val_614_);
lean_dec(v___x_606_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_648_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_mod_620_; uint8_t v___x_621_; 
v___x_618_ = l_Lean_Environment_header(v_env_593_);
lean_dec_ref(v_env_593_);
v___x_619_ = l_Lean_EnvironmentHeader_moduleNames(v___x_618_);
v_mod_620_ = lean_array_get(v___x_591_, v___x_619_, v_val_614_);
lean_dec(v_val_614_);
lean_dec_ref(v___x_619_);
v___x_621_ = l_Lean_isPrivateName(v_declHint_588_);
lean_dec(v_declHint_588_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_622_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5);
v___x_623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v_c_605_);
v___x_624_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l_Lean_MessageData_ofName(v_mod_620_);
v___x_627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_625_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9);
v___x_629_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = l_Lean_MessageData_note(v___x_629_);
v___x_631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_631_, 0, v_msg_587_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 0);
lean_ctor_set(v___x_616_, 0, v___x_631_);
v___x_633_ = v___x_616_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v___x_631_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_646_; 
v___x_635_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_636_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
lean_ctor_set(v___x_636_, 1, v_c_605_);
v___x_637_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11);
v___x_638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_636_);
lean_ctor_set(v___x_638_, 1, v___x_637_);
v___x_639_ = l_Lean_MessageData_ofName(v_mod_620_);
v___x_640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_638_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13);
v___x_642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_640_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = l_Lean_MessageData_note(v___x_642_);
v___x_644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_644_, 0, v_msg_587_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
if (v_isShared_617_ == 0)
{
lean_ctor_set_tag(v___x_616_, 0);
lean_ctor_set(v___x_616_, 0, v___x_644_);
v___x_646_ = v___x_616_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_649_; 
lean_dec_ref(v_env_593_);
lean_dec(v_declHint_588_);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v_msg_587_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___boxed(lean_object* v_msg_650_, lean_object* v_declHint_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_650_, v_declHint_651_, v___y_652_);
lean_dec(v___y_652_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(lean_object* v_msg_655_, lean_object* v_declHint_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_670_; 
v___x_660_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_655_, v_declHint_656_, v___y_658_);
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_670_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_670_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
v___x_665_ = l_Lean_unknownIdentifierMessageTag;
v___x_666_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v_a_661_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_666_);
v___x_668_ = v___x_663_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15___boxed(lean_object* v_msg_671_, lean_object* v_declHint_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(v_msg_671_, v_declHint_672_, v___y_673_, v___y_674_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
return v_res_676_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(lean_object* v_opts_677_, lean_object* v_opt_678_){
_start:
{
lean_object* v_name_679_; lean_object* v_defValue_680_; lean_object* v_map_681_; lean_object* v___x_682_; 
v_name_679_ = lean_ctor_get(v_opt_678_, 0);
v_defValue_680_ = lean_ctor_get(v_opt_678_, 1);
v_map_681_ = lean_ctor_get(v_opts_677_, 0);
v___x_682_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_681_, v_name_679_);
if (lean_obj_tag(v___x_682_) == 0)
{
uint8_t v___x_683_; 
v___x_683_ = lean_unbox(v_defValue_680_);
return v___x_683_;
}
else
{
lean_object* v_val_684_; 
v_val_684_ = lean_ctor_get(v___x_682_, 0);
lean_inc(v_val_684_);
lean_dec_ref_known(v___x_682_, 1);
if (lean_obj_tag(v_val_684_) == 1)
{
uint8_t v_v_685_; 
v_v_685_ = lean_ctor_get_uint8(v_val_684_, 0);
lean_dec_ref_known(v_val_684_, 0);
return v_v_685_;
}
else
{
uint8_t v___x_686_; 
lean_dec(v_val_684_);
v___x_686_ = lean_unbox(v_defValue_680_);
return v___x_686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21___boxed(lean_object* v_opts_687_, lean_object* v_opt_688_){
_start:
{
uint8_t v_res_689_; lean_object* v_r_690_; 
v_res_689_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(v_opts_687_, v_opt_688_);
lean_dec_ref(v_opt_688_);
lean_dec_ref(v_opts_687_);
v_r_690_ = lean_box(v_res_689_);
return v_r_690_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0(void){
_start:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = lean_box(1);
v___x_692_ = l_Lean_MessageData_ofFormat(v___x_691_);
return v___x_692_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__2));
v___x_697_ = l_Lean_MessageData_ofFormat(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object* v_x_698_, lean_object* v_x_699_){
_start:
{
if (lean_obj_tag(v_x_699_) == 0)
{
return v_x_698_;
}
else
{
lean_object* v_head_700_; lean_object* v_tail_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_723_; 
v_head_700_ = lean_ctor_get(v_x_699_, 0);
v_tail_701_ = lean_ctor_get(v_x_699_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_x_699_);
if (v_isSharedCheck_723_ == 0)
{
v___x_703_ = v_x_699_;
v_isShared_704_ = v_isSharedCheck_723_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_tail_701_);
lean_inc(v_head_700_);
lean_dec(v_x_699_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_723_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_before_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_721_; 
v_before_705_ = lean_ctor_get(v_head_700_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v_head_700_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v_head_700_, 1);
lean_dec(v_unused_722_);
v___x_707_ = v_head_700_;
v_isShared_708_ = v_isSharedCheck_721_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_before_705_);
lean_dec(v_head_700_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_721_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0);
if (v_isShared_708_ == 0)
{
lean_ctor_set_tag(v___x_707_, 7);
lean_ctor_set(v___x_707_, 1, v___x_709_);
lean_ctor_set(v___x_707_, 0, v_x_698_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_x_698_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_709_);
v___x_711_ = v_reuseFailAlloc_720_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3);
if (v_isShared_704_ == 0)
{
lean_ctor_set_tag(v___x_703_, 7);
lean_ctor_set(v___x_703_, 1, v___x_712_);
lean_ctor_set(v___x_703_, 0, v___x_711_);
v___x_714_ = v___x_703_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_719_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; 
v___x_715_ = l_Lean_MessageData_ofSyntax(v_before_705_);
v___x_716_ = l_Lean_indentD(v___x_715_);
v___x_717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_714_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
v_x_698_ = v___x_717_;
v_x_699_ = v_tail_701_;
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
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__1));
v___x_728_ = l_Lean_MessageData_ofFormat(v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(lean_object* v_msgData_729_, lean_object* v_macroStack_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_scopes_735_; lean_object* v___x_736_; lean_object* v_opts_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_733_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_734_ = lean_st_ref_get(v___y_731_);
v_scopes_735_ = lean_ctor_get(v___x_734_, 2);
lean_inc(v_scopes_735_);
lean_dec(v___x_734_);
v___x_736_ = l_List_head_x21___redArg(v___x_733_, v_scopes_735_);
lean_dec(v_scopes_735_);
v_opts_737_ = lean_ctor_get(v___x_736_, 1);
lean_inc_ref(v_opts_737_);
lean_dec(v___x_736_);
v___x_738_ = l_Lean_Elab_pp_macroStack;
v___x_739_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(v_opts_737_, v___x_738_);
lean_dec_ref(v_opts_737_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v_macroStack_730_);
v___x_740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_740_, 0, v_msgData_729_);
return v___x_740_;
}
else
{
if (lean_obj_tag(v_macroStack_730_) == 0)
{
lean_object* v___x_741_; 
v___x_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_741_, 0, v_msgData_729_);
return v___x_741_;
}
else
{
lean_object* v_head_742_; lean_object* v_after_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_758_; 
v_head_742_ = lean_ctor_get(v_macroStack_730_, 0);
lean_inc(v_head_742_);
v_after_743_ = lean_ctor_get(v_head_742_, 1);
v_isSharedCheck_758_ = !lean_is_exclusive(v_head_742_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v_head_742_, 0);
lean_dec(v_unused_759_);
v___x_745_ = v_head_742_;
v_isShared_746_ = v_isSharedCheck_758_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_after_743_);
lean_dec(v_head_742_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_758_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_747_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0);
if (v_isShared_746_ == 0)
{
lean_ctor_set_tag(v___x_745_, 7);
lean_ctor_set(v___x_745_, 1, v___x_747_);
lean_ctor_set(v___x_745_, 0, v_msgData_729_);
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_msgData_729_);
lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_747_);
v___x_749_ = v_reuseFailAlloc_757_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v_msgData_754_; lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_750_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v___x_752_ = l_Lean_MessageData_ofSyntax(v_after_743_);
v___x_753_ = l_Lean_indentD(v___x_752_);
v_msgData_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_754_, 0, v___x_751_);
lean_ctor_set(v_msgData_754_, 1, v___x_753_);
v___x_755_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22(v_msgData_754_, v_macroStack_730_);
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
return v___x_756_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_msgData_760_, lean_object* v_macroStack_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v_res_764_; 
v_res_764_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_msgData_760_, v_macroStack_761_, v___y_762_);
lean_dec(v___y_762_);
return v_res_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(lean_object* v_msgData_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; lean_object* v_env_769_; uint8_t v___x_770_; lean_object* v_env_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v_scopes_774_; lean_object* v___x_775_; lean_object* v_opts_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; 
v___x_768_ = lean_st_ref_get(v___y_766_);
v_env_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc_ref(v_env_769_);
lean_dec(v___x_768_);
v___x_770_ = 0;
v_env_771_ = l_Lean_Environment_setRecordingDeps(v_env_769_, v___x_770_);
v___x_772_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_773_ = lean_st_ref_get(v___y_766_);
v_scopes_774_ = lean_ctor_get(v___x_773_, 2);
lean_inc(v_scopes_774_);
lean_dec(v___x_773_);
v___x_775_ = l_List_head_x21___redArg(v___x_772_, v_scopes_774_);
lean_dec(v_scopes_774_);
v_opts_776_ = lean_ctor_get(v___x_775_, 1);
lean_inc_ref(v_opts_776_);
lean_dec(v___x_775_);
v___x_777_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_778_ = lean_unsigned_to_nat(32u);
v___x_779_ = lean_mk_empty_array_with_capacity(v___x_778_);
lean_dec_ref(v___x_779_);
v___x_780_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
v___x_781_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_781_, 0, v_env_771_);
lean_ctor_set(v___x_781_, 1, v___x_777_);
lean_ctor_set(v___x_781_, 2, v___x_780_);
lean_ctor_set(v___x_781_, 3, v_opts_776_);
v___x_782_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
lean_ctor_set(v___x_782_, 1, v_msgData_765_);
v___x_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg___boxed(lean_object* v_msgData_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msgData_784_, v___y_785_);
lean_dec(v___y_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(lean_object* v_msg_788_, lean_object* v___y_789_, lean_object* v___y_790_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l_Lean_Elab_Command_getRef___redArg(v___y_789_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v_macroStack_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v_a_797_; lean_object* v___x_798_; lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_807_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v_macroStack_794_ = lean_ctor_get(v___y_789_, 4);
v___x_795_ = l_Lean_Elab_getBetterRef(v_a_793_, v_macroStack_794_);
lean_dec(v_a_793_);
v___x_796_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msg_788_, v___y_790_);
v_a_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_a_797_);
lean_dec_ref(v___x_796_);
lean_inc(v_macroStack_794_);
v___x_798_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_a_797_, v_macroStack_794_, v___y_790_);
v_a_799_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_807_ == 0)
{
v___x_801_ = v___x_798_;
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_798_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_807_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_795_);
lean_ctor_set(v___x_803_, 1, v_a_799_);
if (v_isShared_802_ == 0)
{
lean_ctor_set_tag(v___x_801_, 1);
lean_ctor_set(v___x_801_, 0, v___x_803_);
v___x_805_ = v___x_801_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_803_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec_ref(v_msg_788_);
v_a_808_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_792_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_792_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_msg_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_res_820_; 
v_res_820_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_816_, v___y_817_, v___y_818_);
lean_dec(v___y_818_);
lean_dec_ref(v___y_817_);
return v_res_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(lean_object* v_ref_821_, lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Elab_Command_getRef___redArg(v___y_823_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v_fileName_828_; lean_object* v_fileMap_829_; lean_object* v_currRecDepth_830_; lean_object* v_cmdPos_831_; lean_object* v_macroStack_832_; lean_object* v_quotContext_x3f_833_; lean_object* v_currMacroScope_834_; lean_object* v_snap_x3f_835_; lean_object* v_cancelTk_x3f_836_; uint8_t v_suppressElabErrors_837_; lean_object* v_ref_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
v_fileName_828_ = lean_ctor_get(v___y_823_, 0);
v_fileMap_829_ = lean_ctor_get(v___y_823_, 1);
v_currRecDepth_830_ = lean_ctor_get(v___y_823_, 2);
v_cmdPos_831_ = lean_ctor_get(v___y_823_, 3);
v_macroStack_832_ = lean_ctor_get(v___y_823_, 4);
v_quotContext_x3f_833_ = lean_ctor_get(v___y_823_, 5);
v_currMacroScope_834_ = lean_ctor_get(v___y_823_, 6);
v_snap_x3f_835_ = lean_ctor_get(v___y_823_, 8);
v_cancelTk_x3f_836_ = lean_ctor_get(v___y_823_, 9);
v_suppressElabErrors_837_ = lean_ctor_get_uint8(v___y_823_, sizeof(void*)*10);
v_ref_838_ = l_Lean_replaceRef(v_ref_821_, v_a_827_);
lean_dec(v_a_827_);
lean_inc(v_cancelTk_x3f_836_);
lean_inc(v_snap_x3f_835_);
lean_inc(v_currMacroScope_834_);
lean_inc(v_quotContext_x3f_833_);
lean_inc(v_macroStack_832_);
lean_inc(v_cmdPos_831_);
lean_inc(v_currRecDepth_830_);
lean_inc_ref(v_fileMap_829_);
lean_inc_ref(v_fileName_828_);
v___x_839_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_839_, 0, v_fileName_828_);
lean_ctor_set(v___x_839_, 1, v_fileMap_829_);
lean_ctor_set(v___x_839_, 2, v_currRecDepth_830_);
lean_ctor_set(v___x_839_, 3, v_cmdPos_831_);
lean_ctor_set(v___x_839_, 4, v_macroStack_832_);
lean_ctor_set(v___x_839_, 5, v_quotContext_x3f_833_);
lean_ctor_set(v___x_839_, 6, v_currMacroScope_834_);
lean_ctor_set(v___x_839_, 7, v_ref_838_);
lean_ctor_set(v___x_839_, 8, v_snap_x3f_835_);
lean_ctor_set(v___x_839_, 9, v_cancelTk_x3f_836_);
lean_ctor_set_uint8(v___x_839_, sizeof(void*)*10, v_suppressElabErrors_837_);
v___x_840_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_822_, v___x_839_, v___y_824_);
lean_dec_ref_known(v___x_839_, 10);
return v___x_840_;
}
else
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_848_; 
lean_dec_ref(v_msg_822_);
v_a_841_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_848_ == 0)
{
v___x_843_ = v___x_826_;
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_826_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_848_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_846_; 
if (v_isShared_844_ == 0)
{
v___x_846_ = v___x_843_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_a_841_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg___boxed(lean_object* v_ref_849_, lean_object* v_msg_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_849_, v_msg_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
lean_dec(v_ref_849_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(lean_object* v_ref_855_, lean_object* v_msg_856_, lean_object* v_declHint_857_, lean_object* v___y_858_, lean_object* v___y_859_){
_start:
{
lean_object* v___x_861_; lean_object* v_a_862_; lean_object* v___x_863_; 
v___x_861_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(v_msg_856_, v_declHint_857_, v___y_858_, v___y_859_);
v_a_862_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v___x_861_);
v___x_863_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_855_, v_a_862_, v___y_858_, v___y_859_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg___boxed(lean_object* v_ref_864_, lean_object* v_msg_865_, lean_object* v_declHint_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_864_, v_msg_865_, v_declHint_866_, v___y_867_, v___y_868_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v_ref_864_);
return v_res_870_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__0));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__2));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(lean_object* v_ref_877_, lean_object* v_constName_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
lean_object* v___x_882_; uint8_t v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_882_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1);
v___x_883_ = 0;
lean_inc(v_constName_878_);
v___x_884_ = l_Lean_MessageData_ofConstName(v_constName_878_, v___x_883_);
v___x_885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_882_);
lean_ctor_set(v___x_885_, 1, v___x_884_);
v___x_886_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3);
v___x_887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_885_);
lean_ctor_set(v___x_887_, 1, v___x_886_);
v___x_888_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_877_, v___x_887_, v_constName_878_, v___y_879_, v___y_880_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_ref_889_, lean_object* v_constName_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v_res_894_; 
v_res_894_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_ref_889_, v_constName_890_, v___y_891_, v___y_892_);
lean_dec(v___y_892_);
lean_dec_ref(v___y_891_);
lean_dec(v_ref_889_);
return v_res_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(lean_object* v_constName_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Lean_Elab_Command_getRef___redArg(v___y_896_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_a_900_, v_constName_895_, v___y_896_, v___y_897_);
lean_dec(v_a_900_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec(v_constName_895_);
v_a_902_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_899_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_899_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_constName_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_910_, v___y_911_, v___y_912_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(lean_object* v_constName_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v___x_919_; lean_object* v_env_920_; uint8_t v___x_921_; lean_object* v___x_922_; 
v___x_919_ = lean_st_ref_get(v___y_917_);
v_env_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc_ref(v_env_920_);
lean_dec(v___x_919_);
v___x_921_ = 0;
lean_inc(v_constName_915_);
v___x_922_ = l_Lean_Environment_findConstVal_x3f(v_env_920_, v_constName_915_, v___x_921_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v___x_923_; 
v___x_923_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_915_, v___y_916_, v___y_917_);
return v___x_923_;
}
else
{
lean_object* v_val_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_constName_915_);
v_val_924_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_922_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_val_924_);
lean_dec(v___x_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set_tag(v___x_926_, 0);
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_val_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6___boxed(lean_object* v_constName_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(v_constName_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(lean_object* v_constName_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v___x_941_; 
lean_inc(v_constName_937_);
v___x_941_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(v_constName_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_953_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_953_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_953_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v_levelParams_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
v_levelParams_946_ = lean_ctor_get(v_a_942_, 1);
lean_inc(v_levelParams_946_);
lean_dec(v_a_942_);
v___x_947_ = lean_box(0);
v___x_948_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__7(v_levelParams_946_, v___x_947_);
v___x_949_ = l_Lean_mkConst(v_constName_937_, v___x_948_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_949_);
v___x_951_ = v___x_944_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_constName_937_);
v_a_954_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_941_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_941_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5___boxed(lean_object* v_constName_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(v_constName_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(lean_object* v_t_967_, lean_object* v___y_968_){
_start:
{
lean_object* v___x_970_; lean_object* v_infoState_971_; uint8_t v_enabled_972_; 
v___x_970_ = lean_st_ref_get(v___y_968_);
v_infoState_971_ = lean_ctor_get(v___x_970_, 8);
lean_inc_ref(v_infoState_971_);
lean_dec(v___x_970_);
v_enabled_972_ = lean_ctor_get_uint8(v_infoState_971_, sizeof(void*)*3);
lean_dec_ref(v_infoState_971_);
if (v_enabled_972_ == 0)
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec_ref(v_t_967_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v_infoState_976_; lean_object* v_env_977_; lean_object* v_messages_978_; lean_object* v_scopes_979_; lean_object* v_usedQuotCtxts_980_; lean_object* v_nextMacroScope_981_; lean_object* v_maxRecDepth_982_; lean_object* v_ngen_983_; lean_object* v_auxDeclNGen_984_; lean_object* v_traceState_985_; lean_object* v_snapshotTasks_986_; lean_object* v_prevLinterStates_987_; lean_object* v_codeQualityEntryTasks_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_1010_; 
v___x_975_ = lean_st_ref_take(v___y_968_);
v_infoState_976_ = lean_ctor_get(v___x_975_, 8);
v_env_977_ = lean_ctor_get(v___x_975_, 0);
v_messages_978_ = lean_ctor_get(v___x_975_, 1);
v_scopes_979_ = lean_ctor_get(v___x_975_, 2);
v_usedQuotCtxts_980_ = lean_ctor_get(v___x_975_, 3);
v_nextMacroScope_981_ = lean_ctor_get(v___x_975_, 4);
v_maxRecDepth_982_ = lean_ctor_get(v___x_975_, 5);
v_ngen_983_ = lean_ctor_get(v___x_975_, 6);
v_auxDeclNGen_984_ = lean_ctor_get(v___x_975_, 7);
v_traceState_985_ = lean_ctor_get(v___x_975_, 9);
v_snapshotTasks_986_ = lean_ctor_get(v___x_975_, 10);
v_prevLinterStates_987_ = lean_ctor_get(v___x_975_, 11);
v_codeQualityEntryTasks_988_ = lean_ctor_get(v___x_975_, 12);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_990_ = v___x_975_;
v_isShared_991_ = v_isSharedCheck_1010_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_codeQualityEntryTasks_988_);
lean_inc(v_prevLinterStates_987_);
lean_inc(v_snapshotTasks_986_);
lean_inc(v_traceState_985_);
lean_inc(v_infoState_976_);
lean_inc(v_auxDeclNGen_984_);
lean_inc(v_ngen_983_);
lean_inc(v_maxRecDepth_982_);
lean_inc(v_nextMacroScope_981_);
lean_inc(v_usedQuotCtxts_980_);
lean_inc(v_scopes_979_);
lean_inc(v_messages_978_);
lean_inc(v_env_977_);
lean_dec(v___x_975_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_1010_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
uint8_t v_enabled_992_; lean_object* v_assignment_993_; lean_object* v_lazyAssignment_994_; lean_object* v_trees_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1009_; 
v_enabled_992_ = lean_ctor_get_uint8(v_infoState_976_, sizeof(void*)*3);
v_assignment_993_ = lean_ctor_get(v_infoState_976_, 0);
v_lazyAssignment_994_ = lean_ctor_get(v_infoState_976_, 1);
v_trees_995_ = lean_ctor_get(v_infoState_976_, 2);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_infoState_976_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_997_ = v_infoState_976_;
v_isShared_998_ = v_isSharedCheck_1009_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_trees_995_);
lean_inc(v_lazyAssignment_994_);
lean_inc(v_assignment_993_);
lean_dec(v_infoState_976_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1009_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_999_ = lean_box(0);
v___x_1000_ = l_Lean_PersistentArray_push___redArg(v_trees_995_, v_t_967_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 2, v___x_1000_);
v___x_1002_ = v___x_997_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_assignment_993_);
lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_lazyAssignment_994_);
lean_ctor_set(v_reuseFailAlloc_1008_, 2, v___x_1000_);
lean_ctor_set_uint8(v_reuseFailAlloc_1008_, sizeof(void*)*3, v_enabled_992_);
v___x_1002_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
lean_object* v___x_1004_; 
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 8, v___x_1002_);
v___x_1004_ = v___x_990_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_env_977_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_messages_978_);
lean_ctor_set(v_reuseFailAlloc_1007_, 2, v_scopes_979_);
lean_ctor_set(v_reuseFailAlloc_1007_, 3, v_usedQuotCtxts_980_);
lean_ctor_set(v_reuseFailAlloc_1007_, 4, v_nextMacroScope_981_);
lean_ctor_set(v_reuseFailAlloc_1007_, 5, v_maxRecDepth_982_);
lean_ctor_set(v_reuseFailAlloc_1007_, 6, v_ngen_983_);
lean_ctor_set(v_reuseFailAlloc_1007_, 7, v_auxDeclNGen_984_);
lean_ctor_set(v_reuseFailAlloc_1007_, 8, v___x_1002_);
lean_ctor_set(v_reuseFailAlloc_1007_, 9, v_traceState_985_);
lean_ctor_set(v_reuseFailAlloc_1007_, 10, v_snapshotTasks_986_);
lean_ctor_set(v_reuseFailAlloc_1007_, 11, v_prevLinterStates_987_);
lean_ctor_set(v_reuseFailAlloc_1007_, 12, v_codeQualityEntryTasks_988_);
v___x_1004_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_st_ref_put(v___y_968_, v___x_1004_);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_999_);
return v___x_1006_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_t_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v_t_1011_, v___y_1012_);
lean_dec(v___y_1012_);
return v_res_1014_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_unsigned_to_nat(32u);
v___x_1016_ = lean_mk_empty_array_with_capacity(v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1(void){
_start:
{
size_t v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1018_ = ((size_t)5ULL);
v___x_1019_ = lean_unsigned_to_nat(0u);
v___x_1020_ = lean_unsigned_to_nat(32u);
v___x_1021_ = lean_mk_empty_array_with_capacity(v___x_1020_);
v___x_1022_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0);
v___x_1023_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
lean_ctor_set(v___x_1023_, 1, v___x_1021_);
lean_ctor_set(v___x_1023_, 2, v___x_1019_);
lean_ctor_set(v___x_1023_, 3, v___x_1019_);
lean_ctor_set_usize(v___x_1023_, 4, v___x_1018_);
return v___x_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(lean_object* v_t_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v_infoState_1029_; uint8_t v_enabled_1030_; 
v___x_1028_ = lean_st_ref_get(v___y_1026_);
v_infoState_1029_ = lean_ctor_get(v___x_1028_, 8);
lean_inc_ref(v_infoState_1029_);
lean_dec(v___x_1028_);
v_enabled_1030_ = lean_ctor_get_uint8(v_infoState_1029_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1029_);
if (v_enabled_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
lean_dec_ref(v_t_1024_);
v___x_1031_ = lean_box(0);
v___x_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
else
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1033_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1);
v___x_1034_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1034_, 0, v_t_1024_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
v___x_1035_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v___x_1034_, v___y_1026_);
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___boxed(lean_object* v_t_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(v_t_1036_, v___y_1037_, v___y_1038_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(lean_object* v_stx_1041_, lean_object* v_n_1042_, lean_object* v_expectedType_x3f_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(v_n_1042_, v___y_1044_, v___y_1045_);
if (lean_obj_tag(v___x_1047_) == 0)
{
lean_object* v_a_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
lean_inc(v_a_1048_);
lean_dec_ref_known(v___x_1047_, 1);
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1049_);
lean_ctor_set(v___x_1050_, 1, v_stx_1041_);
v___x_1051_ = l_Lean_LocalContext_empty;
v___x_1052_ = 0;
v___x_1053_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1053_, 0, v___x_1050_);
lean_ctor_set(v___x_1053_, 1, v___x_1051_);
lean_ctor_set(v___x_1053_, 2, v_expectedType_x3f_1043_);
lean_ctor_set(v___x_1053_, 3, v_a_1048_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*4, v___x_1052_);
lean_ctor_set_uint8(v___x_1053_, sizeof(void*)*4 + 1, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
v___x_1055_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(v___x_1054_, v___y_1044_, v___y_1045_);
return v___x_1055_;
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_dec(v_expectedType_x3f_1043_);
lean_dec(v_stx_1041_);
v_a_1056_ = lean_ctor_get(v___x_1047_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_1047_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_1047_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_1047_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3___boxed(lean_object* v_stx_1064_, lean_object* v_n_1065_, lean_object* v_expectedType_x3f_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v_res_1070_; 
v_res_1070_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(v_stx_1064_, v_n_1065_, v_expectedType_x3f_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
return v_res_1070_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = ((lean_object*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__0));
v___x_1073_ = l_Lean_stringToMessageData(v___x_1072_);
return v___x_1073_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__2));
v___x_1076_ = l_Lean_stringToMessageData(v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1(lean_object* v_declName_1077_, lean_object* v_docString_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___y_1083_; lean_object* v___x_1110_; lean_object* v_env_1111_; lean_object* v___x_1112_; 
v___x_1110_ = lean_st_ref_get(v___y_1080_);
v_env_1111_ = lean_ctor_get(v___x_1110_, 0);
lean_inc_ref(v_env_1111_);
lean_dec(v___x_1110_);
v___x_1112_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1111_, v_declName_1077_);
lean_dec_ref(v_env_1111_);
if (lean_obj_tag(v___x_1112_) == 0)
{
v___y_1083_ = v___y_1080_;
goto v___jp_1082_;
}
else
{
uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_dec_ref_known(v___x_1112_, 1);
lean_dec_ref(v_docString_1078_);
v___x_1113_ = 0;
v___x_1114_ = lean_obj_once(&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1, &l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1_once, _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1);
v___x_1115_ = l_Lean_MessageData_ofConstName(v_declName_1077_, v___x_1113_);
v___x_1116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1114_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = lean_obj_once(&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3, &l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3_once, _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3);
v___x_1118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1116_);
lean_ctor_set(v___x_1118_, 1, v___x_1117_);
v___x_1119_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v___x_1118_, v___y_1079_, v___y_1080_);
return v___x_1119_;
}
v___jp_1082_:
{
lean_object* v___x_1084_; lean_object* v_env_1085_; lean_object* v_nextMacroScope_1086_; lean_object* v_ngen_1087_; lean_object* v_auxDeclNGen_1088_; lean_object* v_traceState_1089_; lean_object* v_recordedDeps_1090_; lean_object* v_messages_1091_; lean_object* v_infoState_1092_; lean_object* v_snapshotTasks_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1108_; 
v___x_1084_ = lean_st_ref_take(v___y_1083_);
v_env_1085_ = lean_ctor_get(v___x_1084_, 0);
v_nextMacroScope_1086_ = lean_ctor_get(v___x_1084_, 1);
v_ngen_1087_ = lean_ctor_get(v___x_1084_, 2);
v_auxDeclNGen_1088_ = lean_ctor_get(v___x_1084_, 3);
v_traceState_1089_ = lean_ctor_get(v___x_1084_, 4);
v_recordedDeps_1090_ = lean_ctor_get(v___x_1084_, 6);
v_messages_1091_ = lean_ctor_get(v___x_1084_, 7);
v_infoState_1092_ = lean_ctor_get(v___x_1084_, 8);
v_snapshotTasks_1093_ = lean_ctor_get(v___x_1084_, 9);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1108_ == 0)
{
lean_object* v_unused_1109_; 
v_unused_1109_ = lean_ctor_get(v___x_1084_, 5);
lean_dec(v_unused_1109_);
v___x_1095_ = v___x_1084_;
v_isShared_1096_ = v_isSharedCheck_1108_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_snapshotTasks_1093_);
lean_inc(v_infoState_1092_);
lean_inc(v_messages_1091_);
lean_inc(v_recordedDeps_1090_);
lean_inc(v_traceState_1089_);
lean_inc(v_auxDeclNGen_1088_);
lean_inc(v_ngen_1087_);
lean_inc(v_nextMacroScope_1086_);
lean_inc(v_env_1085_);
lean_dec(v___x_1084_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1108_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; uint8_t v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1104_; 
v___x_1097_ = lean_box(0);
v___x_1098_ = l_Lean_docStringExt;
v___x_1099_ = l_String_removeLeadingSpaces(v_docString_1078_);
v___x_1100_ = 1;
v___x_1101_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1098_, v_env_1085_, v_declName_1077_, v___x_1099_, v___x_1100_);
v___x_1102_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__1, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__1_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__1);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 5, v___x_1102_);
lean_ctor_set(v___x_1095_, 0, v___x_1101_);
v___x_1104_ = v___x_1095_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1101_);
lean_ctor_set(v_reuseFailAlloc_1107_, 1, v_nextMacroScope_1086_);
lean_ctor_set(v_reuseFailAlloc_1107_, 2, v_ngen_1087_);
lean_ctor_set(v_reuseFailAlloc_1107_, 3, v_auxDeclNGen_1088_);
lean_ctor_set(v_reuseFailAlloc_1107_, 4, v_traceState_1089_);
lean_ctor_set(v_reuseFailAlloc_1107_, 5, v___x_1102_);
lean_ctor_set(v_reuseFailAlloc_1107_, 6, v_recordedDeps_1090_);
lean_ctor_set(v_reuseFailAlloc_1107_, 7, v_messages_1091_);
lean_ctor_set(v_reuseFailAlloc_1107_, 8, v_infoState_1092_);
lean_ctor_set(v_reuseFailAlloc_1107_, 9, v_snapshotTasks_1093_);
v___x_1104_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_st_ref_put(v___y_1083_, v___x_1104_);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1097_);
return v___x_1106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___boxed(lean_object* v_declName_1120_, lean_object* v_docString_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1(v_declName_1120_, v_docString_1121_, v___y_1122_, v___y_1123_);
lean_dec(v___y_1123_);
lean_dec_ref(v___y_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(lean_object* v_stx_1126_, lean_object* v___y_1127_){
_start:
{
uint8_t v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = 0;
v___x_1130_ = l_Lean_Syntax_getRange_x3f(v_stx_1126_, v___x_1129_);
if (lean_obj_tag(v___x_1130_) == 1)
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1143_; 
v_val_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1143_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_fileMap_1135_; lean_object* v_start_1136_; lean_object* v_stop_1137_; lean_object* v___x_1138_; lean_object* v___x_1140_; 
v_fileMap_1135_ = lean_ctor_get(v___y_1127_, 1);
v_start_1136_ = lean_ctor_get(v_val_1131_, 0);
lean_inc(v_start_1136_);
v_stop_1137_ = lean_ctor_get(v_val_1131_, 1);
lean_inc(v_stop_1137_);
lean_dec(v_val_1131_);
lean_inc_ref(v_fileMap_1135_);
v___x_1138_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_1135_, v_start_1136_, v_stop_1137_);
lean_dec(v_stop_1137_);
lean_dec(v_start_1136_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1138_);
v___x_1140_ = v___x_1133_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1138_);
v___x_1140_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
else
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_dec(v___x_1130_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg___boxed(lean_object* v_stx_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_stx_1146_, v___y_1147_);
lean_dec_ref(v___y_1147_);
lean_dec(v_stx_1146_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(lean_object* v_declName_1150_, lean_object* v_declRanges_1151_, lean_object* v___y_1152_){
_start:
{
uint8_t v___x_1154_; 
v___x_1154_ = l_Lean_Name_isAnonymous(v_declName_1150_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v_env_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1155_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1156_ = lean_st_ref_get(v___y_1152_);
v_env_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc_ref(v_env_1157_);
lean_dec(v___x_1156_);
v___x_1158_ = l_Lean_declRangeExt;
v___x_1159_ = lean_box(1);
lean_inc(v_declName_1150_);
v___x_1160_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1155_, v___x_1158_, v_env_1157_, v_declName_1150_, v___x_1159_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; lean_object* v_env_1162_; lean_object* v_messages_1163_; lean_object* v_scopes_1164_; lean_object* v_usedQuotCtxts_1165_; lean_object* v_nextMacroScope_1166_; lean_object* v_maxRecDepth_1167_; lean_object* v_ngen_1168_; lean_object* v_auxDeclNGen_1169_; lean_object* v_infoState_1170_; lean_object* v_traceState_1171_; lean_object* v_snapshotTasks_1172_; lean_object* v_prevLinterStates_1173_; lean_object* v_codeQualityEntryTasks_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1185_; 
v___x_1161_ = lean_st_ref_take(v___y_1152_);
v_env_1162_ = lean_ctor_get(v___x_1161_, 0);
v_messages_1163_ = lean_ctor_get(v___x_1161_, 1);
v_scopes_1164_ = lean_ctor_get(v___x_1161_, 2);
v_usedQuotCtxts_1165_ = lean_ctor_get(v___x_1161_, 3);
v_nextMacroScope_1166_ = lean_ctor_get(v___x_1161_, 4);
v_maxRecDepth_1167_ = lean_ctor_get(v___x_1161_, 5);
v_ngen_1168_ = lean_ctor_get(v___x_1161_, 6);
v_auxDeclNGen_1169_ = lean_ctor_get(v___x_1161_, 7);
v_infoState_1170_ = lean_ctor_get(v___x_1161_, 8);
v_traceState_1171_ = lean_ctor_get(v___x_1161_, 9);
v_snapshotTasks_1172_ = lean_ctor_get(v___x_1161_, 10);
v_prevLinterStates_1173_ = lean_ctor_get(v___x_1161_, 11);
v_codeQualityEntryTasks_1174_ = lean_ctor_get(v___x_1161_, 12);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1176_ = v___x_1161_;
v_isShared_1177_ = v_isSharedCheck_1185_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1174_);
lean_inc(v_prevLinterStates_1173_);
lean_inc(v_snapshotTasks_1172_);
lean_inc(v_traceState_1171_);
lean_inc(v_infoState_1170_);
lean_inc(v_auxDeclNGen_1169_);
lean_inc(v_ngen_1168_);
lean_inc(v_maxRecDepth_1167_);
lean_inc(v_nextMacroScope_1166_);
lean_inc(v_usedQuotCtxts_1165_);
lean_inc(v_scopes_1164_);
lean_inc(v_messages_1163_);
lean_inc(v_env_1162_);
lean_dec(v___x_1161_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1185_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1181_; 
v___x_1178_ = lean_box(0);
v___x_1179_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1158_, v_env_1162_, v_declName_1150_, v_declRanges_1151_, v___x_1160_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v___x_1179_);
v___x_1181_ = v___x_1176_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1179_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_messages_1163_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v_scopes_1164_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_usedQuotCtxts_1165_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_nextMacroScope_1166_);
lean_ctor_set(v_reuseFailAlloc_1184_, 5, v_maxRecDepth_1167_);
lean_ctor_set(v_reuseFailAlloc_1184_, 6, v_ngen_1168_);
lean_ctor_set(v_reuseFailAlloc_1184_, 7, v_auxDeclNGen_1169_);
lean_ctor_set(v_reuseFailAlloc_1184_, 8, v_infoState_1170_);
lean_ctor_set(v_reuseFailAlloc_1184_, 9, v_traceState_1171_);
lean_ctor_set(v_reuseFailAlloc_1184_, 10, v_snapshotTasks_1172_);
lean_ctor_set(v_reuseFailAlloc_1184_, 11, v_prevLinterStates_1173_);
lean_ctor_set(v_reuseFailAlloc_1184_, 12, v_codeQualityEntryTasks_1174_);
v___x_1181_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___x_1182_ = lean_st_ref_put(v___y_1152_, v___x_1181_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1178_);
return v___x_1183_;
}
}
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec_ref(v_declRanges_1151_);
lean_dec(v_declName_1150_);
v___x_1186_ = lean_box(0);
v___x_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
return v___x_1187_;
}
}
else
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v_declRanges_1151_);
lean_dec(v_declName_1150_);
v___x_1188_ = lean_box(0);
v___x_1189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1188_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg___boxed(lean_object* v_declName_1190_, lean_object* v_declRanges_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1190_, v_declRanges_1191_, v___y_1192_);
lean_dec(v___y_1192_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(lean_object* v_declName_1195_, lean_object* v_rangeStx_1196_, lean_object* v_selectionRangeStx_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1218_; 
v___x_1201_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_rangeStx_1196_, v___y_1198_);
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1204_ = v___x_1201_;
v_isShared_1205_ = v_isSharedCheck_1218_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1201_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1218_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
if (lean_obj_tag(v_a_1202_) == 1)
{
lean_object* v_val_1206_; lean_object* v_a_1208_; lean_object* v___x_1211_; lean_object* v_a_1212_; 
lean_del_object(v___x_1204_);
v_val_1206_ = lean_ctor_get(v_a_1202_, 0);
lean_inc(v_val_1206_);
lean_dec_ref_known(v_a_1202_, 1);
v___x_1211_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_selectionRangeStx_1197_, v___y_1198_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v___x_1211_);
if (lean_obj_tag(v_a_1212_) == 0)
{
lean_inc(v_val_1206_);
v_a_1208_ = v_val_1206_;
goto v___jp_1207_;
}
else
{
lean_object* v_val_1213_; 
v_val_1213_ = lean_ctor_get(v_a_1212_, 0);
lean_inc(v_val_1213_);
lean_dec_ref_known(v_a_1212_, 1);
v_a_1208_ = v_val_1213_;
goto v___jp_1207_;
}
v___jp_1207_:
{
lean_object* v___x_1209_; lean_object* v___x_1210_; 
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v_val_1206_);
lean_ctor_set(v___x_1209_, 1, v_a_1208_);
v___x_1210_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1195_, v___x_1209_, v___y_1199_);
return v___x_1210_;
}
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
lean_dec(v_a_1202_);
lean_dec(v_declName_1195_);
v___x_1214_ = lean_box(0);
if (v_isShared_1205_ == 0)
{
lean_ctor_set(v___x_1204_, 0, v___x_1214_);
v___x_1216_ = v___x_1204_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2___boxed(lean_object* v_declName_1219_, lean_object* v_rangeStx_1220_, lean_object* v_selectionRangeStx_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(v_declName_1219_, v_rangeStx_1220_, v_selectionRangeStx_1221_, v___y_1222_, v___y_1223_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v_selectionRangeStx_1221_);
lean_dec(v_rangeStx_1220_);
return v_res_1225_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_box(0);
v___x_1233_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2));
v___x_1234_ = l_Lean_mkConst(v___x_1233_, v___x_1232_);
return v___x_1234_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5));
v___x_1242_ = l_Lean_mkConst(v___x_1241_, v___x_1240_);
return v___x_1242_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6);
v___x_1244_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3);
v___x_1245_ = l_Lean_Expr_app___override(v___x_1244_, v___x_1243_);
return v___x_1245_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9));
v___x_1253_ = l_Lean_mkConst(v___x_1252_, v___x_1251_);
return v___x_1253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs(lean_object* v_x_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v___x_1263_; uint8_t v___x_1264_; 
v___x_1263_ = ((lean_object*)(l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3));
lean_inc(v_x_1259_);
v___x_1264_ = l_Lean_Syntax_isOfKind(v_x_1259_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec(v_x_1259_);
v___x_1265_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_1265_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v_id_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_env_1273_; lean_object* v___x_1274_; 
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_unsigned_to_nat(1u);
v_id_1268_ = l_Lean_Syntax_getArg(v_x_1259_, v___x_1267_);
v___x_1269_ = lean_unsigned_to_nat(3u);
v___x_1270_ = l_Lean_Syntax_getArg(v_x_1259_, v___x_1269_);
lean_dec(v_x_1259_);
v___x_1271_ = lean_box(0);
v___x_1272_ = lean_st_ref_get(v_a_1261_);
v_env_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc_ref(v_env_1273_);
lean_dec(v___x_1272_);
v___x_1274_ = l_Lean_Elab_Command_getScope___redArg(v_a_1261_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v_currNamespace_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___y_1281_; lean_object* v___x_1284_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v_currNamespace_1276_ = lean_ctor_get(v_a_1275_, 2);
lean_inc(v_currNamespace_1276_);
lean_dec(v_a_1275_);
v___x_1277_ = l_Lean_TSyntax_getId(v_id_1268_);
lean_inc(v___x_1277_);
v___x_1278_ = l_Lean_Name_append(v_currNamespace_1276_, v___x_1277_);
v___x_1279_ = l_Lean_mkPrivateName(v_env_1273_, v___x_1278_);
lean_dec_ref(v_env_1273_);
v___x_1284_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_1270_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; lean_object* v___x_1286_; lean_object* v_env_1287_; lean_object* v_messages_1288_; lean_object* v_scopes_1289_; lean_object* v_usedQuotCtxts_1290_; lean_object* v_nextMacroScope_1291_; lean_object* v_maxRecDepth_1292_; lean_object* v_ngen_1293_; lean_object* v_auxDeclNGen_1294_; lean_object* v_infoState_1295_; lean_object* v_traceState_1296_; lean_object* v_snapshotTasks_1297_; lean_object* v_prevLinterStates_1298_; lean_object* v_codeQualityEntryTasks_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1372_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
v___x_1286_ = lean_st_ref_take(v_a_1261_);
v_env_1287_ = lean_ctor_get(v___x_1286_, 0);
v_messages_1288_ = lean_ctor_get(v___x_1286_, 1);
v_scopes_1289_ = lean_ctor_get(v___x_1286_, 2);
v_usedQuotCtxts_1290_ = lean_ctor_get(v___x_1286_, 3);
v_nextMacroScope_1291_ = lean_ctor_get(v___x_1286_, 4);
v_maxRecDepth_1292_ = lean_ctor_get(v___x_1286_, 5);
v_ngen_1293_ = lean_ctor_get(v___x_1286_, 6);
v_auxDeclNGen_1294_ = lean_ctor_get(v___x_1286_, 7);
v_infoState_1295_ = lean_ctor_get(v___x_1286_, 8);
v_traceState_1296_ = lean_ctor_get(v___x_1286_, 9);
v_snapshotTasks_1297_ = lean_ctor_get(v___x_1286_, 10);
v_prevLinterStates_1298_ = lean_ctor_get(v___x_1286_, 11);
v_codeQualityEntryTasks_1299_ = lean_ctor_get(v___x_1286_, 12);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1301_ = v___x_1286_;
v_isShared_1302_ = v_isSharedCheck_1372_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1299_);
lean_inc(v_prevLinterStates_1298_);
lean_inc(v_snapshotTasks_1297_);
lean_inc(v_traceState_1296_);
lean_inc(v_infoState_1295_);
lean_inc(v_auxDeclNGen_1294_);
lean_inc(v_ngen_1293_);
lean_inc(v_maxRecDepth_1292_);
lean_inc(v_nextMacroScope_1291_);
lean_inc(v_usedQuotCtxts_1290_);
lean_inc(v_scopes_1289_);
lean_inc(v_messages_1288_);
lean_inc(v_env_1287_);
lean_dec(v___x_1286_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1372_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___y_1304_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = lean_array_get_size(v_a_1285_);
v___x_1364_ = lean_nat_dec_lt(v___x_1266_, v___x_1363_);
if (v___x_1364_ == 0)
{
v___y_1304_ = v_messages_1288_;
goto v___jp_1303_;
}
else
{
uint8_t v___x_1365_; 
v___x_1365_ = lean_nat_dec_le(v___x_1363_, v___x_1363_);
if (v___x_1365_ == 0)
{
if (v___x_1364_ == 0)
{
v___y_1304_ = v_messages_1288_;
goto v___jp_1303_;
}
else
{
size_t v___x_1366_; size_t v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = ((size_t)0ULL);
v___x_1367_ = lean_usize_of_nat(v___x_1363_);
v___x_1368_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_a_1285_, v___x_1366_, v___x_1367_, v_messages_1288_);
v___y_1304_ = v___x_1368_;
goto v___jp_1303_;
}
}
else
{
size_t v___x_1369_; size_t v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = ((size_t)0ULL);
v___x_1370_ = lean_usize_of_nat(v___x_1363_);
v___x_1371_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_a_1285_, v___x_1369_, v___x_1370_, v_messages_1288_);
v___y_1304_ = v___x_1371_;
goto v___jp_1303_;
}
}
v___jp_1303_:
{
lean_object* v___x_1306_; 
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 1, v___y_1304_);
v___x_1306_ = v___x_1301_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_env_1287_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___y_1304_);
lean_ctor_set(v_reuseFailAlloc_1362_, 2, v_scopes_1289_);
lean_ctor_set(v_reuseFailAlloc_1362_, 3, v_usedQuotCtxts_1290_);
lean_ctor_set(v_reuseFailAlloc_1362_, 4, v_nextMacroScope_1291_);
lean_ctor_set(v_reuseFailAlloc_1362_, 5, v_maxRecDepth_1292_);
lean_ctor_set(v_reuseFailAlloc_1362_, 6, v_ngen_1293_);
lean_ctor_set(v_reuseFailAlloc_1362_, 7, v_auxDeclNGen_1294_);
lean_ctor_set(v_reuseFailAlloc_1362_, 8, v_infoState_1295_);
lean_ctor_set(v_reuseFailAlloc_1362_, 9, v_traceState_1296_);
lean_ctor_set(v_reuseFailAlloc_1362_, 10, v_snapshotTasks_1297_);
lean_ctor_set(v_reuseFailAlloc_1362_, 11, v_prevLinterStates_1298_);
lean_ctor_set(v_reuseFailAlloc_1362_, 12, v_codeQualityEntryTasks_1299_);
v___x_1306_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1307_ = lean_st_ref_put(v_a_1261_, v___x_1306_);
v___x_1308_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7);
lean_inc_n(v___x_1279_, 3);
v___x_1309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1309_, 0, v___x_1279_);
lean_ctor_set(v___x_1309_, 1, v___x_1271_);
lean_ctor_set(v___x_1309_, 2, v___x_1308_);
v___x_1310_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10);
v___x_1311_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v___x_1279_);
v___x_1312_ = l_Lean_Expr_app___override(v___x_1310_, v___x_1311_);
v___x_1313_ = lean_box(1);
v___x_1314_ = 1;
v___x_1315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1279_);
lean_ctor_set(v___x_1315_, 1, v___x_1271_);
v___x_1316_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1316_, 0, v___x_1309_);
lean_ctor_set(v___x_1316_, 1, v___x_1312_);
lean_ctor_set(v___x_1316_, 2, v___x_1313_);
lean_ctor_set(v___x_1316_, 3, v___x_1315_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*4, v___x_1314_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
v___x_1318_ = lean_box(v___x_1264_);
v___x_1319_ = lean_box(v___x_1264_);
v___x_1320_ = lean_alloc_closure((void*)(l_Lean_addAndCompile___boxed), 6, 3);
lean_closure_set(v___x_1320_, 0, v___x_1317_);
lean_closure_set(v___x_1320_, 1, v___x_1318_);
lean_closure_set(v___x_1320_, 2, v___x_1319_);
v___x_1321_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1320_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_fileName_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; 
lean_dec_ref_known(v___x_1321_, 1);
v_fileName_1322_ = lean_ctor_get(v_a_1260_, 0);
v___x_1323_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__11));
v___x_1324_ = lean_string_append(v___x_1323_, v_fileName_1322_);
v___x_1325_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__12));
v___x_1326_ = lean_string_append(v___x_1324_, v___x_1325_);
v___x_1327_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1277_, v___x_1264_);
v___x_1328_ = lean_string_append(v___x_1326_, v___x_1327_);
v___x_1329_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__13));
v___x_1330_ = lean_string_append(v___x_1328_, v___x_1329_);
v___x_1331_ = lean_string_append(v___x_1330_, v___x_1327_);
v___x_1332_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__14));
v___x_1333_ = lean_string_append(v___x_1331_, v___x_1332_);
v___x_1334_ = lean_string_append(v___x_1333_, v___x_1327_);
lean_dec_ref(v___x_1327_);
v___x_1335_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__15));
v___x_1336_ = lean_string_append(v___x_1334_, v___x_1335_);
lean_inc(v___x_1279_);
v___x_1337_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___boxed), 5, 2);
lean_closure_set(v___x_1337_, 0, v___x_1279_);
lean_closure_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1337_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref_known(v___x_1338_, 1);
v___x_1339_ = l_Lean_Elab_Command_getRef___redArg(v_a_1260_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
lean_inc(v___x_1279_);
v___x_1341_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(v___x_1279_, v_a_1340_, v_id_1268_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1340_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
lean_dec_ref_known(v___x_1341_, 1);
v___x_1342_ = lean_box(0);
lean_inc(v___x_1279_);
v___x_1343_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(v_id_1268_, v___x_1279_, v___x_1342_, v_a_1260_, v_a_1261_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
lean_dec_ref_known(v___x_1343_, 1);
v___x_1344_ = lean_array_get_size(v_a_1285_);
v___x_1345_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0));
v___x_1346_ = lean_nat_dec_lt(v___x_1266_, v___x_1344_);
if (v___x_1346_ == 0)
{
lean_dec(v_a_1285_);
v___y_1281_ = v___x_1345_;
goto v___jp_1280_;
}
else
{
uint8_t v___x_1347_; 
v___x_1347_ = lean_nat_dec_le(v___x_1344_, v___x_1344_);
if (v___x_1347_ == 0)
{
if (v___x_1346_ == 0)
{
lean_dec(v_a_1285_);
v___y_1281_ = v___x_1345_;
goto v___jp_1280_;
}
else
{
size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = lean_usize_of_nat(v___x_1344_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_a_1285_, v___x_1348_, v___x_1349_, v___x_1345_);
lean_dec(v_a_1285_);
v___y_1281_ = v___x_1350_;
goto v___jp_1280_;
}
}
else
{
size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1351_ = ((size_t)0ULL);
v___x_1352_ = lean_usize_of_nat(v___x_1344_);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_a_1285_, v___x_1351_, v___x_1352_, v___x_1345_);
lean_dec(v_a_1285_);
v___y_1281_ = v___x_1353_;
goto v___jp_1280_;
}
}
}
else
{
lean_dec(v_a_1285_);
lean_dec(v___x_1279_);
return v___x_1343_;
}
}
else
{
lean_dec(v_a_1285_);
lean_dec(v___x_1279_);
lean_dec(v_id_1268_);
return v___x_1341_;
}
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_a_1285_);
lean_dec(v___x_1279_);
lean_dec(v_id_1268_);
v_a_1354_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1339_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1339_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
else
{
lean_dec(v_a_1285_);
lean_dec(v___x_1279_);
lean_dec(v_id_1268_);
return v___x_1338_;
}
}
else
{
lean_dec(v_a_1285_);
lean_dec(v___x_1279_);
lean_dec(v___x_1277_);
lean_dec(v_id_1268_);
return v___x_1321_;
}
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_dec(v___x_1279_);
lean_dec(v___x_1277_);
lean_dec(v_id_1268_);
v_a_1373_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1284_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1284_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
v___jp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_storeTraces___boxed), 5, 2);
lean_closure_set(v___x_1282_, 0, v___x_1279_);
lean_closure_set(v___x_1282_, 1, v___y_1281_);
v___x_1283_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1282_, v_a_1260_, v_a_1261_);
return v___x_1283_;
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v_env_1273_);
lean_dec(v___x_1270_);
lean_dec(v_id_1268_);
v_a_1381_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1274_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1274_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___boxed(lean_object* v_x_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_Elab_PostprocessTraces_elabStoreTraceAs(v_x_1389_, v_a_1390_, v_a_1391_);
lean_dec(v_a_1391_);
lean_dec_ref(v_a_1390_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2(lean_object* v_stx_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_stx_1394_, v___y_1395_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___boxed(lean_object* v_stx_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2(v_stx_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v_stx_1399_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3(lean_object* v_declName_1404_, lean_object* v_declRanges_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1404_, v_declRanges_1405_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___boxed(lean_object* v_declName_1410_, lean_object* v_declRanges_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3(v_declName_1410_, v_declRanges_1411_, v___y_1412_, v___y_1413_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9(lean_object* v_t_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v_t_1416_, v___y_1418_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___boxed(lean_object* v_t_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9(v_t_1421_, v___y_1422_, v___y_1423_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9(lean_object* v_00_u03b1_1426_, lean_object* v_constName_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_1427_, v___y_1428_, v___y_1429_);
return v___x_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1432_, lean_object* v_constName_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9(v_00_u03b1_1432_, v_constName_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1438_, lean_object* v_ref_1439_, lean_object* v_constName_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_ref_1439_, v_constName_1440_, v___y_1441_, v___y_1442_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1445_, lean_object* v_ref_1446_, lean_object* v_constName_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12(v_00_u03b1_1445_, v_ref_1446_, v_constName_1447_, v___y_1448_, v___y_1449_);
lean_dec(v___y_1449_);
lean_dec_ref(v___y_1448_);
lean_dec(v_ref_1446_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14(lean_object* v_00_u03b1_1452_, lean_object* v_ref_1453_, lean_object* v_msg_1454_, lean_object* v_declHint_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_1453_, v_msg_1454_, v_declHint_1455_, v___y_1456_, v___y_1457_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___boxed(lean_object* v_00_u03b1_1460_, lean_object* v_ref_1461_, lean_object* v_msg_1462_, lean_object* v_declHint_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14(v_00_u03b1_1460_, v_ref_1461_, v_msg_1462_, v_declHint_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v_ref_1461_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16(lean_object* v_msg_1468_, lean_object* v_declHint_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_1468_, v_declHint_1469_, v___y_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___boxed(lean_object* v_msg_1474_, lean_object* v_declHint_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16(v_msg_1474_, v_declHint_1475_, v___y_1476_, v___y_1477_);
lean_dec(v___y_1477_);
lean_dec_ref(v___y_1476_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16(lean_object* v_00_u03b1_1480_, lean_object* v_ref_1481_, lean_object* v_msg_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_1481_, v_msg_1482_, v___y_1483_, v___y_1484_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1487_, lean_object* v_ref_1488_, lean_object* v_msg_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16(v_00_u03b1_1487_, v_ref_1488_, v_msg_1489_, v___y_1490_, v___y_1491_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v_ref_1488_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19(lean_object* v_msgData_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_){
_start:
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msgData_1494_, v___y_1496_);
return v___x_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___boxed(lean_object* v_msgData_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19(v_msgData_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1504_, lean_object* v_msg_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_1505_, v___y_1506_, v___y_1507_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1510_, lean_object* v_msg_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18(v_00_u03b1_1510_, v_msg_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20(lean_object* v_msgData_1516_, lean_object* v_macroStack_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_msgData_1516_, v_macroStack_1517_, v___y_1519_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___boxed(lean_object* v_msgData_1522_, lean_object* v_macroStack_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20(v_msgData_1522_, v_macroStack_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace_spec__0(lean_object* v_a_1528_, lean_object* v_a_1529_){
_start:
{
if (lean_obj_tag(v_a_1528_) == 0)
{
lean_object* v___x_1530_; 
v___x_1530_ = l_List_reverse___redArg(v_a_1529_);
return v___x_1530_;
}
else
{
lean_object* v_head_1531_; lean_object* v_tail_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1553_; 
v_head_1531_ = lean_ctor_get(v_a_1528_, 0);
v_tail_1532_ = lean_ctor_get(v_a_1528_, 1);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_a_1528_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1534_ = v_a_1528_;
v_isShared_1535_ = v_isSharedCheck_1553_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_tail_1532_);
lean_inc(v_head_1531_);
lean_dec(v_a_1528_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1553_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v_fst_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1551_; 
v_fst_1536_ = lean_ctor_get(v_head_1531_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v_head_1531_);
if (v_isSharedCheck_1551_ == 0)
{
lean_object* v_unused_1552_; 
v_unused_1552_ = lean_ctor_get(v_head_1531_, 1);
lean_dec(v_unused_1552_);
v___x_1538_ = v_head_1531_;
v_isShared_1539_ = v_isSharedCheck_1551_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_fst_1536_);
lean_dec(v_head_1531_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1551_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1540_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3);
v___x_1541_ = l_Lean_privateToUserName(v_fst_1536_);
v___x_1542_ = l_Lean_MessageData_ofName(v___x_1541_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set_tag(v___x_1538_, 7);
lean_ctor_set(v___x_1538_, 1, v___x_1542_);
lean_ctor_set(v___x_1538_, 0, v___x_1540_);
v___x_1544_ = v___x_1538_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1540_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
v___x_1545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v___x_1540_);
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 1, v_a_1529_);
lean_ctor_set(v___x_1534_, 0, v___x_1545_);
v___x_1547_ = v___x_1534_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v_a_1529_);
v___x_1547_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
v_a_1528_ = v_tail_1532_;
v_a_1529_ = v___x_1547_;
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
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__0));
v___x_1556_ = l_Lean_stringToMessageData(v___x_1555_);
return v___x_1556_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__2));
v___x_1559_ = l_Lean_stringToMessageData(v___x_1558_);
return v___x_1559_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1561_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__4));
v___x_1562_ = l_Lean_stringToMessageData(v___x_1561_);
return v___x_1562_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__6));
v___x_1565_ = l_Lean_stringToMessageData(v___x_1564_);
return v___x_1565_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__8));
v___x_1568_ = l_Lean_stringToMessageData(v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__11));
v___x_1573_ = l_Lean_MessageData_ofFormat(v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14(void){
_start:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__13));
v___x_1576_ = l_Lean_stringToMessageData(v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(lean_object* v_id_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = lean_box(0);
lean_inc(v_id_1577_);
v___x_1582_ = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed), 5, 2);
lean_closure_set(v___x_1582_, 0, v_id_1577_);
lean_closure_set(v___x_1582_, 1, v___x_1581_);
v___x_1583_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1582_, v_a_1578_, v_a_1579_);
if (lean_obj_tag(v___x_1583_) == 0)
{
lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1621_; 
v_a_1584_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1586_ = v___x_1583_;
v_isShared_1587_ = v_isSharedCheck_1621_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v___x_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1621_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v_env_1589_; lean_object* v___x_1590_; 
v___x_1588_ = lean_st_ref_get(v_a_1579_);
v_env_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc_ref(v_env_1589_);
lean_dec(v___x_1588_);
v___x_1590_ = l_Lean_PostprocessTraces_findStoredTrace_x3f(v_env_1589_, v_a_1584_);
lean_dec(v_a_1584_);
if (lean_obj_tag(v___x_1590_) == 1)
{
lean_object* v_val_1591_; lean_object* v___x_1593_; 
lean_dec(v_id_1577_);
v_val_1591_ = lean_ctor_get(v___x_1590_, 0);
lean_inc(v_val_1591_);
lean_dec_ref_known(v___x_1590_, 1);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v_val_1591_);
v___x_1593_ = v___x_1586_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_val_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
else
{
lean_object* v___x_1595_; lean_object* v___y_1597_; lean_object* v_env_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; uint8_t v___x_1615_; 
lean_dec(v___x_1590_);
lean_del_object(v___x_1586_);
v___x_1595_ = lean_st_ref_get(v_a_1579_);
v_env_1611_ = lean_ctor_get(v___x_1595_, 0);
lean_inc_ref(v_env_1611_);
lean_dec(v___x_1595_);
v___x_1612_ = l_Lean_PostprocessTraces_allStoredTraces(v_env_1611_);
v___x_1613_ = lean_box(0);
v___x_1614_ = l_List_mapTR_loop___at___00__private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace_spec__0(v___x_1612_, v___x_1613_);
v___x_1615_ = l_List_isEmpty___redArg(v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1616_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9);
v___x_1617_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12);
v___x_1618_ = l_Lean_MessageData_joinSep(v___x_1614_, v___x_1617_);
v___x_1619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1616_);
lean_ctor_set(v___x_1619_, 1, v___x_1618_);
v___y_1597_ = v___x_1619_;
goto v___jp_1596_;
}
else
{
lean_object* v___x_1620_; 
lean_dec(v___x_1614_);
v___x_1620_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14);
v___y_1597_ = v___x_1620_;
goto v___jp_1596_;
}
v___jp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1598_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1);
v___x_1599_ = l_Lean_TSyntax_getId(v_id_1577_);
v___x_1600_ = l_Lean_MessageData_ofName(v___x_1599_);
lean_inc_ref(v___x_1600_);
v___x_1601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1598_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3);
v___x_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1601_);
lean_ctor_set(v___x_1603_, 1, v___x_1602_);
v___x_1604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v___y_1597_);
v___x_1605_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v___x_1600_);
v___x_1608_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7);
v___x_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1607_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
v___x_1610_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_id_1577_, v___x_1609_, v_a_1578_, v_a_1579_);
lean_dec(v_id_1577_);
return v___x_1610_;
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec(v_id_1577_);
v_a_1622_ = lean_ctor_get(v___x_1583_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1583_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1583_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1583_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___boxed(lean_object* v_id_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(v_id_1630_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
return v_res_1634_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0(uint8_t v_suppressElabErrors_1636_, lean_object* v_x_1637_){
_start:
{
if (lean_obj_tag(v_x_1637_) == 1)
{
lean_object* v_pre_1638_; 
v_pre_1638_ = lean_ctor_get(v_x_1637_, 0);
if (lean_obj_tag(v_pre_1638_) == 0)
{
lean_object* v_str_1639_; lean_object* v___x_1640_; uint8_t v___x_1641_; 
v_str_1639_ = lean_ctor_get(v_x_1637_, 1);
v___x_1640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___closed__0));
v___x_1641_ = lean_string_dec_eq(v_str_1639_, v___x_1640_);
if (v___x_1641_ == 0)
{
return v___x_1641_;
}
else
{
return v_suppressElabErrors_1636_;
}
}
else
{
uint8_t v___x_1642_; 
v___x_1642_ = 0;
return v___x_1642_;
}
}
else
{
uint8_t v___x_1643_; 
v___x_1643_ = 0;
return v___x_1643_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_1644_, lean_object* v_x_1645_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1646_; uint8_t v_res_1647_; lean_object* v_r_1648_; 
v_suppressElabErrors_boxed_1646_ = lean_unbox(v_suppressElabErrors_1644_);
v_res_1647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0(v_suppressElabErrors_boxed_1646_, v_x_1645_);
lean_dec(v_x_1645_);
v_r_1648_ = lean_box(v_res_1647_);
return v_r_1648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v_as_1651_, size_t v_sz_1652_, size_t v_i_1653_, lean_object* v_b_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_a_1659_; uint8_t v___x_1663_; 
v___x_1663_ = lean_usize_dec_lt(v_i_1653_, v_sz_1652_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1664_, 0, v_b_1654_);
return v___x_1664_;
}
else
{
lean_object* v_fileName_1665_; lean_object* v_fileMap_1666_; uint8_t v_suppressElabErrors_1667_; lean_object* v_a_1668_; lean_object* v_data_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; lean_object* v___x_1672_; lean_object* v___y_1674_; 
v_fileName_1665_ = lean_ctor_get(v___y_1655_, 0);
v_fileMap_1666_ = lean_ctor_get(v___y_1655_, 1);
v_suppressElabErrors_1667_ = lean_ctor_get_uint8(v___y_1655_, sizeof(void*)*10);
v_a_1668_ = lean_array_uget_borrowed(v_as_1651_, v_i_1653_);
v_data_1669_ = lean_ctor_get(v_a_1668_, 4);
v___x_1670_ = lean_box(0);
v___x_1671_ = 0;
lean_inc(v_data_1669_);
lean_inc_ref(v_fileMap_1666_);
lean_inc_ref(v_fileName_1665_);
v___x_1672_ = l_Lean_Elab_mkMessageCore(v_fileName_1665_, v_fileMap_1666_, v_data_1669_, v___x_1671_, v___y_1649_, v___y_1650_);
if (v_suppressElabErrors_1667_ == 0)
{
v___y_1674_ = v___y_1656_;
goto v___jp_1673_;
}
else
{
lean_object* v_data_1737_; lean_object* v___x_1738_; lean_object* v___f_1739_; uint8_t v___x_1740_; 
v_data_1737_ = lean_ctor_get(v___x_1672_, 4);
v___x_1738_ = lean_box(v_suppressElabErrors_1667_);
v___f_1739_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1739_, 0, v___x_1738_);
lean_inc(v_data_1737_);
v___x_1740_ = l_Lean_MessageData_hasTag(v___f_1739_, v_data_1737_);
if (v___x_1740_ == 0)
{
lean_dec_ref(v___x_1672_);
v_a_1659_ = v___x_1670_;
goto v___jp_1658_;
}
else
{
v___y_1674_ = v___y_1656_;
goto v___jp_1673_;
}
}
v___jp_1673_:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Elab_Command_getScope___redArg(v___y_1674_);
if (lean_obj_tag(v___x_1675_) == 0)
{
lean_object* v_a_1676_; lean_object* v_currNamespace_1677_; lean_object* v___x_1678_; 
v_a_1676_ = lean_ctor_get(v___x_1675_, 0);
lean_inc(v_a_1676_);
lean_dec_ref_known(v___x_1675_, 1);
v_currNamespace_1677_ = lean_ctor_get(v_a_1676_, 2);
lean_inc(v_currNamespace_1677_);
lean_dec(v_a_1676_);
v___x_1678_ = l_Lean_Elab_Command_getScope___redArg(v___y_1674_);
if (lean_obj_tag(v___x_1678_) == 0)
{
lean_object* v_a_1679_; lean_object* v_openDecls_1680_; lean_object* v_fileName_1681_; lean_object* v_pos_1682_; lean_object* v_endPos_1683_; uint8_t v_keepFullRange_1684_; uint8_t v_severity_1685_; uint8_t v_isSilent_1686_; lean_object* v_caption_1687_; lean_object* v_data_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1720_; 
v_a_1679_ = lean_ctor_get(v___x_1678_, 0);
lean_inc(v_a_1679_);
lean_dec_ref_known(v___x_1678_, 1);
v_openDecls_1680_ = lean_ctor_get(v_a_1679_, 3);
lean_inc(v_openDecls_1680_);
lean_dec(v_a_1679_);
v_fileName_1681_ = lean_ctor_get(v___x_1672_, 0);
v_pos_1682_ = lean_ctor_get(v___x_1672_, 1);
v_endPos_1683_ = lean_ctor_get(v___x_1672_, 2);
v_keepFullRange_1684_ = lean_ctor_get_uint8(v___x_1672_, sizeof(void*)*5);
v_severity_1685_ = lean_ctor_get_uint8(v___x_1672_, sizeof(void*)*5 + 1);
v_isSilent_1686_ = lean_ctor_get_uint8(v___x_1672_, sizeof(void*)*5 + 2);
v_caption_1687_ = lean_ctor_get(v___x_1672_, 3);
v_data_1688_ = lean_ctor_get(v___x_1672_, 4);
v_isSharedCheck_1720_ = !lean_is_exclusive(v___x_1672_);
if (v_isSharedCheck_1720_ == 0)
{
v___x_1690_ = v___x_1672_;
v_isShared_1691_ = v_isSharedCheck_1720_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_data_1688_);
lean_inc(v_caption_1687_);
lean_inc(v_endPos_1683_);
lean_inc(v_pos_1682_);
lean_inc(v_fileName_1681_);
lean_dec(v___x_1672_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1720_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1695_; 
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v_currNamespace_1677_);
lean_ctor_set(v___x_1692_, 1, v_openDecls_1680_);
v___x_1693_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
lean_ctor_set(v___x_1693_, 1, v_data_1688_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 4, v___x_1693_);
v___x_1695_ = v___x_1690_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_fileName_1681_);
lean_ctor_set(v_reuseFailAlloc_1719_, 1, v_pos_1682_);
lean_ctor_set(v_reuseFailAlloc_1719_, 2, v_endPos_1683_);
lean_ctor_set(v_reuseFailAlloc_1719_, 3, v_caption_1687_);
lean_ctor_set(v_reuseFailAlloc_1719_, 4, v___x_1693_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*5, v_keepFullRange_1684_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*5 + 1, v_severity_1685_);
lean_ctor_set_uint8(v_reuseFailAlloc_1719_, sizeof(void*)*5 + 2, v_isSilent_1686_);
v___x_1695_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; lean_object* v_env_1697_; lean_object* v_messages_1698_; lean_object* v_scopes_1699_; lean_object* v_usedQuotCtxts_1700_; lean_object* v_nextMacroScope_1701_; lean_object* v_maxRecDepth_1702_; lean_object* v_ngen_1703_; lean_object* v_auxDeclNGen_1704_; lean_object* v_infoState_1705_; lean_object* v_traceState_1706_; lean_object* v_snapshotTasks_1707_; lean_object* v_prevLinterStates_1708_; lean_object* v_codeQualityEntryTasks_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1718_; 
v___x_1696_ = lean_st_ref_take(v___y_1674_);
v_env_1697_ = lean_ctor_get(v___x_1696_, 0);
v_messages_1698_ = lean_ctor_get(v___x_1696_, 1);
v_scopes_1699_ = lean_ctor_get(v___x_1696_, 2);
v_usedQuotCtxts_1700_ = lean_ctor_get(v___x_1696_, 3);
v_nextMacroScope_1701_ = lean_ctor_get(v___x_1696_, 4);
v_maxRecDepth_1702_ = lean_ctor_get(v___x_1696_, 5);
v_ngen_1703_ = lean_ctor_get(v___x_1696_, 6);
v_auxDeclNGen_1704_ = lean_ctor_get(v___x_1696_, 7);
v_infoState_1705_ = lean_ctor_get(v___x_1696_, 8);
v_traceState_1706_ = lean_ctor_get(v___x_1696_, 9);
v_snapshotTasks_1707_ = lean_ctor_get(v___x_1696_, 10);
v_prevLinterStates_1708_ = lean_ctor_get(v___x_1696_, 11);
v_codeQualityEntryTasks_1709_ = lean_ctor_get(v___x_1696_, 12);
v_isSharedCheck_1718_ = !lean_is_exclusive(v___x_1696_);
if (v_isSharedCheck_1718_ == 0)
{
v___x_1711_ = v___x_1696_;
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1709_);
lean_inc(v_prevLinterStates_1708_);
lean_inc(v_snapshotTasks_1707_);
lean_inc(v_traceState_1706_);
lean_inc(v_infoState_1705_);
lean_inc(v_auxDeclNGen_1704_);
lean_inc(v_ngen_1703_);
lean_inc(v_maxRecDepth_1702_);
lean_inc(v_nextMacroScope_1701_);
lean_inc(v_usedQuotCtxts_1700_);
lean_inc(v_scopes_1699_);
lean_inc(v_messages_1698_);
lean_inc(v_env_1697_);
lean_dec(v___x_1696_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1718_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1713_ = l_Lean_MessageLog_add(v___x_1695_, v_messages_1698_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v___x_1713_);
v___x_1715_ = v___x_1711_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_env_1697_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1717_, 2, v_scopes_1699_);
lean_ctor_set(v_reuseFailAlloc_1717_, 3, v_usedQuotCtxts_1700_);
lean_ctor_set(v_reuseFailAlloc_1717_, 4, v_nextMacroScope_1701_);
lean_ctor_set(v_reuseFailAlloc_1717_, 5, v_maxRecDepth_1702_);
lean_ctor_set(v_reuseFailAlloc_1717_, 6, v_ngen_1703_);
lean_ctor_set(v_reuseFailAlloc_1717_, 7, v_auxDeclNGen_1704_);
lean_ctor_set(v_reuseFailAlloc_1717_, 8, v_infoState_1705_);
lean_ctor_set(v_reuseFailAlloc_1717_, 9, v_traceState_1706_);
lean_ctor_set(v_reuseFailAlloc_1717_, 10, v_snapshotTasks_1707_);
lean_ctor_set(v_reuseFailAlloc_1717_, 11, v_prevLinterStates_1708_);
lean_ctor_set(v_reuseFailAlloc_1717_, 12, v_codeQualityEntryTasks_1709_);
v___x_1715_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1716_; 
v___x_1716_ = lean_st_ref_put(v___y_1674_, v___x_1715_);
v_a_1659_ = v___x_1670_;
goto v___jp_1658_;
}
}
}
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec(v_currNamespace_1677_);
lean_dec_ref(v___x_1672_);
v_a_1721_ = lean_ctor_get(v___x_1678_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1678_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1678_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1678_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec_ref(v___x_1672_);
v_a_1729_ = lean_ctor_get(v___x_1675_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1675_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1675_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1675_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
v___jp_1658_:
{
size_t v___x_1660_; size_t v___x_1661_; 
v___x_1660_ = ((size_t)1ULL);
v___x_1661_ = lean_usize_add(v_i_1653_, v___x_1660_);
v_i_1653_ = v___x_1661_;
v_b_1654_ = v_a_1659_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___boxed(lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v_as_1743_, lean_object* v_sz_1744_, lean_object* v_i_1745_, lean_object* v_b_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
size_t v_sz_boxed_1750_; size_t v_i_boxed_1751_; lean_object* v_res_1752_; 
v_sz_boxed_1750_ = lean_unbox_usize(v_sz_1744_);
lean_dec(v_sz_1744_);
v_i_boxed_1751_ = lean_unbox_usize(v_i_1745_);
lean_dec(v_i_1745_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(v___y_1741_, v___y_1742_, v_as_1743_, v_sz_boxed_1750_, v_i_boxed_1751_, v_b_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec_ref(v_as_1743_);
lean_dec(v___y_1742_);
lean_dec(v___y_1741_);
return v_res_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces(lean_object* v_x_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_){
_start:
{
lean_object* v___x_1757_; uint8_t v___x_1758_; 
v___x_1757_ = ((lean_object*)(l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1));
lean_inc(v_x_1753_);
v___x_1758_ = l_Lean_Syntax_isOfKind(v_x_1753_, v___x_1757_);
if (v___x_1758_ == 0)
{
lean_object* v___x_1759_; 
lean_dec(v_x_1753_);
v___x_1759_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; lean_object* v_id_1761_; lean_object* v___x_1762_; lean_object* v_post_1763_; lean_object* v___x_1764_; 
v___x_1760_ = lean_unsigned_to_nat(1u);
v_id_1761_ = l_Lean_Syntax_getArg(v_x_1753_, v___x_1760_);
v___x_1762_ = lean_unsigned_to_nat(2u);
v_post_1763_ = l_Lean_Syntax_getArg(v_x_1753_, v___x_1762_);
lean_dec(v_x_1753_);
v___x_1764_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(v_id_1761_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
lean_dec_ref_known(v___x_1764_, 1);
v___x_1766_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1763_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1766_) == 0)
{
lean_object* v_a_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v_a_1767_ = lean_ctor_get(v___x_1766_, 0);
lean_inc(v_a_1767_);
lean_dec_ref_known(v___x_1766_, 1);
v___x_1768_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_StoredTrace_postprocess___boxed), 5, 2);
lean_closure_set(v___x_1768_, 0, v_a_1765_);
lean_closure_set(v___x_1768_, 1, v_a_1767_);
v___x_1769_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1768_, v_a_1754_, v_a_1755_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1771_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
lean_inc(v_a_1770_);
lean_dec_ref_known(v___x_1769_, 1);
v___x_1771_ = l_Lean_Elab_Command_getRef___redArg(v_a_1754_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_object* v_a_1772_; lean_object* v___y_1774_; lean_object* v___y_1775_; uint8_t v___x_1788_; lean_object* v___y_1790_; lean_object* v___x_1793_; 
v_a_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_a_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1788_ = 0;
v___x_1793_ = l_Lean_Syntax_getPos_x3f(v_a_1772_, v___x_1788_);
if (lean_obj_tag(v___x_1793_) == 0)
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_unsigned_to_nat(0u);
v___y_1790_ = v___x_1794_;
goto v___jp_1789_;
}
else
{
lean_object* v_val_1795_; 
v_val_1795_ = lean_ctor_get(v___x_1793_, 0);
lean_inc(v_val_1795_);
lean_dec_ref_known(v___x_1793_, 1);
v___y_1790_ = v_val_1795_;
goto v___jp_1789_;
}
v___jp_1773_:
{
lean_object* v___x_1776_; size_t v_sz_1777_; size_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = lean_box(0);
v_sz_1777_ = lean_array_size(v_a_1770_);
v___x_1778_ = ((size_t)0ULL);
v___x_1779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(v___y_1774_, v___y_1775_, v_a_1770_, v_sz_1777_, v___x_1778_, v___x_1776_, v_a_1754_, v_a_1755_);
lean_dec(v_a_1770_);
lean_dec(v___y_1775_);
lean_dec(v___y_1774_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1786_ == 0)
{
lean_object* v_unused_1787_; 
v_unused_1787_ = lean_ctor_get(v___x_1779_, 0);
lean_dec(v_unused_1787_);
v___x_1781_ = v___x_1779_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_dec(v___x_1779_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
lean_ctor_set(v___x_1781_, 0, v___x_1776_);
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1776_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
else
{
return v___x_1779_;
}
}
v___jp_1789_:
{
lean_object* v___x_1791_; 
v___x_1791_ = l_Lean_Syntax_getTailPos_x3f(v_a_1772_, v___x_1788_);
lean_dec(v_a_1772_);
if (lean_obj_tag(v___x_1791_) == 0)
{
lean_inc(v___y_1790_);
v___y_1774_ = v___y_1790_;
v___y_1775_ = v___y_1790_;
goto v___jp_1773_;
}
else
{
lean_object* v_val_1792_; 
v_val_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___y_1774_ = v___y_1790_;
v___y_1775_ = v_val_1792_;
goto v___jp_1773_;
}
}
}
else
{
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec(v_a_1770_);
v_a_1796_ = lean_ctor_get(v___x_1771_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1771_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1771_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1771_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
v_a_1804_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1769_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1769_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v_a_1765_);
v_a_1812_ = lean_ctor_get(v___x_1766_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1766_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1766_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1766_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_post_1763_);
v_a_1820_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1764_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1764_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces___boxed(lean_object* v_x_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces(v_x_1828_, v_a_1829_, v_a_1830_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
return v_res_1832_;
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
