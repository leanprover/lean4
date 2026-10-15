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
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "A declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "` exists in the private scope of `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "`, which is accessible here through `import all`, but `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "` does not export it, so it cannot be accessed in a public scope."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__19;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__20 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__20_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__21;
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
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__15(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__14));
v___x_589_ = l_Lean_stringToMessageData(v___x_588_);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__17(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__16));
v___x_592_ = l_Lean_stringToMessageData(v___x_591_);
return v___x_592_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__19(void){
_start:
{
lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_594_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__18));
v___x_595_ = l_Lean_stringToMessageData(v___x_594_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__21(void){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; 
v___x_597_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__20));
v___x_598_ = l_Lean_stringToMessageData(v___x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(lean_object* v_msg_599_, lean_object* v_declHint_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v_env_605_; uint8_t v___x_606_; 
v___x_603_ = lean_box(0);
v___x_604_ = lean_st_ref_get(v___y_601_);
v_env_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_env_605_);
lean_dec(v___x_604_);
v___x_606_ = l_Lean_Name_isAnonymous(v_declHint_600_);
if (v___x_606_ == 0)
{
uint8_t v_isExporting_607_; 
v_isExporting_607_ = lean_ctor_get_uint8(v_env_605_, sizeof(void*)*13);
if (v_isExporting_607_ == 0)
{
lean_object* v___x_608_; 
lean_dec_ref(v_env_605_);
lean_dec(v_declHint_600_);
v___x_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_608_, 0, v_msg_599_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; uint8_t v___x_610_; 
lean_inc_ref(v_env_605_);
v___x_609_ = l_Lean_Environment_setExporting(v_env_605_, v___x_606_);
lean_inc(v_declHint_600_);
lean_inc_ref(v___x_609_);
v___x_610_ = l_Lean_Environment_contains(v___x_609_, v_declHint_600_, v_isExporting_607_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; 
lean_dec_ref(v___x_609_);
lean_dec_ref(v_env_605_);
lean_dec(v_declHint_600_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v_msg_599_);
return v___x_611_;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v_c_617_; lean_object* v___x_618_; 
v___x_612_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_613_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
v___x_614_ = l_Lean_Options_empty;
v___x_615_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_615_, 0, v___x_609_);
lean_ctor_set(v___x_615_, 1, v___x_612_);
lean_ctor_set(v___x_615_, 2, v___x_613_);
lean_ctor_set(v___x_615_, 3, v___x_614_);
lean_inc(v_declHint_600_);
v___x_616_ = l_Lean_MessageData_ofConstName(v_declHint_600_, v___x_606_);
v_c_617_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_617_, 0, v___x_615_);
lean_ctor_set(v_c_617_, 1, v___x_616_);
v___x_618_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_605_, v_declHint_600_);
if (lean_obj_tag(v___x_618_) == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec_ref(v_env_605_);
lean_dec(v_declHint_600_);
v___x_619_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_619_);
lean_ctor_set(v___x_620_, 1, v_c_617_);
v___x_621_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__3);
v___x_622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_620_);
lean_ctor_set(v___x_622_, 1, v___x_621_);
v___x_623_ = l_Lean_MessageData_note(v___x_622_);
v___x_624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_624_, 0, v_msg_599_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
v___x_625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
return v___x_625_;
}
else
{
lean_object* v_val_626_; lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_682_; 
v_val_626_ = lean_ctor_get(v___x_618_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_618_);
if (v_isSharedCheck_682_ == 0)
{
v___x_628_ = v___x_618_;
v_isShared_629_ = v_isSharedCheck_682_;
goto v_resetjp_627_;
}
else
{
lean_inc(v_val_626_);
lean_dec(v___x_618_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_682_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
lean_object* v___x_630_; lean_object* v_modules_631_; lean_object* v_moduleNames_632_; lean_object* v_mod_633_; uint8_t v___y_635_; uint8_t v___x_665_; 
v___x_630_ = l_Lean_Environment_header(v_env_605_);
lean_dec_ref(v_env_605_);
v_modules_631_ = lean_ctor_get(v___x_630_, 3);
lean_inc_ref(v_modules_631_);
v_moduleNames_632_ = lean_ctor_get(v___x_630_, 4);
lean_inc_ref(v_moduleNames_632_);
lean_dec_ref(v___x_630_);
v_mod_633_ = lean_array_get(v___x_603_, v_moduleNames_632_, v_val_626_);
lean_dec_ref(v_moduleNames_632_);
v___x_665_ = l_Lean_isPrivateName(v_declHint_600_);
lean_dec(v_declHint_600_);
if (v___x_665_ == 0)
{
lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_666_ = lean_array_get_size(v_modules_631_);
v___x_667_ = lean_nat_dec_lt(v_val_626_, v___x_666_);
if (v___x_667_ == 0)
{
lean_dec_ref(v_modules_631_);
lean_dec(v_val_626_);
v___y_635_ = v___x_665_;
goto v___jp_634_;
}
else
{
lean_object* v___x_668_; lean_object* v_toImport_669_; uint8_t v_isExported_670_; 
v___x_668_ = lean_array_fget(v_modules_631_, v_val_626_);
lean_dec(v_val_626_);
lean_dec_ref(v_modules_631_);
v_toImport_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc_ref(v_toImport_669_);
lean_dec(v___x_668_);
v_isExported_670_ = lean_ctor_get_uint8(v_toImport_669_, sizeof(void*)*1 + 1);
lean_dec_ref(v_toImport_669_);
v___y_635_ = v_isExported_670_;
goto v___jp_634_;
}
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
lean_dec_ref(v_modules_631_);
lean_del_object(v___x_628_);
lean_dec(v_val_626_);
v___x_671_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__1);
v___x_672_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v_c_617_);
v___x_673_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__19);
v___x_674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
v___x_675_ = l_Lean_MessageData_ofName(v_mod_633_);
v___x_676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
v___x_677_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__21, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__21_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__21);
v___x_678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_678_, 0, v___x_676_);
lean_ctor_set(v___x_678_, 1, v___x_677_);
v___x_679_ = l_Lean_MessageData_note(v___x_678_);
v___x_680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_680_, 0, v_msg_599_);
lean_ctor_set(v___x_680_, 1, v___x_679_);
v___x_681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
return v___x_681_;
}
v___jp_634_:
{
if (v___y_635_ == 0)
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_636_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__5);
v___x_637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_c_617_);
v___x_638_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__7);
v___x_639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_637_);
lean_ctor_set(v___x_639_, 1, v___x_638_);
v___x_640_ = l_Lean_MessageData_ofName(v_mod_633_);
v___x_641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__9);
v___x_643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_641_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
v___x_644_ = l_Lean_MessageData_note(v___x_643_);
v___x_645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_645_, 0, v_msg_599_);
lean_ctor_set(v___x_645_, 1, v___x_644_);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 0);
lean_ctor_set(v___x_628_, 0, v___x_645_);
v___x_647_ = v___x_628_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v___x_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_649_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__11);
v___x_650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
lean_ctor_set(v___x_650_, 1, v_c_617_);
v___x_651_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__13);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l_Lean_MessageData_ofName(v_mod_633_);
lean_inc_ref(v___x_653_);
v___x_654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_652_);
lean_ctor_set(v___x_654_, 1, v___x_653_);
v___x_655_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__15);
v___x_656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_654_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
v___x_657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_656_);
lean_ctor_set(v___x_657_, 1, v___x_653_);
v___x_658_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___closed__17);
v___x_659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_657_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
v___x_660_ = l_Lean_MessageData_note(v___x_659_);
v___x_661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_661_, 0, v_msg_599_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
if (v_isShared_629_ == 0)
{
lean_ctor_set_tag(v___x_628_, 0);
lean_ctor_set(v___x_628_, 0, v___x_661_);
v___x_663_ = v___x_628_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
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
lean_object* v___x_683_; 
lean_dec_ref(v_env_605_);
lean_dec(v_declHint_600_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v_msg_599_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg___boxed(lean_object* v_msg_684_, lean_object* v_declHint_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_684_, v_declHint_685_, v___y_686_);
lean_dec(v___y_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(lean_object* v_msg_689_, lean_object* v_declHint_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_704_; 
v___x_694_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_689_, v_declHint_690_, v___y_692_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_704_ == 0)
{
v___x_697_ = v___x_694_;
v_isShared_698_ = v_isSharedCheck_704_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_704_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_702_; 
v___x_699_ = l_Lean_unknownIdentifierMessageTag;
v___x_700_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v_a_695_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 0, v___x_700_);
v___x_702_ = v___x_697_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15___boxed(lean_object* v_msg_705_, lean_object* v_declHint_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(v_msg_705_, v_declHint_706_, v___y_707_, v___y_708_);
lean_dec(v___y_708_);
lean_dec_ref(v___y_707_);
return v_res_710_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(lean_object* v_opts_711_, lean_object* v_opt_712_){
_start:
{
lean_object* v_name_713_; lean_object* v_defValue_714_; lean_object* v_map_715_; lean_object* v___x_716_; 
v_name_713_ = lean_ctor_get(v_opt_712_, 0);
v_defValue_714_ = lean_ctor_get(v_opt_712_, 1);
v_map_715_ = lean_ctor_get(v_opts_711_, 0);
v___x_716_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_715_, v_name_713_);
if (lean_obj_tag(v___x_716_) == 0)
{
uint8_t v___x_717_; 
v___x_717_ = lean_unbox(v_defValue_714_);
return v___x_717_;
}
else
{
lean_object* v_val_718_; 
v_val_718_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_val_718_);
lean_dec_ref_known(v___x_716_, 1);
if (lean_obj_tag(v_val_718_) == 1)
{
uint8_t v_v_719_; 
v_v_719_ = lean_ctor_get_uint8(v_val_718_, 0);
lean_dec_ref_known(v_val_718_, 0);
return v_v_719_;
}
else
{
uint8_t v___x_720_; 
lean_dec(v_val_718_);
v___x_720_ = lean_unbox(v_defValue_714_);
return v___x_720_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21___boxed(lean_object* v_opts_721_, lean_object* v_opt_722_){
_start:
{
uint8_t v_res_723_; lean_object* v_r_724_; 
v_res_723_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(v_opts_721_, v_opt_722_);
lean_dec_ref(v_opt_722_);
lean_dec_ref(v_opts_721_);
v_r_724_ = lean_box(v_res_723_);
return v_r_724_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_box(1);
v___x_726_ = l_Lean_MessageData_ofFormat(v___x_725_);
return v___x_726_;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3(void){
_start:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__2));
v___x_731_ = l_Lean_MessageData_ofFormat(v___x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22(lean_object* v_x_732_, lean_object* v_x_733_){
_start:
{
if (lean_obj_tag(v_x_733_) == 0)
{
return v_x_732_;
}
else
{
lean_object* v_head_734_; lean_object* v_tail_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_757_; 
v_head_734_ = lean_ctor_get(v_x_733_, 0);
v_tail_735_ = lean_ctor_get(v_x_733_, 1);
v_isSharedCheck_757_ = !lean_is_exclusive(v_x_733_);
if (v_isSharedCheck_757_ == 0)
{
v___x_737_ = v_x_733_;
v_isShared_738_ = v_isSharedCheck_757_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_tail_735_);
lean_inc(v_head_734_);
lean_dec(v_x_733_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_757_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_before_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_755_; 
v_before_739_ = lean_ctor_get(v_head_734_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v_head_734_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_head_734_, 1);
lean_dec(v_unused_756_);
v___x_741_ = v_head_734_;
v_isShared_742_ = v_isSharedCheck_755_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_before_739_);
lean_dec(v_head_734_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_755_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_743_; lean_object* v___x_745_; 
v___x_743_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0);
if (v_isShared_742_ == 0)
{
lean_ctor_set_tag(v___x_741_, 7);
lean_ctor_set(v___x_741_, 1, v___x_743_);
lean_ctor_set(v___x_741_, 0, v_x_732_);
v___x_745_ = v___x_741_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_x_732_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_743_);
v___x_745_ = v_reuseFailAlloc_754_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__3);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 7);
lean_ctor_set(v___x_737_, 1, v___x_746_);
lean_ctor_set(v___x_737_, 0, v___x_745_);
v___x_748_ = v___x_737_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___x_746_);
v___x_748_ = v_reuseFailAlloc_753_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = l_Lean_MessageData_ofSyntax(v_before_739_);
v___x_750_ = l_Lean_indentD(v___x_749_);
v___x_751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_748_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
v_x_732_ = v___x_751_;
v_x_733_ = v_tail_735_;
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
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__1));
v___x_762_ = l_Lean_MessageData_ofFormat(v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(lean_object* v_msgData_763_, lean_object* v_macroStack_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v_scopes_769_; lean_object* v___x_770_; lean_object* v_opts_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v___x_767_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_768_ = lean_st_ref_get(v___y_765_);
v_scopes_769_ = lean_ctor_get(v___x_768_, 2);
lean_inc(v_scopes_769_);
lean_dec(v___x_768_);
v___x_770_ = l_List_head_x21___redArg(v___x_767_, v_scopes_769_);
lean_dec(v_scopes_769_);
v_opts_771_ = lean_ctor_get(v___x_770_, 1);
lean_inc_ref(v_opts_771_);
lean_dec(v___x_770_);
v___x_772_ = l_Lean_Elab_pp_macroStack;
v___x_773_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__21(v_opts_771_, v___x_772_);
lean_dec_ref(v_opts_771_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; 
lean_dec(v_macroStack_764_);
v___x_774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_774_, 0, v_msgData_763_);
return v___x_774_;
}
else
{
if (lean_obj_tag(v_macroStack_764_) == 0)
{
lean_object* v___x_775_; 
v___x_775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_775_, 0, v_msgData_763_);
return v___x_775_;
}
else
{
lean_object* v_head_776_; lean_object* v_after_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_792_; 
v_head_776_ = lean_ctor_get(v_macroStack_764_, 0);
lean_inc(v_head_776_);
v_after_777_ = lean_ctor_get(v_head_776_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_head_776_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_head_776_, 0);
lean_dec(v_unused_793_);
v___x_779_ = v_head_776_;
v_isShared_780_ = v_isSharedCheck_792_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_after_777_);
lean_dec(v_head_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_792_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22___closed__0);
if (v_isShared_780_ == 0)
{
lean_ctor_set_tag(v___x_779_, 7);
lean_ctor_set(v___x_779_, 1, v___x_781_);
lean_ctor_set(v___x_779_, 0, v_msgData_763_);
v___x_783_ = v___x_779_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_msgData_763_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_791_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v_msgData_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_784_ = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___closed__2);
v___x_785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_785_, 0, v___x_783_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
v___x_786_ = l_Lean_MessageData_ofSyntax(v_after_777_);
v___x_787_ = l_Lean_indentD(v___x_786_);
v_msgData_788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_msgData_788_, 0, v___x_785_);
lean_ctor_set(v_msgData_788_, 1, v___x_787_);
v___x_789_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20_spec__22(v_msgData_788_, v_macroStack_764_);
v___x_790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
return v___x_790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg___boxed(lean_object* v_msgData_794_, lean_object* v_macroStack_795_, lean_object* v___y_796_, lean_object* v___y_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_msgData_794_, v_macroStack_795_, v___y_796_);
lean_dec(v___y_796_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(lean_object* v_msgData_799_, lean_object* v___y_800_){
_start:
{
lean_object* v___x_802_; lean_object* v_env_803_; uint8_t v___x_804_; lean_object* v_env_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v_scopes_808_; lean_object* v___x_809_; lean_object* v_opts_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___x_802_ = lean_st_ref_get(v___y_800_);
v_env_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc_ref(v_env_803_);
lean_dec(v___x_802_);
v___x_804_ = 0;
v_env_805_ = l_Lean_Environment_setRecordingDeps(v_env_803_, v___x_804_);
v___x_806_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_807_ = lean_st_ref_get(v___y_800_);
v_scopes_808_ = lean_ctor_get(v___x_807_, 2);
lean_inc(v_scopes_808_);
lean_dec(v___x_807_);
v___x_809_ = l_List_head_x21___redArg(v___x_806_, v_scopes_808_);
lean_dec(v_scopes_808_);
v_opts_810_ = lean_ctor_get(v___x_809_, 1);
lean_inc_ref(v_opts_810_);
lean_dec(v___x_809_);
v___x_811_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__2);
v___x_812_ = lean_unsigned_to_nat(32u);
v___x_813_ = lean_mk_empty_array_with_capacity(v___x_812_);
lean_dec_ref(v___x_813_);
v___x_814_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0_spec__0___closed__5);
v___x_815_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_815_, 0, v_env_805_);
lean_ctor_set(v___x_815_, 1, v___x_811_);
lean_ctor_set(v___x_815_, 2, v___x_814_);
lean_ctor_set(v___x_815_, 3, v_opts_810_);
v___x_816_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v_msgData_799_);
v___x_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg___boxed(lean_object* v_msgData_818_, lean_object* v___y_819_, lean_object* v___y_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msgData_818_, v___y_819_);
lean_dec(v___y_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(lean_object* v_msg_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_Lean_Elab_Command_getRef___redArg(v___y_823_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v_macroStack_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v_a_831_; lean_object* v___x_832_; lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_841_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
v_macroStack_828_ = lean_ctor_get(v___y_823_, 4);
v___x_829_ = l_Lean_Elab_getBetterRef(v_a_827_, v_macroStack_828_);
lean_dec(v_a_827_);
v___x_830_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msg_822_, v___y_824_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref(v___x_830_);
lean_inc(v_macroStack_828_);
v___x_832_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_a_831_, v_macroStack_828_, v___y_824_);
v_a_833_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_841_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_841_ == 0)
{
v___x_835_ = v___x_832_;
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_832_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_841_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_837_; lean_object* v___x_839_; 
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_829_);
lean_ctor_set(v___x_837_, 1, v_a_833_);
if (v_isShared_836_ == 0)
{
lean_ctor_set_tag(v___x_835_, 1);
lean_ctor_set(v___x_835_, 0, v___x_837_);
v___x_839_ = v___x_835_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec_ref(v_msg_822_);
v_a_842_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_826_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_826_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg___boxed(lean_object* v_msg_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_850_, v___y_851_, v___y_852_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(lean_object* v_ref_855_, lean_object* v_msg_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
lean_object* v___x_860_; 
v___x_860_ = l_Lean_Elab_Command_getRef___redArg(v___y_857_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_a_861_; lean_object* v_fileName_862_; lean_object* v_fileMap_863_; lean_object* v_currRecDepth_864_; lean_object* v_cmdPos_865_; lean_object* v_macroStack_866_; lean_object* v_quotContext_x3f_867_; lean_object* v_currMacroScope_868_; lean_object* v_snap_x3f_869_; lean_object* v_cancelTk_x3f_870_; uint8_t v_suppressElabErrors_871_; lean_object* v_ref_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref_known(v___x_860_, 1);
v_fileName_862_ = lean_ctor_get(v___y_857_, 0);
v_fileMap_863_ = lean_ctor_get(v___y_857_, 1);
v_currRecDepth_864_ = lean_ctor_get(v___y_857_, 2);
v_cmdPos_865_ = lean_ctor_get(v___y_857_, 3);
v_macroStack_866_ = lean_ctor_get(v___y_857_, 4);
v_quotContext_x3f_867_ = lean_ctor_get(v___y_857_, 5);
v_currMacroScope_868_ = lean_ctor_get(v___y_857_, 6);
v_snap_x3f_869_ = lean_ctor_get(v___y_857_, 8);
v_cancelTk_x3f_870_ = lean_ctor_get(v___y_857_, 9);
v_suppressElabErrors_871_ = lean_ctor_get_uint8(v___y_857_, sizeof(void*)*10);
v_ref_872_ = l_Lean_replaceRef(v_ref_855_, v_a_861_);
lean_dec(v_a_861_);
lean_inc(v_cancelTk_x3f_870_);
lean_inc(v_snap_x3f_869_);
lean_inc(v_currMacroScope_868_);
lean_inc(v_quotContext_x3f_867_);
lean_inc(v_macroStack_866_);
lean_inc(v_cmdPos_865_);
lean_inc(v_currRecDepth_864_);
lean_inc_ref(v_fileMap_863_);
lean_inc_ref(v_fileName_862_);
v___x_873_ = lean_alloc_ctor(0, 10, 1);
lean_ctor_set(v___x_873_, 0, v_fileName_862_);
lean_ctor_set(v___x_873_, 1, v_fileMap_863_);
lean_ctor_set(v___x_873_, 2, v_currRecDepth_864_);
lean_ctor_set(v___x_873_, 3, v_cmdPos_865_);
lean_ctor_set(v___x_873_, 4, v_macroStack_866_);
lean_ctor_set(v___x_873_, 5, v_quotContext_x3f_867_);
lean_ctor_set(v___x_873_, 6, v_currMacroScope_868_);
lean_ctor_set(v___x_873_, 7, v_ref_872_);
lean_ctor_set(v___x_873_, 8, v_snap_x3f_869_);
lean_ctor_set(v___x_873_, 9, v_cancelTk_x3f_870_);
lean_ctor_set_uint8(v___x_873_, sizeof(void*)*10, v_suppressElabErrors_871_);
v___x_874_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_856_, v___x_873_, v___y_858_);
lean_dec_ref_known(v___x_873_, 10);
return v___x_874_;
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v_msg_856_);
v_a_875_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_860_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_860_);
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
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg___boxed(lean_object* v_ref_883_, lean_object* v_msg_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_883_, v_msg_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v_ref_883_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(lean_object* v_ref_889_, lean_object* v_msg_890_, lean_object* v_declHint_891_, lean_object* v___y_892_, lean_object* v___y_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_a_896_; lean_object* v___x_897_; 
v___x_895_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15(v_msg_890_, v_declHint_891_, v___y_892_, v___y_893_);
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref(v___x_895_);
v___x_897_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_889_, v_a_896_, v___y_892_, v___y_893_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg___boxed(lean_object* v_ref_898_, lean_object* v_msg_899_, lean_object* v_declHint_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_898_, v_msg_899_, v_declHint_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v_ref_898_);
return v_res_904_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__0));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__2));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(lean_object* v_ref_911_, lean_object* v_constName_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v___x_916_; uint8_t v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_916_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__1);
v___x_917_ = 0;
lean_inc(v_constName_912_);
v___x_918_ = l_Lean_MessageData_ofConstName(v_constName_912_, v___x_917_);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_916_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_911_, v___x_921_, v_constName_912_, v___y_913_, v___y_914_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___boxed(lean_object* v_ref_923_, lean_object* v_constName_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_ref_923_, v_constName_924_, v___y_925_, v___y_926_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v_ref_923_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(lean_object* v_constName_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_Elab_Command_getRef___redArg(v___y_930_);
if (lean_obj_tag(v___x_933_) == 0)
{
lean_object* v_a_934_; lean_object* v___x_935_; 
v_a_934_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_a_934_);
lean_dec_ref_known(v___x_933_, 1);
v___x_935_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_a_934_, v_constName_929_, v___y_930_, v___y_931_);
lean_dec(v_a_934_);
return v___x_935_;
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_constName_929_);
v_a_936_ = lean_ctor_get(v___x_933_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_933_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_933_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg___boxed(lean_object* v_constName_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_944_, v___y_945_, v___y_946_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(lean_object* v_constName_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v___x_953_; lean_object* v_env_954_; uint8_t v___x_955_; lean_object* v___x_956_; 
v___x_953_ = lean_st_ref_get(v___y_951_);
v_env_954_ = lean_ctor_get(v___x_953_, 0);
lean_inc_ref(v_env_954_);
lean_dec(v___x_953_);
v___x_955_ = 0;
lean_inc(v_constName_949_);
v___x_956_ = l_Lean_Environment_findConstVal_x3f(v_env_954_, v_constName_949_, v___x_955_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_949_, v___y_950_, v___y_951_);
return v___x_957_;
}
else
{
lean_object* v_val_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_constName_949_);
v_val_958_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_956_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_val_958_);
lean_dec(v___x_956_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
lean_ctor_set_tag(v___x_960_, 0);
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_val_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6___boxed(lean_object* v_constName_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(v_constName_966_, v___y_967_, v___y_968_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(lean_object* v_constName_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; 
lean_inc(v_constName_971_);
v___x_975_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6(v_constName_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_987_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_987_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_987_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v_levelParams_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; 
v_levelParams_980_ = lean_ctor_get(v_a_976_, 1);
lean_inc(v_levelParams_980_);
lean_dec(v_a_976_);
v___x_981_ = lean_box(0);
v___x_982_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__7(v_levelParams_980_, v___x_981_);
v___x_983_ = l_Lean_mkConst(v_constName_971_, v___x_982_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_983_);
v___x_985_ = v___x_978_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec(v_constName_971_);
v_a_988_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_975_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_975_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5___boxed(lean_object* v_constName_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(v_constName_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(lean_object* v_t_1001_, lean_object* v___y_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v_infoState_1005_; uint8_t v_enabled_1006_; 
v___x_1004_ = lean_st_ref_get(v___y_1002_);
v_infoState_1005_ = lean_ctor_get(v___x_1004_, 8);
lean_inc_ref(v_infoState_1005_);
lean_dec(v___x_1004_);
v_enabled_1006_ = lean_ctor_get_uint8(v_infoState_1005_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1005_);
if (v_enabled_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; 
lean_dec_ref(v_t_1001_);
v___x_1007_ = lean_box(0);
v___x_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_1007_);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v_infoState_1010_; lean_object* v_env_1011_; lean_object* v_messages_1012_; lean_object* v_scopes_1013_; lean_object* v_usedQuotCtxts_1014_; lean_object* v_nextMacroScope_1015_; lean_object* v_maxRecDepth_1016_; lean_object* v_ngen_1017_; lean_object* v_auxDeclNGen_1018_; lean_object* v_traceState_1019_; lean_object* v_snapshotTasks_1020_; lean_object* v_prevLinterStates_1021_; lean_object* v_codeQualityEntryTasks_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1044_; 
v___x_1009_ = lean_st_ref_take(v___y_1002_);
v_infoState_1010_ = lean_ctor_get(v___x_1009_, 8);
v_env_1011_ = lean_ctor_get(v___x_1009_, 0);
v_messages_1012_ = lean_ctor_get(v___x_1009_, 1);
v_scopes_1013_ = lean_ctor_get(v___x_1009_, 2);
v_usedQuotCtxts_1014_ = lean_ctor_get(v___x_1009_, 3);
v_nextMacroScope_1015_ = lean_ctor_get(v___x_1009_, 4);
v_maxRecDepth_1016_ = lean_ctor_get(v___x_1009_, 5);
v_ngen_1017_ = lean_ctor_get(v___x_1009_, 6);
v_auxDeclNGen_1018_ = lean_ctor_get(v___x_1009_, 7);
v_traceState_1019_ = lean_ctor_get(v___x_1009_, 9);
v_snapshotTasks_1020_ = lean_ctor_get(v___x_1009_, 10);
v_prevLinterStates_1021_ = lean_ctor_get(v___x_1009_, 11);
v_codeQualityEntryTasks_1022_ = lean_ctor_get(v___x_1009_, 12);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1024_ = v___x_1009_;
v_isShared_1025_ = v_isSharedCheck_1044_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1022_);
lean_inc(v_prevLinterStates_1021_);
lean_inc(v_snapshotTasks_1020_);
lean_inc(v_traceState_1019_);
lean_inc(v_infoState_1010_);
lean_inc(v_auxDeclNGen_1018_);
lean_inc(v_ngen_1017_);
lean_inc(v_maxRecDepth_1016_);
lean_inc(v_nextMacroScope_1015_);
lean_inc(v_usedQuotCtxts_1014_);
lean_inc(v_scopes_1013_);
lean_inc(v_messages_1012_);
lean_inc(v_env_1011_);
lean_dec(v___x_1009_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1044_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
uint8_t v_enabled_1026_; lean_object* v_assignment_1027_; lean_object* v_lazyAssignment_1028_; lean_object* v_trees_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1043_; 
v_enabled_1026_ = lean_ctor_get_uint8(v_infoState_1010_, sizeof(void*)*3);
v_assignment_1027_ = lean_ctor_get(v_infoState_1010_, 0);
v_lazyAssignment_1028_ = lean_ctor_get(v_infoState_1010_, 1);
v_trees_1029_ = lean_ctor_get(v_infoState_1010_, 2);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_infoState_1010_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1031_ = v_infoState_1010_;
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_trees_1029_);
lean_inc(v_lazyAssignment_1028_);
lean_inc(v_assignment_1027_);
lean_dec(v_infoState_1010_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1043_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1033_ = lean_box(0);
v___x_1034_ = l_Lean_PersistentArray_push___redArg(v_trees_1029_, v_t_1001_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 2, v___x_1034_);
v___x_1036_ = v___x_1031_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_assignment_1027_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_lazyAssignment_1028_);
lean_ctor_set(v_reuseFailAlloc_1042_, 2, v___x_1034_);
lean_ctor_set_uint8(v_reuseFailAlloc_1042_, sizeof(void*)*3, v_enabled_1026_);
v___x_1036_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 8, v___x_1036_);
v___x_1038_ = v___x_1024_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_env_1011_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_messages_1012_);
lean_ctor_set(v_reuseFailAlloc_1041_, 2, v_scopes_1013_);
lean_ctor_set(v_reuseFailAlloc_1041_, 3, v_usedQuotCtxts_1014_);
lean_ctor_set(v_reuseFailAlloc_1041_, 4, v_nextMacroScope_1015_);
lean_ctor_set(v_reuseFailAlloc_1041_, 5, v_maxRecDepth_1016_);
lean_ctor_set(v_reuseFailAlloc_1041_, 6, v_ngen_1017_);
lean_ctor_set(v_reuseFailAlloc_1041_, 7, v_auxDeclNGen_1018_);
lean_ctor_set(v_reuseFailAlloc_1041_, 8, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1041_, 9, v_traceState_1019_);
lean_ctor_set(v_reuseFailAlloc_1041_, 10, v_snapshotTasks_1020_);
lean_ctor_set(v_reuseFailAlloc_1041_, 11, v_prevLinterStates_1021_);
lean_ctor_set(v_reuseFailAlloc_1041_, 12, v_codeQualityEntryTasks_1022_);
v___x_1038_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = lean_st_ref_put(v___y_1002_, v___x_1038_);
v___x_1040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1040_, 0, v___x_1033_);
return v___x_1040_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v_t_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v_t_1045_, v___y_1046_);
lean_dec(v___y_1046_);
return v_res_1048_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1049_ = lean_unsigned_to_nat(32u);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_1049_);
v___x_1051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1051_, 0, v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1(void){
_start:
{
size_t v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1052_ = ((size_t)5ULL);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_unsigned_to_nat(32u);
v___x_1055_ = lean_mk_empty_array_with_capacity(v___x_1054_);
v___x_1056_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__0);
v___x_1057_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v___x_1055_);
lean_ctor_set(v___x_1057_, 2, v___x_1053_);
lean_ctor_set(v___x_1057_, 3, v___x_1053_);
lean_ctor_set_usize(v___x_1057_, 4, v___x_1052_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(lean_object* v_t_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
lean_object* v___x_1062_; lean_object* v_infoState_1063_; uint8_t v_enabled_1064_; 
v___x_1062_ = lean_st_ref_get(v___y_1060_);
v_infoState_1063_ = lean_ctor_get(v___x_1062_, 8);
lean_inc_ref(v_infoState_1063_);
lean_dec(v___x_1062_);
v_enabled_1064_ = lean_ctor_get_uint8(v_infoState_1063_, sizeof(void*)*3);
lean_dec_ref(v_infoState_1063_);
if (v_enabled_1064_ == 0)
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
lean_dec_ref(v_t_1058_);
v___x_1065_ = lean_box(0);
v___x_1066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
return v___x_1066_;
}
else
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_obj_once(&l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1, &l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1_once, _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___closed__1);
v___x_1068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1068_, 0, v_t_1058_);
lean_ctor_set(v___x_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v___x_1068_, v___y_1060_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6___boxed(lean_object* v_t_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(v_t_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(lean_object* v_stx_1075_, lean_object* v_n_1076_, lean_object* v_expectedType_x3f_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5(v_n_1076_, v___y_1078_, v___y_1079_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
lean_ctor_set(v___x_1084_, 1, v_stx_1075_);
v___x_1085_ = l_Lean_LocalContext_empty;
v___x_1086_ = 0;
v___x_1087_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1087_, 0, v___x_1084_);
lean_ctor_set(v___x_1087_, 1, v___x_1085_);
lean_ctor_set(v___x_1087_, 2, v_expectedType_x3f_1077_);
lean_ctor_set(v___x_1087_, 3, v_a_1082_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*4, v___x_1086_);
lean_ctor_set_uint8(v___x_1087_, sizeof(void*)*4 + 1, v___x_1086_);
v___x_1088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
v___x_1089_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6(v___x_1088_, v___y_1078_, v___y_1079_);
return v___x_1089_;
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_dec(v_expectedType_x3f_1077_);
lean_dec(v_stx_1075_);
v_a_1090_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1081_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1081_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3___boxed(lean_object* v_stx_1098_, lean_object* v_n_1099_, lean_object* v_expectedType_x3f_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(v_stx_1098_, v_n_1099_, v_expectedType_x3f_1100_, v___y_1101_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1101_);
return v_res_1104_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1(void){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = ((lean_object*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__0));
v___x_1107_ = l_Lean_stringToMessageData(v___x_1106_);
return v___x_1107_;
}
}
static lean_object* _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__2));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1(lean_object* v_declName_1111_, lean_object* v_docString_1112_, lean_object* v___y_1113_, lean_object* v___y_1114_){
_start:
{
lean_object* v___y_1117_; lean_object* v___x_1144_; lean_object* v_env_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_st_ref_get(v___y_1114_);
v_env_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc_ref(v_env_1145_);
lean_dec(v___x_1144_);
v___x_1146_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1145_, v_declName_1111_);
lean_dec_ref(v_env_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
v___y_1117_ = v___y_1114_;
goto v___jp_1116_;
}
else
{
uint8_t v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
lean_dec_ref_known(v___x_1146_, 1);
lean_dec_ref(v_docString_1112_);
v___x_1147_ = 0;
v___x_1148_ = lean_obj_once(&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1, &l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1_once, _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__1);
v___x_1149_ = l_Lean_MessageData_ofConstName(v_declName_1111_, v___x_1147_);
v___x_1150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1148_);
lean_ctor_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_obj_once(&l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3, &l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3_once, _init_l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___closed__3);
v___x_1152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
lean_ctor_set(v___x_1152_, 1, v___x_1151_);
v___x_1153_ = l_Lean_throwError___at___00Lean_PostprocessTraces_findStoredTrace_spec__0___redArg(v___x_1152_, v___y_1113_, v___y_1114_);
return v___x_1153_;
}
v___jp_1116_:
{
lean_object* v___x_1118_; lean_object* v_env_1119_; lean_object* v_nextMacroScope_1120_; lean_object* v_ngen_1121_; lean_object* v_auxDeclNGen_1122_; lean_object* v_traceState_1123_; lean_object* v_recordedDeps_1124_; lean_object* v_messages_1125_; lean_object* v_infoState_1126_; lean_object* v_snapshotTasks_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1142_; 
v___x_1118_ = lean_st_ref_take(v___y_1117_);
v_env_1119_ = lean_ctor_get(v___x_1118_, 0);
v_nextMacroScope_1120_ = lean_ctor_get(v___x_1118_, 1);
v_ngen_1121_ = lean_ctor_get(v___x_1118_, 2);
v_auxDeclNGen_1122_ = lean_ctor_get(v___x_1118_, 3);
v_traceState_1123_ = lean_ctor_get(v___x_1118_, 4);
v_recordedDeps_1124_ = lean_ctor_get(v___x_1118_, 6);
v_messages_1125_ = lean_ctor_get(v___x_1118_, 7);
v_infoState_1126_ = lean_ctor_get(v___x_1118_, 8);
v_snapshotTasks_1127_ = lean_ctor_get(v___x_1118_, 9);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1142_ == 0)
{
lean_object* v_unused_1143_; 
v_unused_1143_ = lean_ctor_get(v___x_1118_, 5);
lean_dec(v_unused_1143_);
v___x_1129_ = v___x_1118_;
v_isShared_1130_ = v_isSharedCheck_1142_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_snapshotTasks_1127_);
lean_inc(v_infoState_1126_);
lean_inc(v_messages_1125_);
lean_inc(v_recordedDeps_1124_);
lean_inc(v_traceState_1123_);
lean_inc(v_auxDeclNGen_1122_);
lean_inc(v_ngen_1121_);
lean_inc(v_nextMacroScope_1120_);
lean_inc(v_env_1119_);
lean_dec(v___x_1118_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1142_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1138_; 
v___x_1131_ = lean_box(0);
v___x_1132_ = l_Lean_docStringExt;
v___x_1133_ = l_String_removeLeadingSpaces(v_docString_1112_);
v___x_1134_ = 1;
v___x_1135_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1132_, v_env_1119_, v_declName_1111_, v___x_1133_, v___x_1134_);
v___x_1136_ = lean_obj_once(&l_Lean_PostprocessTraces_storeTraces___redArg___closed__1, &l_Lean_PostprocessTraces_storeTraces___redArg___closed__1_once, _init_l_Lean_PostprocessTraces_storeTraces___redArg___closed__1);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 5, v___x_1136_);
lean_ctor_set(v___x_1129_, 0, v___x_1135_);
v___x_1138_ = v___x_1129_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1135_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_nextMacroScope_1120_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_ngen_1121_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_auxDeclNGen_1122_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_traceState_1123_);
lean_ctor_set(v_reuseFailAlloc_1141_, 5, v___x_1136_);
lean_ctor_set(v_reuseFailAlloc_1141_, 6, v_recordedDeps_1124_);
lean_ctor_set(v_reuseFailAlloc_1141_, 7, v_messages_1125_);
lean_ctor_set(v_reuseFailAlloc_1141_, 8, v_infoState_1126_);
lean_ctor_set(v_reuseFailAlloc_1141_, 9, v_snapshotTasks_1127_);
v___x_1138_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_st_ref_put(v___y_1117_, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1131_);
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___boxed(lean_object* v_declName_1154_, lean_object* v_docString_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1(v_declName_1154_, v_docString_1155_, v___y_1156_, v___y_1157_);
lean_dec(v___y_1157_);
lean_dec_ref(v___y_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(lean_object* v_stx_1160_, lean_object* v___y_1161_){
_start:
{
uint8_t v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = 0;
v___x_1164_ = l_Lean_Syntax_getRange_x3f(v_stx_1160_, v___x_1163_);
if (lean_obj_tag(v___x_1164_) == 1)
{
lean_object* v_val_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1177_; 
v_val_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1177_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_val_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1177_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_fileMap_1169_; lean_object* v_start_1170_; lean_object* v_stop_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v_fileMap_1169_ = lean_ctor_get(v___y_1161_, 1);
v_start_1170_ = lean_ctor_get(v_val_1165_, 0);
lean_inc(v_start_1170_);
v_stop_1171_ = lean_ctor_get(v_val_1165_, 1);
lean_inc(v_stop_1171_);
lean_dec(v_val_1165_);
lean_inc_ref(v_fileMap_1169_);
v___x_1172_ = l_Lean_DeclarationRange_ofStringPositions(v_fileMap_1169_, v_start_1170_, v_stop_1171_);
lean_dec(v_stop_1171_);
lean_dec(v_start_1170_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 0, v___x_1172_);
v___x_1174_ = v___x_1167_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v___x_1172_);
v___x_1174_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1174_);
return v___x_1175_;
}
}
}
else
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec(v___x_1164_);
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg___boxed(lean_object* v_stx_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_stx_1180_, v___y_1181_);
lean_dec_ref(v___y_1181_);
lean_dec(v_stx_1180_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(lean_object* v_declName_1184_, lean_object* v_declRanges_1185_, lean_object* v___y_1186_){
_start:
{
uint8_t v___x_1188_; 
v___x_1188_ = l_Lean_Name_isAnonymous(v_declName_1184_);
if (v___x_1188_ == 0)
{
lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v_env_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; uint8_t v___x_1194_; 
v___x_1189_ = l_Lean_instInhabitedDeclarationRanges_default;
v___x_1190_ = lean_st_ref_get(v___y_1186_);
v_env_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc_ref(v_env_1191_);
lean_dec(v___x_1190_);
v___x_1192_ = l_Lean_declRangeExt;
v___x_1193_ = lean_box(1);
lean_inc(v_declName_1184_);
v___x_1194_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_1189_, v___x_1192_, v_env_1191_, v_declName_1184_, v___x_1193_);
if (v___x_1194_ == 0)
{
lean_object* v___x_1195_; lean_object* v_env_1196_; lean_object* v_messages_1197_; lean_object* v_scopes_1198_; lean_object* v_usedQuotCtxts_1199_; lean_object* v_nextMacroScope_1200_; lean_object* v_maxRecDepth_1201_; lean_object* v_ngen_1202_; lean_object* v_auxDeclNGen_1203_; lean_object* v_infoState_1204_; lean_object* v_traceState_1205_; lean_object* v_snapshotTasks_1206_; lean_object* v_prevLinterStates_1207_; lean_object* v_codeQualityEntryTasks_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1219_; 
v___x_1195_ = lean_st_ref_take(v___y_1186_);
v_env_1196_ = lean_ctor_get(v___x_1195_, 0);
v_messages_1197_ = lean_ctor_get(v___x_1195_, 1);
v_scopes_1198_ = lean_ctor_get(v___x_1195_, 2);
v_usedQuotCtxts_1199_ = lean_ctor_get(v___x_1195_, 3);
v_nextMacroScope_1200_ = lean_ctor_get(v___x_1195_, 4);
v_maxRecDepth_1201_ = lean_ctor_get(v___x_1195_, 5);
v_ngen_1202_ = lean_ctor_get(v___x_1195_, 6);
v_auxDeclNGen_1203_ = lean_ctor_get(v___x_1195_, 7);
v_infoState_1204_ = lean_ctor_get(v___x_1195_, 8);
v_traceState_1205_ = lean_ctor_get(v___x_1195_, 9);
v_snapshotTasks_1206_ = lean_ctor_get(v___x_1195_, 10);
v_prevLinterStates_1207_ = lean_ctor_get(v___x_1195_, 11);
v_codeQualityEntryTasks_1208_ = lean_ctor_get(v___x_1195_, 12);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1210_ = v___x_1195_;
v_isShared_1211_ = v_isSharedCheck_1219_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1208_);
lean_inc(v_prevLinterStates_1207_);
lean_inc(v_snapshotTasks_1206_);
lean_inc(v_traceState_1205_);
lean_inc(v_infoState_1204_);
lean_inc(v_auxDeclNGen_1203_);
lean_inc(v_ngen_1202_);
lean_inc(v_maxRecDepth_1201_);
lean_inc(v_nextMacroScope_1200_);
lean_inc(v_usedQuotCtxts_1199_);
lean_inc(v_scopes_1198_);
lean_inc(v_messages_1197_);
lean_inc(v_env_1196_);
lean_dec(v___x_1195_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1219_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1212_ = lean_box(0);
v___x_1213_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1192_, v_env_1196_, v_declName_1184_, v_declRanges_1185_, v___x_1194_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v___x_1213_);
v___x_1215_ = v___x_1210_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v_messages_1197_);
lean_ctor_set(v_reuseFailAlloc_1218_, 2, v_scopes_1198_);
lean_ctor_set(v_reuseFailAlloc_1218_, 3, v_usedQuotCtxts_1199_);
lean_ctor_set(v_reuseFailAlloc_1218_, 4, v_nextMacroScope_1200_);
lean_ctor_set(v_reuseFailAlloc_1218_, 5, v_maxRecDepth_1201_);
lean_ctor_set(v_reuseFailAlloc_1218_, 6, v_ngen_1202_);
lean_ctor_set(v_reuseFailAlloc_1218_, 7, v_auxDeclNGen_1203_);
lean_ctor_set(v_reuseFailAlloc_1218_, 8, v_infoState_1204_);
lean_ctor_set(v_reuseFailAlloc_1218_, 9, v_traceState_1205_);
lean_ctor_set(v_reuseFailAlloc_1218_, 10, v_snapshotTasks_1206_);
lean_ctor_set(v_reuseFailAlloc_1218_, 11, v_prevLinterStates_1207_);
lean_ctor_set(v_reuseFailAlloc_1218_, 12, v_codeQualityEntryTasks_1208_);
v___x_1215_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_st_ref_put(v___y_1186_, v___x_1215_);
v___x_1217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1212_);
return v___x_1217_;
}
}
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec_ref(v_declRanges_1185_);
lean_dec(v_declName_1184_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
return v___x_1221_;
}
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; 
lean_dec_ref(v_declRanges_1185_);
lean_dec(v_declName_1184_);
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1222_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg___boxed(lean_object* v_declName_1224_, lean_object* v_declRanges_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1224_, v_declRanges_1225_, v___y_1226_);
lean_dec(v___y_1226_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(lean_object* v_declName_1229_, lean_object* v_rangeStx_1230_, lean_object* v_selectionRangeStx_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v___x_1235_; lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1252_; 
v___x_1235_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_rangeStx_1230_, v___y_1232_);
v_a_1236_ = lean_ctor_get(v___x_1235_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1235_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1238_ = v___x_1235_;
v_isShared_1239_ = v_isSharedCheck_1252_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1235_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1252_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
if (lean_obj_tag(v_a_1236_) == 1)
{
lean_object* v_val_1240_; lean_object* v_a_1242_; lean_object* v___x_1245_; lean_object* v_a_1246_; 
lean_del_object(v___x_1238_);
v_val_1240_ = lean_ctor_get(v_a_1236_, 0);
lean_inc(v_val_1240_);
lean_dec_ref_known(v_a_1236_, 1);
v___x_1245_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_selectionRangeStx_1231_, v___y_1232_);
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1245_);
if (lean_obj_tag(v_a_1246_) == 0)
{
lean_inc(v_val_1240_);
v_a_1242_ = v_val_1240_;
goto v___jp_1241_;
}
else
{
lean_object* v_val_1247_; 
v_val_1247_ = lean_ctor_get(v_a_1246_, 0);
lean_inc(v_val_1247_);
lean_dec_ref_known(v_a_1246_, 1);
v_a_1242_ = v_val_1247_;
goto v___jp_1241_;
}
v___jp_1241_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_val_1240_);
lean_ctor_set(v___x_1243_, 1, v_a_1242_);
v___x_1244_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1229_, v___x_1243_, v___y_1233_);
return v___x_1244_;
}
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_dec(v_a_1236_);
lean_dec(v_declName_1229_);
v___x_1248_ = lean_box(0);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 0, v___x_1248_);
v___x_1250_ = v___x_1238_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2___boxed(lean_object* v_declName_1253_, lean_object* v_rangeStx_1254_, lean_object* v_selectionRangeStx_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(v_declName_1253_, v_rangeStx_1254_, v_selectionRangeStx_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v_selectionRangeStx_1255_);
lean_dec(v_rangeStx_1254_);
return v_res_1259_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_box(0);
v___x_1267_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__2));
v___x_1268_ = l_Lean_mkConst(v___x_1267_, v___x_1266_);
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1274_ = lean_box(0);
v___x_1275_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__5));
v___x_1276_ = l_Lean_mkConst(v___x_1275_, v___x_1274_);
return v___x_1276_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1277_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__6);
v___x_1278_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__3);
v___x_1279_ = l_Lean_Expr_app___override(v___x_1278_, v___x_1277_);
return v___x_1279_;
}
}
static lean_object* _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1285_ = lean_box(0);
v___x_1286_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__9));
v___x_1287_ = l_Lean_mkConst(v___x_1286_, v___x_1285_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs(lean_object* v_x_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_PostprocessTraces_storeTracesAsCmd___closed__3));
lean_inc(v_x_1293_);
v___x_1298_ = l_Lean_Syntax_isOfKind(v_x_1293_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; 
lean_dec(v_x_1293_);
v___x_1299_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_1299_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_id_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_env_1307_; lean_object* v___x_1308_; 
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_unsigned_to_nat(1u);
v_id_1302_ = l_Lean_Syntax_getArg(v_x_1293_, v___x_1301_);
v___x_1303_ = lean_unsigned_to_nat(3u);
v___x_1304_ = l_Lean_Syntax_getArg(v_x_1293_, v___x_1303_);
lean_dec(v_x_1293_);
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_st_ref_get(v_a_1295_);
v_env_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc_ref(v_env_1307_);
lean_dec(v___x_1306_);
v___x_1308_ = l_Lean_Elab_Command_getScope___redArg(v_a_1295_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v_currNamespace_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___y_1315_; lean_object* v___x_1318_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v_currNamespace_1310_ = lean_ctor_get(v_a_1309_, 2);
lean_inc(v_currNamespace_1310_);
lean_dec(v_a_1309_);
v___x_1311_ = l_Lean_TSyntax_getId(v_id_1302_);
lean_inc(v___x_1311_);
v___x_1312_ = l_Lean_Name_append(v_currNamespace_1310_, v___x_1311_);
v___x_1313_ = l_Lean_mkPrivateName(v_env_1307_, v___x_1312_);
lean_dec_ref(v_env_1307_);
v___x_1318_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_1304_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; lean_object* v_env_1321_; lean_object* v_messages_1322_; lean_object* v_scopes_1323_; lean_object* v_usedQuotCtxts_1324_; lean_object* v_nextMacroScope_1325_; lean_object* v_maxRecDepth_1326_; lean_object* v_ngen_1327_; lean_object* v_auxDeclNGen_1328_; lean_object* v_infoState_1329_; lean_object* v_traceState_1330_; lean_object* v_snapshotTasks_1331_; lean_object* v_prevLinterStates_1332_; lean_object* v_codeQualityEntryTasks_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1406_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
v___x_1320_ = lean_st_ref_take(v_a_1295_);
v_env_1321_ = lean_ctor_get(v___x_1320_, 0);
v_messages_1322_ = lean_ctor_get(v___x_1320_, 1);
v_scopes_1323_ = lean_ctor_get(v___x_1320_, 2);
v_usedQuotCtxts_1324_ = lean_ctor_get(v___x_1320_, 3);
v_nextMacroScope_1325_ = lean_ctor_get(v___x_1320_, 4);
v_maxRecDepth_1326_ = lean_ctor_get(v___x_1320_, 5);
v_ngen_1327_ = lean_ctor_get(v___x_1320_, 6);
v_auxDeclNGen_1328_ = lean_ctor_get(v___x_1320_, 7);
v_infoState_1329_ = lean_ctor_get(v___x_1320_, 8);
v_traceState_1330_ = lean_ctor_get(v___x_1320_, 9);
v_snapshotTasks_1331_ = lean_ctor_get(v___x_1320_, 10);
v_prevLinterStates_1332_ = lean_ctor_get(v___x_1320_, 11);
v_codeQualityEntryTasks_1333_ = lean_ctor_get(v___x_1320_, 12);
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1335_ = v___x_1320_;
v_isShared_1336_ = v_isSharedCheck_1406_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1333_);
lean_inc(v_prevLinterStates_1332_);
lean_inc(v_snapshotTasks_1331_);
lean_inc(v_traceState_1330_);
lean_inc(v_infoState_1329_);
lean_inc(v_auxDeclNGen_1328_);
lean_inc(v_ngen_1327_);
lean_inc(v_maxRecDepth_1326_);
lean_inc(v_nextMacroScope_1325_);
lean_inc(v_usedQuotCtxts_1324_);
lean_inc(v_scopes_1323_);
lean_inc(v_messages_1322_);
lean_inc(v_env_1321_);
lean_dec(v___x_1320_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1406_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___y_1338_; lean_object* v___x_1397_; uint8_t v___x_1398_; 
v___x_1397_ = lean_array_get_size(v_a_1319_);
v___x_1398_ = lean_nat_dec_lt(v___x_1300_, v___x_1397_);
if (v___x_1398_ == 0)
{
v___y_1338_ = v_messages_1322_;
goto v___jp_1337_;
}
else
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_nat_dec_le(v___x_1397_, v___x_1397_);
if (v___x_1399_ == 0)
{
if (v___x_1398_ == 0)
{
v___y_1338_ = v_messages_1322_;
goto v___jp_1337_;
}
else
{
size_t v___x_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = lean_usize_of_nat(v___x_1397_);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_a_1319_, v___x_1400_, v___x_1401_, v_messages_1322_);
v___y_1338_ = v___x_1402_;
goto v___jp_1337_;
}
}
else
{
size_t v___x_1403_; size_t v___x_1404_; lean_object* v___x_1405_; 
v___x_1403_ = ((size_t)0ULL);
v___x_1404_ = lean_usize_of_nat(v___x_1397_);
v___x_1405_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__5(v_a_1319_, v___x_1403_, v___x_1404_, v_messages_1322_);
v___y_1338_ = v___x_1405_;
goto v___jp_1337_;
}
}
v___jp_1337_:
{
lean_object* v___x_1340_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 1, v___y_1338_);
v___x_1340_ = v___x_1335_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_env_1321_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v___y_1338_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_scopes_1323_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_usedQuotCtxts_1324_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_nextMacroScope_1325_);
lean_ctor_set(v_reuseFailAlloc_1396_, 5, v_maxRecDepth_1326_);
lean_ctor_set(v_reuseFailAlloc_1396_, 6, v_ngen_1327_);
lean_ctor_set(v_reuseFailAlloc_1396_, 7, v_auxDeclNGen_1328_);
lean_ctor_set(v_reuseFailAlloc_1396_, 8, v_infoState_1329_);
lean_ctor_set(v_reuseFailAlloc_1396_, 9, v_traceState_1330_);
lean_ctor_set(v_reuseFailAlloc_1396_, 10, v_snapshotTasks_1331_);
lean_ctor_set(v_reuseFailAlloc_1396_, 11, v_prevLinterStates_1332_);
lean_ctor_set(v_reuseFailAlloc_1396_, 12, v_codeQualityEntryTasks_1333_);
v___x_1340_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1341_ = lean_st_ref_put(v_a_1295_, v___x_1340_);
v___x_1342_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__7);
lean_inc_n(v___x_1313_, 3);
v___x_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1313_);
lean_ctor_set(v___x_1343_, 1, v___x_1305_);
lean_ctor_set(v___x_1343_, 2, v___x_1342_);
v___x_1344_ = lean_obj_once(&l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10, &l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10_once, _init_l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__10);
v___x_1345_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v___x_1313_);
v___x_1346_ = l_Lean_Expr_app___override(v___x_1344_, v___x_1345_);
v___x_1347_ = lean_box(1);
v___x_1348_ = 1;
v___x_1349_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1313_);
lean_ctor_set(v___x_1349_, 1, v___x_1305_);
v___x_1350_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_1350_, 0, v___x_1343_);
lean_ctor_set(v___x_1350_, 1, v___x_1346_);
lean_ctor_set(v___x_1350_, 2, v___x_1347_);
lean_ctor_set(v___x_1350_, 3, v___x_1349_);
lean_ctor_set_uint8(v___x_1350_, sizeof(void*)*4, v___x_1348_);
v___x_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1350_);
v___x_1352_ = lean_box(v___x_1298_);
v___x_1353_ = lean_box(v___x_1298_);
v___x_1354_ = lean_alloc_closure((void*)(l_Lean_addAndCompile___boxed), 6, 3);
lean_closure_set(v___x_1354_, 0, v___x_1351_);
lean_closure_set(v___x_1354_, 1, v___x_1352_);
lean_closure_set(v___x_1354_, 2, v___x_1353_);
v___x_1355_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1354_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_object* v_fileName_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref_known(v___x_1355_, 1);
v_fileName_1356_ = lean_ctor_get(v_a_1294_, 0);
v___x_1357_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__11));
v___x_1358_ = lean_string_append(v___x_1357_, v_fileName_1356_);
v___x_1359_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__12));
v___x_1360_ = lean_string_append(v___x_1358_, v___x_1359_);
v___x_1361_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_1311_, v___x_1298_);
v___x_1362_ = lean_string_append(v___x_1360_, v___x_1361_);
v___x_1363_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__13));
v___x_1364_ = lean_string_append(v___x_1362_, v___x_1363_);
v___x_1365_ = lean_string_append(v___x_1364_, v___x_1361_);
v___x_1366_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__14));
v___x_1367_ = lean_string_append(v___x_1365_, v___x_1366_);
v___x_1368_ = lean_string_append(v___x_1367_, v___x_1361_);
lean_dec_ref(v___x_1361_);
v___x_1369_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___closed__15));
v___x_1370_ = lean_string_append(v___x_1368_, v___x_1369_);
lean_inc(v___x_1313_);
v___x_1371_ = lean_alloc_closure((void*)(l_Lean_addDocStringCore___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__1___boxed), 5, 2);
lean_closure_set(v___x_1371_, 0, v___x_1313_);
lean_closure_set(v___x_1371_, 1, v___x_1370_);
v___x_1372_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1371_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1372_) == 0)
{
lean_object* v___x_1373_; 
lean_dec_ref_known(v___x_1372_, 1);
v___x_1373_ = l_Lean_Elab_Command_getRef___redArg(v_a_1294_);
if (lean_obj_tag(v___x_1373_) == 0)
{
lean_object* v_a_1374_; lean_object* v___x_1375_; 
v_a_1374_ = lean_ctor_get(v___x_1373_, 0);
lean_inc(v_a_1374_);
lean_dec_ref_known(v___x_1373_, 1);
lean_inc(v___x_1313_);
v___x_1375_ = l_Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2(v___x_1313_, v_a_1374_, v_id_1302_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1374_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref_known(v___x_1375_, 1);
v___x_1376_ = lean_box(0);
lean_inc(v___x_1313_);
v___x_1377_ = l_Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3(v_id_1302_, v___x_1313_, v___x_1376_, v_a_1294_, v_a_1295_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; uint8_t v___x_1380_; 
lean_dec_ref_known(v___x_1377_, 1);
v___x_1378_ = lean_array_get_size(v_a_1319_);
v___x_1379_ = ((lean_object*)(l_Array_filterMapM___at___00Lean_PostprocessTraces_StoredTrace_postprocess_spec__0___closed__0));
v___x_1380_ = lean_nat_dec_lt(v___x_1300_, v___x_1378_);
if (v___x_1380_ == 0)
{
lean_dec(v_a_1319_);
v___y_1315_ = v___x_1379_;
goto v___jp_1314_;
}
else
{
uint8_t v___x_1381_; 
v___x_1381_ = lean_nat_dec_le(v___x_1378_, v___x_1378_);
if (v___x_1381_ == 0)
{
if (v___x_1380_ == 0)
{
lean_dec(v_a_1319_);
v___y_1315_ = v___x_1379_;
goto v___jp_1314_;
}
else
{
size_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = lean_usize_of_nat(v___x_1378_);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_a_1319_, v___x_1382_, v___x_1383_, v___x_1379_);
lean_dec(v_a_1319_);
v___y_1315_ = v___x_1384_;
goto v___jp_1314_;
}
}
else
{
size_t v___x_1385_; size_t v___x_1386_; lean_object* v___x_1387_; 
v___x_1385_ = ((size_t)0ULL);
v___x_1386_ = lean_usize_of_nat(v___x_1378_);
v___x_1387_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__4(v_a_1319_, v___x_1385_, v___x_1386_, v___x_1379_);
lean_dec(v_a_1319_);
v___y_1315_ = v___x_1387_;
goto v___jp_1314_;
}
}
}
else
{
lean_dec(v_a_1319_);
lean_dec(v___x_1313_);
return v___x_1377_;
}
}
else
{
lean_dec(v_a_1319_);
lean_dec(v___x_1313_);
lean_dec(v_id_1302_);
return v___x_1375_;
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_dec(v_a_1319_);
lean_dec(v___x_1313_);
lean_dec(v_id_1302_);
v_a_1388_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1373_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1373_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
else
{
lean_dec(v_a_1319_);
lean_dec(v___x_1313_);
lean_dec(v_id_1302_);
return v___x_1372_;
}
}
else
{
lean_dec(v_a_1319_);
lean_dec(v___x_1313_);
lean_dec(v___x_1311_);
lean_dec(v_id_1302_);
return v___x_1355_;
}
}
}
}
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v___x_1313_);
lean_dec(v___x_1311_);
lean_dec(v_id_1302_);
v_a_1407_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1318_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1318_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1412_; 
if (v_isShared_1410_ == 0)
{
v___x_1412_ = v___x_1409_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
v___jp_1314_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1316_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_storeTraces___boxed), 5, 2);
lean_closure_set(v___x_1316_, 0, v___x_1313_);
lean_closure_set(v___x_1316_, 1, v___y_1315_);
v___x_1317_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1316_, v_a_1294_, v_a_1295_);
return v___x_1317_;
}
}
else
{
lean_object* v_a_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1422_; 
lean_dec_ref(v_env_1307_);
lean_dec(v___x_1304_);
lean_dec(v_id_1302_);
v_a_1415_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1422_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1422_ == 0)
{
v___x_1417_ = v___x_1308_;
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_a_1415_);
lean_dec(v___x_1308_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1422_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1420_; 
if (v_isShared_1418_ == 0)
{
v___x_1420_ = v___x_1417_;
goto v_reusejp_1419_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
v___x_1420_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1419_;
}
v_reusejp_1419_:
{
return v___x_1420_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabStoreTraceAs___boxed(lean_object* v_x_1423_, lean_object* v_a_1424_, lean_object* v_a_1425_, lean_object* v_a_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_Elab_PostprocessTraces_elabStoreTraceAs(v_x_1423_, v_a_1424_, v_a_1425_);
lean_dec(v_a_1425_);
lean_dec_ref(v_a_1424_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2(lean_object* v_stx_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___redArg(v_stx_1428_, v___y_1429_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2___boxed(lean_object* v_stx_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v_res_1437_; 
v_res_1437_ = l_Lean_Elab_getDeclarationRange_x3f___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__2(v_stx_1433_, v___y_1434_, v___y_1435_);
lean_dec(v___y_1435_);
lean_dec_ref(v___y_1434_);
lean_dec(v_stx_1433_);
return v_res_1437_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3(lean_object* v_declName_1438_, lean_object* v_declRanges_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___redArg(v_declName_1438_, v_declRanges_1439_, v___y_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3___boxed(lean_object* v_declName_1444_, lean_object* v_declRanges_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Lean_addDeclarationRanges___at___00Lean_Elab_addDeclarationRangesFromSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__2_spec__3(v_declName_1444_, v_declRanges_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9(lean_object* v_t_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___redArg(v_t_1450_, v___y_1452_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9___boxed(lean_object* v_t_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__6_spec__9(v_t_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9(lean_object* v_00_u03b1_1460_, lean_object* v_constName_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___redArg(v_constName_1461_, v___y_1462_, v___y_1463_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9___boxed(lean_object* v_00_u03b1_1466_, lean_object* v_constName_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9(v_00_u03b1_1466_, v_constName_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12(lean_object* v_00_u03b1_1472_, lean_object* v_ref_1473_, lean_object* v_constName_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg(v_ref_1473_, v_constName_1474_, v___y_1475_, v___y_1476_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___boxed(lean_object* v_00_u03b1_1479_, lean_object* v_ref_1480_, lean_object* v_constName_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_){
_start:
{
lean_object* v_res_1485_; 
v_res_1485_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12(v_00_u03b1_1479_, v_ref_1480_, v_constName_1481_, v___y_1482_, v___y_1483_);
lean_dec(v___y_1483_);
lean_dec_ref(v___y_1482_);
lean_dec(v_ref_1480_);
return v_res_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14(lean_object* v_00_u03b1_1486_, lean_object* v_ref_1487_, lean_object* v_msg_1488_, lean_object* v_declHint_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___redArg(v_ref_1487_, v_msg_1488_, v_declHint_1489_, v___y_1490_, v___y_1491_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14___boxed(lean_object* v_00_u03b1_1494_, lean_object* v_ref_1495_, lean_object* v_msg_1496_, lean_object* v_declHint_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14(v_00_u03b1_1494_, v_ref_1495_, v_msg_1496_, v_declHint_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v_ref_1495_);
return v_res_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16(lean_object* v_msg_1502_, lean_object* v_declHint_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___redArg(v_msg_1502_, v_declHint_1503_, v___y_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16___boxed(lean_object* v_msg_1508_, lean_object* v_declHint_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__15_spec__16(v_msg_1508_, v_declHint_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16(lean_object* v_00_u03b1_1514_, lean_object* v_ref_1515_, lean_object* v_msg_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_ref_1515_, v_msg_1516_, v___y_1517_, v___y_1518_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___boxed(lean_object* v_00_u03b1_1521_, lean_object* v_ref_1522_, lean_object* v_msg_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16(v_00_u03b1_1521_, v_ref_1522_, v_msg_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v_ref_1522_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19(lean_object* v_msgData_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___redArg(v_msgData_1528_, v___y_1530_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19___boxed(lean_object* v_msgData_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_){
_start:
{
lean_object* v_res_1537_; 
v_res_1537_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__19(v_msgData_1533_, v___y_1534_, v___y_1535_);
lean_dec(v___y_1535_);
lean_dec_ref(v___y_1534_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18(lean_object* v_00_u03b1_1538_, lean_object* v_msg_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___redArg(v_msg_1539_, v___y_1540_, v___y_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18___boxed(lean_object* v_00_u03b1_1544_, lean_object* v_msg_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18(v_00_u03b1_1544_, v_msg_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20(lean_object* v_msgData_1550_, lean_object* v_macroStack_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___redArg(v_msgData_1550_, v_macroStack_1551_, v___y_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20___boxed(lean_object* v_msgData_1556_, lean_object* v_macroStack_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16_spec__18_spec__20(v_msgData_1556_, v_macroStack_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace_spec__0(lean_object* v_a_1562_, lean_object* v_a_1563_){
_start:
{
if (lean_obj_tag(v_a_1562_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = l_List_reverse___redArg(v_a_1563_);
return v___x_1564_;
}
else
{
lean_object* v_head_1565_; lean_object* v_tail_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1587_; 
v_head_1565_ = lean_ctor_get(v_a_1562_, 0);
v_tail_1566_ = lean_ctor_get(v_a_1562_, 1);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_a_1562_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1568_ = v_a_1562_;
v_isShared_1569_ = v_isSharedCheck_1587_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_tail_1566_);
lean_inc(v_head_1565_);
lean_dec(v_a_1562_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1587_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v_fst_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1585_; 
v_fst_1570_ = lean_ctor_get(v_head_1565_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v_head_1565_);
if (v_isSharedCheck_1585_ == 0)
{
lean_object* v_unused_1586_; 
v_unused_1586_ = lean_ctor_get(v_head_1565_, 1);
lean_dec(v_unused_1586_);
v___x_1572_ = v_head_1565_;
v_isShared_1573_ = v_isSharedCheck_1585_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_fst_1570_);
lean_dec(v_head_1565_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1585_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1574_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12___redArg___closed__3);
v___x_1575_ = l_Lean_privateToUserName(v_fst_1570_);
v___x_1576_ = l_Lean_MessageData_ofName(v___x_1575_);
if (v_isShared_1573_ == 0)
{
lean_ctor_set_tag(v___x_1572_, 7);
lean_ctor_set(v___x_1572_, 1, v___x_1576_);
lean_ctor_set(v___x_1572_, 0, v___x_1574_);
v___x_1578_ = v___x_1572_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v___x_1576_);
v___x_1578_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
lean_ctor_set(v___x_1579_, 1, v___x_1574_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v_a_1563_);
lean_ctor_set(v___x_1568_, 0, v___x_1579_);
v___x_1581_ = v___x_1568_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1579_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_a_1563_);
v___x_1581_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
v_a_1562_ = v_tail_1566_;
v_a_1563_ = v___x_1581_;
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
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__0));
v___x_1590_ = l_Lean_stringToMessageData(v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__2));
v___x_1593_ = l_Lean_stringToMessageData(v___x_1592_);
return v___x_1593_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__4));
v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
return v___x_1596_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1598_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__6));
v___x_1599_ = l_Lean_stringToMessageData(v___x_1598_);
return v___x_1599_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9(void){
_start:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1601_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__8));
v___x_1602_ = l_Lean_stringToMessageData(v___x_1601_);
return v___x_1602_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12(void){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__11));
v___x_1607_ = l_Lean_MessageData_ofFormat(v___x_1606_);
return v___x_1607_;
}
}
static lean_object* _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = ((lean_object*)(l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__13));
v___x_1610_ = l_Lean_stringToMessageData(v___x_1609_);
return v___x_1610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(lean_object* v_id_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1615_ = lean_box(0);
lean_inc(v_id_1611_);
v___x_1616_ = lean_alloc_closure((void*)(l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo___boxed), 5, 2);
lean_closure_set(v___x_1616_, 0, v_id_1611_);
lean_closure_set(v___x_1616_, 1, v___x_1615_);
v___x_1617_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1616_, v_a_1612_, v_a_1613_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1655_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1620_ = v___x_1617_;
v_isShared_1621_ = v_isSharedCheck_1655_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1655_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v_env_1623_; lean_object* v___x_1624_; 
v___x_1622_ = lean_st_ref_get(v_a_1613_);
v_env_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc_ref(v_env_1623_);
lean_dec(v___x_1622_);
v___x_1624_ = l_Lean_PostprocessTraces_findStoredTrace_x3f(v_env_1623_, v_a_1618_);
lean_dec(v_a_1618_);
if (lean_obj_tag(v___x_1624_) == 1)
{
lean_object* v_val_1625_; lean_object* v___x_1627_; 
lean_dec(v_id_1611_);
v_val_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v___x_1624_, 1);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 0, v_val_1625_);
v___x_1627_ = v___x_1620_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_val_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
else
{
lean_object* v___x_1629_; lean_object* v___y_1631_; lean_object* v_env_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
lean_dec(v___x_1624_);
lean_del_object(v___x_1620_);
v___x_1629_ = lean_st_ref_get(v_a_1613_);
v_env_1645_ = lean_ctor_get(v___x_1629_, 0);
lean_inc_ref(v_env_1645_);
lean_dec(v___x_1629_);
v___x_1646_ = l_Lean_PostprocessTraces_allStoredTraces(v_env_1645_);
v___x_1647_ = lean_box(0);
v___x_1648_ = l_List_mapTR_loop___at___00__private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace_spec__0(v___x_1646_, v___x_1647_);
v___x_1649_ = l_List_isEmpty___redArg(v___x_1648_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1650_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__9);
v___x_1651_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__12);
v___x_1652_ = l_Lean_MessageData_joinSep(v___x_1648_, v___x_1651_);
v___x_1653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1653_, 0, v___x_1650_);
lean_ctor_set(v___x_1653_, 1, v___x_1652_);
v___y_1631_ = v___x_1653_;
goto v___jp_1630_;
}
else
{
lean_object* v___x_1654_; 
lean_dec(v___x_1648_);
v___x_1654_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__14);
v___y_1631_ = v___x_1654_;
goto v___jp_1630_;
}
v___jp_1630_:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1632_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__1);
v___x_1633_ = l_Lean_TSyntax_getId(v_id_1611_);
v___x_1634_ = l_Lean_MessageData_ofName(v___x_1633_);
lean_inc_ref(v___x_1634_);
v___x_1635_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1635_, 0, v___x_1632_);
lean_ctor_set(v___x_1635_, 1, v___x_1634_);
v___x_1636_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__3);
v___x_1637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1637_, 0, v___x_1635_);
lean_ctor_set(v___x_1637_, 1, v___x_1636_);
v___x_1638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1638_, 0, v___x_1637_);
lean_ctor_set(v___x_1638_, 1, v___y_1631_);
v___x_1639_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__5);
v___x_1640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1638_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1640_);
lean_ctor_set(v___x_1641_, 1, v___x_1634_);
v___x_1642_ = lean_obj_once(&l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7, &l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7_once, _init_l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___closed__7);
v___x_1643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1641_);
lean_ctor_set(v___x_1643_, 1, v___x_1642_);
v___x_1644_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Elab_addConstInfo___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__3_spec__5_spec__6_spec__9_spec__12_spec__14_spec__16___redArg(v_id_1611_, v___x_1643_, v_a_1612_, v_a_1613_);
lean_dec(v_id_1611_);
return v___x_1644_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec(v_id_1611_);
v_a_1656_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1617_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1617_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace___boxed(lean_object* v_id_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(v_id_1664_, v_a_1665_, v_a_1666_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
return v_res_1668_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0(uint8_t v_suppressElabErrors_1670_, lean_object* v_x_1671_){
_start:
{
if (lean_obj_tag(v_x_1671_) == 1)
{
lean_object* v_pre_1672_; 
v_pre_1672_ = lean_ctor_get(v_x_1671_, 0);
if (lean_obj_tag(v_pre_1672_) == 0)
{
lean_object* v_str_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v_str_1673_ = lean_ctor_get(v_x_1671_, 1);
v___x_1674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___closed__0));
v___x_1675_ = lean_string_dec_eq(v_str_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
return v___x_1675_;
}
else
{
return v_suppressElabErrors_1670_;
}
}
else
{
uint8_t v___x_1676_; 
v___x_1676_ = 0;
return v___x_1676_;
}
}
else
{
uint8_t v___x_1677_; 
v___x_1677_ = 0;
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___boxed(lean_object* v_suppressElabErrors_1678_, lean_object* v_x_1679_){
_start:
{
uint8_t v_suppressElabErrors_boxed_1680_; uint8_t v_res_1681_; lean_object* v_r_1682_; 
v_suppressElabErrors_boxed_1680_ = lean_unbox(v_suppressElabErrors_1678_);
v_res_1681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0(v_suppressElabErrors_boxed_1680_, v_x_1679_);
lean_dec(v_x_1679_);
v_r_1682_ = lean_box(v_res_1681_);
return v_r_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v_as_1685_, size_t v_sz_1686_, size_t v_i_1687_, lean_object* v_b_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v_a_1693_; uint8_t v___x_1697_; 
v___x_1697_ = lean_usize_dec_lt(v_i_1687_, v_sz_1686_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1698_, 0, v_b_1688_);
return v___x_1698_;
}
else
{
lean_object* v_fileName_1699_; lean_object* v_fileMap_1700_; uint8_t v_suppressElabErrors_1701_; lean_object* v_a_1702_; lean_object* v_data_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; lean_object* v___x_1706_; lean_object* v___y_1708_; 
v_fileName_1699_ = lean_ctor_get(v___y_1689_, 0);
v_fileMap_1700_ = lean_ctor_get(v___y_1689_, 1);
v_suppressElabErrors_1701_ = lean_ctor_get_uint8(v___y_1689_, sizeof(void*)*10);
v_a_1702_ = lean_array_uget_borrowed(v_as_1685_, v_i_1687_);
v_data_1703_ = lean_ctor_get(v_a_1702_, 4);
v___x_1704_ = lean_box(0);
v___x_1705_ = 0;
lean_inc(v_data_1703_);
lean_inc_ref(v_fileMap_1700_);
lean_inc_ref(v_fileName_1699_);
v___x_1706_ = l_Lean_Elab_mkMessageCore(v_fileName_1699_, v_fileMap_1700_, v_data_1703_, v___x_1705_, v___y_1683_, v___y_1684_);
if (v_suppressElabErrors_1701_ == 0)
{
v___y_1708_ = v___y_1690_;
goto v___jp_1707_;
}
else
{
lean_object* v_data_1771_; lean_object* v___x_1772_; lean_object* v___f_1773_; uint8_t v___x_1774_; 
v_data_1771_ = lean_ctor_get(v___x_1706_, 4);
v___x_1772_ = lean_box(v_suppressElabErrors_1701_);
v___f_1773_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1773_, 0, v___x_1772_);
lean_inc(v_data_1771_);
v___x_1774_ = l_Lean_MessageData_hasTag(v___f_1773_, v_data_1771_);
if (v___x_1774_ == 0)
{
lean_dec_ref(v___x_1706_);
v_a_1693_ = v___x_1704_;
goto v___jp_1692_;
}
else
{
v___y_1708_ = v___y_1690_;
goto v___jp_1707_;
}
}
v___jp_1707_:
{
lean_object* v___x_1709_; 
v___x_1709_ = l_Lean_Elab_Command_getScope___redArg(v___y_1708_);
if (lean_obj_tag(v___x_1709_) == 0)
{
lean_object* v_a_1710_; lean_object* v_currNamespace_1711_; lean_object* v___x_1712_; 
v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
lean_inc(v_a_1710_);
lean_dec_ref_known(v___x_1709_, 1);
v_currNamespace_1711_ = lean_ctor_get(v_a_1710_, 2);
lean_inc(v_currNamespace_1711_);
lean_dec(v_a_1710_);
v___x_1712_ = l_Lean_Elab_Command_getScope___redArg(v___y_1708_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v_openDecls_1714_; lean_object* v_fileName_1715_; lean_object* v_pos_1716_; lean_object* v_endPos_1717_; uint8_t v_keepFullRange_1718_; uint8_t v_severity_1719_; uint8_t v_isSilent_1720_; lean_object* v_caption_1721_; lean_object* v_data_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1754_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
lean_inc(v_a_1713_);
lean_dec_ref_known(v___x_1712_, 1);
v_openDecls_1714_ = lean_ctor_get(v_a_1713_, 3);
lean_inc(v_openDecls_1714_);
lean_dec(v_a_1713_);
v_fileName_1715_ = lean_ctor_get(v___x_1706_, 0);
v_pos_1716_ = lean_ctor_get(v___x_1706_, 1);
v_endPos_1717_ = lean_ctor_get(v___x_1706_, 2);
v_keepFullRange_1718_ = lean_ctor_get_uint8(v___x_1706_, sizeof(void*)*5);
v_severity_1719_ = lean_ctor_get_uint8(v___x_1706_, sizeof(void*)*5 + 1);
v_isSilent_1720_ = lean_ctor_get_uint8(v___x_1706_, sizeof(void*)*5 + 2);
v_caption_1721_ = lean_ctor_get(v___x_1706_, 3);
v_data_1722_ = lean_ctor_get(v___x_1706_, 4);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1724_ = v___x_1706_;
v_isShared_1725_ = v_isSharedCheck_1754_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_data_1722_);
lean_inc(v_caption_1721_);
lean_inc(v_endPos_1717_);
lean_inc(v_pos_1716_);
lean_inc(v_fileName_1715_);
lean_dec(v___x_1706_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1754_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_currNamespace_1711_);
lean_ctor_set(v___x_1726_, 1, v_openDecls_1714_);
v___x_1727_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_1727_, 0, v___x_1726_);
lean_ctor_set(v___x_1727_, 1, v_data_1722_);
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 4, v___x_1727_);
v___x_1729_ = v___x_1724_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_fileName_1715_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_pos_1716_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_endPos_1717_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_caption_1721_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v___x_1727_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*5, v_keepFullRange_1718_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*5 + 1, v_severity_1719_);
lean_ctor_set_uint8(v_reuseFailAlloc_1753_, sizeof(void*)*5 + 2, v_isSilent_1720_);
v___x_1729_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; lean_object* v_env_1731_; lean_object* v_messages_1732_; lean_object* v_scopes_1733_; lean_object* v_usedQuotCtxts_1734_; lean_object* v_nextMacroScope_1735_; lean_object* v_maxRecDepth_1736_; lean_object* v_ngen_1737_; lean_object* v_auxDeclNGen_1738_; lean_object* v_infoState_1739_; lean_object* v_traceState_1740_; lean_object* v_snapshotTasks_1741_; lean_object* v_prevLinterStates_1742_; lean_object* v_codeQualityEntryTasks_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1752_; 
v___x_1730_ = lean_st_ref_take(v___y_1708_);
v_env_1731_ = lean_ctor_get(v___x_1730_, 0);
v_messages_1732_ = lean_ctor_get(v___x_1730_, 1);
v_scopes_1733_ = lean_ctor_get(v___x_1730_, 2);
v_usedQuotCtxts_1734_ = lean_ctor_get(v___x_1730_, 3);
v_nextMacroScope_1735_ = lean_ctor_get(v___x_1730_, 4);
v_maxRecDepth_1736_ = lean_ctor_get(v___x_1730_, 5);
v_ngen_1737_ = lean_ctor_get(v___x_1730_, 6);
v_auxDeclNGen_1738_ = lean_ctor_get(v___x_1730_, 7);
v_infoState_1739_ = lean_ctor_get(v___x_1730_, 8);
v_traceState_1740_ = lean_ctor_get(v___x_1730_, 9);
v_snapshotTasks_1741_ = lean_ctor_get(v___x_1730_, 10);
v_prevLinterStates_1742_ = lean_ctor_get(v___x_1730_, 11);
v_codeQualityEntryTasks_1743_ = lean_ctor_get(v___x_1730_, 12);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1745_ = v___x_1730_;
v_isShared_1746_ = v_isSharedCheck_1752_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_codeQualityEntryTasks_1743_);
lean_inc(v_prevLinterStates_1742_);
lean_inc(v_snapshotTasks_1741_);
lean_inc(v_traceState_1740_);
lean_inc(v_infoState_1739_);
lean_inc(v_auxDeclNGen_1738_);
lean_inc(v_ngen_1737_);
lean_inc(v_maxRecDepth_1736_);
lean_inc(v_nextMacroScope_1735_);
lean_inc(v_usedQuotCtxts_1734_);
lean_inc(v_scopes_1733_);
lean_inc(v_messages_1732_);
lean_inc(v_env_1731_);
lean_dec(v___x_1730_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1752_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1747_; lean_object* v___x_1749_; 
v___x_1747_ = l_Lean_MessageLog_add(v___x_1729_, v_messages_1732_);
if (v_isShared_1746_ == 0)
{
lean_ctor_set(v___x_1745_, 1, v___x_1747_);
v___x_1749_ = v___x_1745_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_env_1731_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v___x_1747_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_scopes_1733_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v_usedQuotCtxts_1734_);
lean_ctor_set(v_reuseFailAlloc_1751_, 4, v_nextMacroScope_1735_);
lean_ctor_set(v_reuseFailAlloc_1751_, 5, v_maxRecDepth_1736_);
lean_ctor_set(v_reuseFailAlloc_1751_, 6, v_ngen_1737_);
lean_ctor_set(v_reuseFailAlloc_1751_, 7, v_auxDeclNGen_1738_);
lean_ctor_set(v_reuseFailAlloc_1751_, 8, v_infoState_1739_);
lean_ctor_set(v_reuseFailAlloc_1751_, 9, v_traceState_1740_);
lean_ctor_set(v_reuseFailAlloc_1751_, 10, v_snapshotTasks_1741_);
lean_ctor_set(v_reuseFailAlloc_1751_, 11, v_prevLinterStates_1742_);
lean_ctor_set(v_reuseFailAlloc_1751_, 12, v_codeQualityEntryTasks_1743_);
v___x_1749_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
lean_object* v___x_1750_; 
v___x_1750_ = lean_st_ref_put(v___y_1708_, v___x_1749_);
v_a_1693_ = v___x_1704_;
goto v___jp_1692_;
}
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_currNamespace_1711_);
lean_dec_ref(v___x_1706_);
v_a_1755_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1712_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1712_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec_ref(v___x_1706_);
v_a_1763_ = lean_ctor_get(v___x_1709_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1709_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1709_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
v___jp_1692_:
{
size_t v___x_1694_; size_t v___x_1695_; 
v___x_1694_ = ((size_t)1ULL);
v___x_1695_ = lean_usize_add(v_i_1687_, v___x_1694_);
v_i_1687_ = v___x_1695_;
v_b_1688_ = v_a_1693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0___boxed(lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v_as_1777_, lean_object* v_sz_1778_, lean_object* v_i_1779_, lean_object* v_b_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
size_t v_sz_boxed_1784_; size_t v_i_boxed_1785_; lean_object* v_res_1786_; 
v_sz_boxed_1784_ = lean_unbox_usize(v_sz_1778_);
lean_dec(v_sz_1778_);
v_i_boxed_1785_ = lean_unbox_usize(v_i_1779_);
lean_dec(v_i_1779_);
v_res_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(v___y_1775_, v___y_1776_, v_as_1777_, v_sz_boxed_1784_, v_i_boxed_1785_, v_b_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec_ref(v_as_1777_);
lean_dec(v___y_1776_);
lean_dec(v___y_1775_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces(lean_object* v_x_1787_, lean_object* v_a_1788_, lean_object* v_a_1789_){
_start:
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_Lean_PostprocessTraces_postprocessStoredTracesCmd___closed__1));
lean_inc(v_x_1787_);
v___x_1792_ = l_Lean_Syntax_isOfKind(v_x_1787_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___x_1793_; 
lean_dec(v_x_1787_);
v___x_1793_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabStoreTraceAs_spec__0___redArg();
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; lean_object* v_id_1795_; lean_object* v___x_1796_; lean_object* v_post_1797_; lean_object* v___x_1798_; 
v___x_1794_ = lean_unsigned_to_nat(1u);
v_id_1795_ = l_Lean_Syntax_getArg(v_x_1787_, v___x_1794_);
v___x_1796_ = lean_unsigned_to_nat(2u);
v_post_1797_ = l_Lean_Syntax_getArg(v_x_1787_, v___x_1796_);
lean_dec(v_x_1787_);
v___x_1798_ = l___private_Lean_PostprocessTraces_StoredTraces_0__Lean_Elab_PostprocessTraces_resolveStoredTrace(v_id_1795_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1800_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v___x_1800_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_1797_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1800_) == 0)
{
lean_object* v_a_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v_a_1801_ = lean_ctor_get(v___x_1800_, 0);
lean_inc(v_a_1801_);
lean_dec_ref_known(v___x_1800_, 1);
v___x_1802_ = lean_alloc_closure((void*)(l_Lean_PostprocessTraces_StoredTrace_postprocess___boxed), 5, 2);
lean_closure_set(v___x_1802_, 0, v_a_1799_);
lean_closure_set(v___x_1802_, 1, v_a_1801_);
v___x_1803_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_1802_, v_a_1788_, v_a_1789_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = l_Lean_Elab_Command_getRef___redArg(v_a_1788_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___y_1808_; lean_object* v___y_1809_; uint8_t v___x_1822_; lean_object* v___y_1824_; lean_object* v___x_1827_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1822_ = 0;
v___x_1827_ = l_Lean_Syntax_getPos_x3f(v_a_1806_, v___x_1822_);
if (lean_obj_tag(v___x_1827_) == 0)
{
lean_object* v___x_1828_; 
v___x_1828_ = lean_unsigned_to_nat(0u);
v___y_1824_ = v___x_1828_;
goto v___jp_1823_;
}
else
{
lean_object* v_val_1829_; 
v_val_1829_ = lean_ctor_get(v___x_1827_, 0);
lean_inc(v_val_1829_);
lean_dec_ref_known(v___x_1827_, 1);
v___y_1824_ = v_val_1829_;
goto v___jp_1823_;
}
v___jp_1807_:
{
lean_object* v___x_1810_; size_t v_sz_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v___x_1810_ = lean_box(0);
v_sz_1811_ = lean_array_size(v_a_1804_);
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces_spec__0(v___y_1808_, v___y_1809_, v_a_1804_, v_sz_1811_, v___x_1812_, v___x_1810_, v_a_1788_, v_a_1789_);
lean_dec(v_a_1804_);
lean_dec(v___y_1809_);
lean_dec(v___y_1808_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1813_, 0);
lean_dec(v_unused_1821_);
v___x_1815_ = v___x_1813_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_dec(v___x_1813_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1810_);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1810_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
return v___x_1813_;
}
}
v___jp_1823_:
{
lean_object* v___x_1825_; 
v___x_1825_ = l_Lean_Syntax_getTailPos_x3f(v_a_1806_, v___x_1822_);
lean_dec(v_a_1806_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_inc(v___y_1824_);
v___y_1808_ = v___y_1824_;
v___y_1809_ = v___y_1824_;
goto v___jp_1807_;
}
else
{
lean_object* v_val_1826_; 
v_val_1826_ = lean_ctor_get(v___x_1825_, 0);
lean_inc(v_val_1826_);
lean_dec_ref_known(v___x_1825_, 1);
v___y_1808_ = v___y_1824_;
v___y_1809_ = v_val_1826_;
goto v___jp_1807_;
}
}
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec(v_a_1804_);
v_a_1830_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___x_1805_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1805_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
else
{
lean_object* v_a_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1845_; 
v_a_1838_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1845_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1840_ = v___x_1803_;
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_a_1838_);
lean_dec(v___x_1803_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1845_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v___x_1843_; 
if (v_isShared_1841_ == 0)
{
v___x_1843_ = v___x_1840_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_a_1838_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
}
}
else
{
lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1853_; 
lean_dec(v_a_1799_);
v_a_1846_ = lean_ctor_get(v___x_1800_, 0);
v_isSharedCheck_1853_ = !lean_is_exclusive(v___x_1800_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1848_ = v___x_1800_;
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1800_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1853_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1851_; 
if (v_isShared_1849_ == 0)
{
v___x_1851_ = v___x_1848_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_a_1846_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
else
{
lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
lean_dec(v_post_1797_);
v_a_1854_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1798_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1798_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces___boxed(lean_object* v_x_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Elab_PostprocessTraces_elabPostprocessStoredTraces(v_x_1862_, v_a_1863_, v_a_1864_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
return v_res_1866_;
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
