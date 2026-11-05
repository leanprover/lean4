// Lean compiler output
// Module: Lean.PostprocessTraces.PostprocessTracesCommand
// Imports: public meta import Lean.PostprocessTraces.Basic public meta import Lean.Elab.Command
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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_stringToMessageData(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftCoreM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_PostprocessTraces_runAndCollectMessages(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "PostprocessTraces"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "postprocessTracesCmd"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__2 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__2_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value_aux_0),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(169, 31, 168, 57, 105, 170, 97, 138)}};
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value_aux_1),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__2_value),LEAN_SCALAR_PTR_LITERAL(174, 16, 235, 102, 51, 61, 86, 237)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__4 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__4_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "postprocess_traces "};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__6 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__6_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__6_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__7 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__7_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__8 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__8_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__9 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__9_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__10 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__10_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__7_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__10_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__11 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__11_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " in"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__12 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__12_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__12_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__13 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__13_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__11_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__13_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__14 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__14_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ppLine"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__15 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__15_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__15_value),LEAN_SCALAR_PTR_LITERAL(117, 61, 38, 245, 158, 59, 171, 58)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__16 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__16_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__16_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__17 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__17_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__14_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__17_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__18 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__18_value;
static const lean_string_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__19 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__19_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__19_value),LEAN_SCALAR_PTR_LITERAL(29, 69, 134, 125, 237, 175, 69, 70)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__20 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__20_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__21 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__21_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__5_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__18_value),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__21_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__22 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__22_value;
static const lean_ctor_object l_Lean_PostprocessTraces_postprocessTracesCmd___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__22_value)}};
static const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd___closed__23 = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__23_value;
LEAN_EXPORT const lean_object* l_Lean_PostprocessTraces_postprocessTracesCmd = (const lean_object*)&l_Lean_PostprocessTraces_postprocessTracesCmd___closed__23_value;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "internal exception: "};
static const lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0 = (const lean_object*)&l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___closed__0 = (const lean_object*)&l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_box(0);
v___x_56_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_57_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
lean_ctor_set(v___x_57_, 1, v___x_55_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0);
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___boxed(lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0(lean_object* v_00_u03b1_63_, lean_object* v___y_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___boxed(lean_object* v_00_u03b1_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0(v_00_u03b1_68_, v___y_69_, v___y_70_);
lean_dec(v___y_70_);
lean_dec_ref(v___y_69_);
return v_res_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0(lean_object* v_roots_73_, lean_object* v___y_74_, lean_object* v___y_75_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v_roots_73_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0___boxed(lean_object* v_roots_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0(v_roots_78_, v___y_79_, v___y_80_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
return v_res_82_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_83_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_84_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_87_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
lean_ctor_set(v___x_88_, 3, v___x_87_);
lean_ctor_set(v___x_88_, 4, v___x_86_);
lean_ctor_set(v___x_88_, 5, v___x_86_);
lean_ctor_set(v___x_88_, 6, v___x_86_);
lean_ctor_set(v___x_88_, 7, v___x_86_);
lean_ctor_set(v___x_88_, 8, v___x_86_);
lean_ctor_set(v___x_88_, 9, v___x_86_);
lean_ctor_set(v___x_88_, 10, v___x_86_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_unsigned_to_nat(32u);
v___x_90_ = lean_mk_empty_array_with_capacity(v___x_89_);
v___x_91_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
return v___x_91_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_92_ = ((size_t)5ULL);
v___x_93_ = lean_unsigned_to_nat(0u);
v___x_94_ = lean_unsigned_to_nat(32u);
v___x_95_ = lean_mk_empty_array_with_capacity(v___x_94_);
v___x_96_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3);
v___x_97_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_93_);
lean_ctor_set(v___x_97_, 3, v___x_93_);
lean_ctor_set_usize(v___x_97_, 4, v___x_92_);
return v___x_97_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_98_ = lean_box(1);
v___x_99_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_98_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_102_, lean_object* v___y_103_){
_start:
{
lean_object* v___x_105_; lean_object* v_env_106_; uint8_t v___x_107_; lean_object* v_env_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_scopes_111_; lean_object* v___x_112_; lean_object* v_opts_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_105_ = lean_st_ref_get(v___y_103_);
v_env_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_env_106_);
lean_dec(v___x_105_);
v___x_107_ = 0;
v_env_108_ = l_Lean_Environment_setRecordingDeps(v_env_106_, v___x_107_);
v___x_109_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_110_ = lean_st_ref_get(v___y_103_);
v_scopes_111_ = lean_ctor_get(v___x_110_, 2);
lean_inc(v_scopes_111_);
lean_dec(v___x_110_);
v___x_112_ = l_List_head_x21___redArg(v___x_109_, v_scopes_111_);
lean_dec(v_scopes_111_);
v_opts_113_ = lean_ctor_get(v___x_112_, 1);
lean_inc_ref(v_opts_113_);
lean_dec(v___x_112_);
v___x_114_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_115_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5);
v___x_116_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_116_, 0, v_env_108_);
lean_ctor_set(v___x_116_, 1, v___x_114_);
lean_ctor_set(v___x_116_, 2, v___x_115_);
lean_ctor_set(v___x_116_, 3, v_opts_113_);
v___x_117_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_msgData_102_);
v___x_118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_119_, v___y_120_);
lean_dec(v___y_120_);
return v_res_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 1)
{
lean_object* v_pre_126_; 
v_pre_126_ = lean_ctor_get(v_x_125_, 0);
if (lean_obj_tag(v_pre_126_) == 0)
{
lean_object* v_str_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v_str_127_ = lean_ctor_get(v_x_125_, 1);
v___x_128_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_129_ = lean_string_dec_eq(v_str_127_, v___x_128_);
if (v___x_129_ == 0)
{
return v___x_129_;
}
else
{
return v_suppressElabErrors_124_;
}
}
else
{
uint8_t v___x_130_; 
v___x_130_ = 0;
return v___x_130_;
}
}
else
{
uint8_t v___x_131_; 
v___x_131_ = 0;
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_132_, lean_object* v_x_133_){
_start:
{
uint8_t v_suppressElabErrors_boxed_134_; uint8_t v_res_135_; lean_object* v_r_136_; 
v_suppressElabErrors_boxed_134_ = lean_unbox(v_suppressElabErrors_132_);
v_res_135_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_134_, v_x_133_);
lean_dec(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(lean_object* v_opts_137_, lean_object* v_opt_138_){
_start:
{
lean_object* v_name_139_; lean_object* v_defValue_140_; lean_object* v_map_141_; lean_object* v___x_142_; 
v_name_139_ = lean_ctor_get(v_opt_138_, 0);
v_defValue_140_ = lean_ctor_get(v_opt_138_, 1);
v_map_141_ = lean_ctor_get(v_opts_137_, 0);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_141_, v_name_139_);
if (lean_obj_tag(v___x_142_) == 0)
{
uint8_t v___x_143_; 
v___x_143_ = lean_unbox(v_defValue_140_);
return v___x_143_;
}
else
{
lean_object* v_val_144_; 
v_val_144_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v___x_142_, 1);
if (lean_obj_tag(v_val_144_) == 1)
{
uint8_t v_v_145_; 
v_v_145_ = lean_ctor_get_uint8(v_val_144_, 0);
lean_dec_ref_known(v_val_144_, 0);
return v_v_145_;
}
else
{
uint8_t v___x_146_; 
lean_dec(v_val_144_);
v___x_146_ = lean_unbox(v_defValue_140_);
return v___x_146_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_opts_147_, lean_object* v_opt_148_){
_start:
{
uint8_t v_res_149_; lean_object* v_r_150_; 
v_res_149_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_147_, v_opt_148_);
lean_dec_ref(v_opt_148_);
lean_dec_ref(v_opts_147_);
v_r_150_ = lean_box(v_res_149_);
return v_r_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(lean_object* v_ref_152_, lean_object* v_msgData_153_, uint8_t v_severity_154_, uint8_t v_isSilent_155_, lean_object* v___y_156_, lean_object* v___y_157_){
_start:
{
lean_object* v___y_160_; lean_object* v___y_161_; uint8_t v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; uint8_t v___y_165_; lean_object* v___y_166_; lean_object* v___y_167_; uint8_t v___y_225_; uint8_t v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; lean_object* v___y_251_; uint8_t v___y_252_; uint8_t v___y_253_; lean_object* v___y_254_; uint8_t v___y_258_; uint8_t v___y_259_; uint8_t v___x_274_; uint8_t v___y_276_; uint8_t v___x_286_; 
v___x_274_ = 2;
v___x_286_ = l_Lean_instBEqMessageSeverity_beq(v_severity_154_, v___x_274_);
if (v___x_286_ == 0)
{
v___y_276_ = v___x_286_;
goto v___jp_275_;
}
else
{
uint8_t v___x_287_; 
lean_inc_ref(v_msgData_153_);
v___x_287_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_153_);
if (v___x_287_ == 0)
{
v___y_276_ = v___x_287_;
goto v___jp_275_;
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec_ref(v_msgData_153_);
v___x_288_ = lean_box(0);
v___x_289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
return v___x_289_;
}
}
v___jp_159_:
{
lean_object* v___x_168_; 
v___x_168_ = l_Lean_Elab_Command_getScope___redArg(v___y_167_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_object* v_a_169_; lean_object* v_currNamespace_170_; lean_object* v___x_171_; 
v_a_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_a_169_);
lean_dec_ref_known(v___x_168_, 1);
v_currNamespace_170_ = lean_ctor_get(v_a_169_, 2);
lean_inc(v_currNamespace_170_);
lean_dec(v_a_169_);
v___x_171_ = l_Lean_Elab_Command_getScope___redArg(v___y_167_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_207_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_207_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_207_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_207_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v_openDecls_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_env_181_; lean_object* v_messages_182_; lean_object* v_scopes_183_; lean_object* v_usedQuotCtxts_184_; lean_object* v_nextMacroScope_185_; lean_object* v_maxRecDepth_186_; lean_object* v_ngen_187_; lean_object* v_auxDeclNGen_188_; lean_object* v_infoState_189_; lean_object* v_traceState_190_; lean_object* v_snapshotTasks_191_; lean_object* v_prevLinterStates_192_; lean_object* v_codeQualityEntryTasks_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_206_; 
v_openDecls_176_ = lean_ctor_get(v_a_172_, 3);
lean_inc(v_openDecls_176_);
lean_dec(v_a_172_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_currNamespace_170_);
lean_ctor_set(v___x_177_, 1, v_openDecls_176_);
v___x_178_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___y_161_);
lean_inc_ref(v___y_164_);
lean_inc_ref(v___y_163_);
v___x_179_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_179_, 0, v___y_163_);
lean_ctor_set(v___x_179_, 1, v___y_166_);
lean_ctor_set(v___x_179_, 2, v___y_160_);
lean_ctor_set(v___x_179_, 3, v___y_164_);
lean_ctor_set(v___x_179_, 4, v___x_178_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5, v___y_165_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5 + 1, v___y_162_);
lean_ctor_set_uint8(v___x_179_, sizeof(void*)*5 + 2, v_isSilent_155_);
v___x_180_ = lean_st_ref_take(v___y_167_);
v_env_181_ = lean_ctor_get(v___x_180_, 0);
v_messages_182_ = lean_ctor_get(v___x_180_, 1);
v_scopes_183_ = lean_ctor_get(v___x_180_, 2);
v_usedQuotCtxts_184_ = lean_ctor_get(v___x_180_, 3);
v_nextMacroScope_185_ = lean_ctor_get(v___x_180_, 4);
v_maxRecDepth_186_ = lean_ctor_get(v___x_180_, 5);
v_ngen_187_ = lean_ctor_get(v___x_180_, 6);
v_auxDeclNGen_188_ = lean_ctor_get(v___x_180_, 7);
v_infoState_189_ = lean_ctor_get(v___x_180_, 8);
v_traceState_190_ = lean_ctor_get(v___x_180_, 9);
v_snapshotTasks_191_ = lean_ctor_get(v___x_180_, 10);
v_prevLinterStates_192_ = lean_ctor_get(v___x_180_, 11);
v_codeQualityEntryTasks_193_ = lean_ctor_get(v___x_180_, 12);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_206_ == 0)
{
v___x_195_ = v___x_180_;
v_isShared_196_ = v_isSharedCheck_206_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_codeQualityEntryTasks_193_);
lean_inc(v_prevLinterStates_192_);
lean_inc(v_snapshotTasks_191_);
lean_inc(v_traceState_190_);
lean_inc(v_infoState_189_);
lean_inc(v_auxDeclNGen_188_);
lean_inc(v_ngen_187_);
lean_inc(v_maxRecDepth_186_);
lean_inc(v_nextMacroScope_185_);
lean_inc(v_usedQuotCtxts_184_);
lean_inc(v_scopes_183_);
lean_inc(v_messages_182_);
lean_inc(v_env_181_);
lean_dec(v___x_180_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_206_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_197_ = lean_box(0);
v___x_198_ = l_Lean_MessageLog_add(v___x_179_, v_messages_182_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___x_198_);
v___x_200_ = v___x_195_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_env_181_);
lean_ctor_set(v_reuseFailAlloc_205_, 1, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_205_, 2, v_scopes_183_);
lean_ctor_set(v_reuseFailAlloc_205_, 3, v_usedQuotCtxts_184_);
lean_ctor_set(v_reuseFailAlloc_205_, 4, v_nextMacroScope_185_);
lean_ctor_set(v_reuseFailAlloc_205_, 5, v_maxRecDepth_186_);
lean_ctor_set(v_reuseFailAlloc_205_, 6, v_ngen_187_);
lean_ctor_set(v_reuseFailAlloc_205_, 7, v_auxDeclNGen_188_);
lean_ctor_set(v_reuseFailAlloc_205_, 8, v_infoState_189_);
lean_ctor_set(v_reuseFailAlloc_205_, 9, v_traceState_190_);
lean_ctor_set(v_reuseFailAlloc_205_, 10, v_snapshotTasks_191_);
lean_ctor_set(v_reuseFailAlloc_205_, 11, v_prevLinterStates_192_);
lean_ctor_set(v_reuseFailAlloc_205_, 12, v_codeQualityEntryTasks_193_);
v___x_200_ = v_reuseFailAlloc_205_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_201_ = lean_st_ref_put(v___y_167_, v___x_200_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_197_);
v___x_203_ = v___x_174_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_197_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec(v_currNamespace_170_);
lean_dec_ref(v___y_166_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
v_a_208_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_171_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_171_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v___y_166_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
v_a_216_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_168_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_168_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
v___jp_224_:
{
lean_object* v_fileName_229_; lean_object* v_fileMap_230_; uint8_t v_suppressElabErrors_231_; lean_object* v___x_232_; lean_object* v___f_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_249_; 
v_fileName_229_ = lean_ctor_get(v___y_156_, 0);
v_fileMap_230_ = lean_ctor_get(v___y_156_, 1);
v_suppressElabErrors_231_ = lean_ctor_get_uint8(v___y_156_, sizeof(void*)*10);
v___x_232_ = lean_box(v_suppressElabErrors_231_);
v___f_233_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed), 2, 1);
lean_closure_set(v___f_233_, 0, v___x_232_);
v___x_234_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_153_);
v___x_235_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v___x_234_, v___y_157_);
v_a_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_249_ == 0)
{
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_249_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_249_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_inc_ref_n(v_fileMap_230_, 2);
v___x_240_ = l_Lean_FileMap_toPosition(v_fileMap_230_, v___y_227_);
lean_dec(v___y_227_);
v___x_241_ = l_Lean_FileMap_toPosition(v_fileMap_230_, v___y_228_);
lean_dec(v___y_228_);
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
v___x_243_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___closed__0));
if (v_suppressElabErrors_231_ == 0)
{
lean_del_object(v___x_238_);
lean_dec_ref(v___f_233_);
v___y_160_ = v___x_242_;
v___y_161_ = v_a_236_;
v___y_162_ = v___y_225_;
v___y_163_ = v_fileName_229_;
v___y_164_ = v___x_243_;
v___y_165_ = v___y_226_;
v___y_166_ = v___x_240_;
v___y_167_ = v___y_157_;
goto v___jp_159_;
}
else
{
uint8_t v___x_244_; 
lean_inc(v_a_236_);
v___x_244_ = l_Lean_MessageData_hasTag(v___f_233_, v_a_236_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_dec_ref_known(v___x_242_, 1);
lean_dec_ref(v___x_240_);
lean_dec(v_a_236_);
v___x_245_ = lean_box(0);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_245_);
v___x_247_ = v___x_238_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
else
{
lean_del_object(v___x_238_);
v___y_160_ = v___x_242_;
v___y_161_ = v_a_236_;
v___y_162_ = v___y_225_;
v___y_163_ = v_fileName_229_;
v___y_164_ = v___x_243_;
v___y_165_ = v___y_226_;
v___y_166_ = v___x_240_;
v___y_167_ = v___y_157_;
goto v___jp_159_;
}
}
}
}
v___jp_250_:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Syntax_getTailPos_x3f(v___y_251_, v___y_253_);
lean_dec(v___y_251_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_inc(v___y_254_);
v___y_225_ = v___y_252_;
v___y_226_ = v___y_253_;
v___y_227_ = v___y_254_;
v___y_228_ = v___y_254_;
goto v___jp_224_;
}
else
{
lean_object* v_val_256_; 
v_val_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v___x_255_, 1);
v___y_225_ = v___y_252_;
v___y_226_ = v___y_253_;
v___y_227_ = v___y_254_;
v___y_228_ = v_val_256_;
goto v___jp_224_;
}
}
v___jp_257_:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_Elab_Command_getRef___redArg(v___y_156_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_a_261_; lean_object* v_ref_262_; lean_object* v___x_263_; 
v_a_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v___x_260_, 1);
v_ref_262_ = l_Lean_replaceRef(v_ref_152_, v_a_261_);
lean_dec(v_a_261_);
v___x_263_ = l_Lean_Syntax_getPos_x3f(v_ref_262_, v___y_258_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_unsigned_to_nat(0u);
v___y_251_ = v_ref_262_;
v___y_252_ = v___y_259_;
v___y_253_ = v___y_258_;
v___y_254_ = v___x_264_;
goto v___jp_250_;
}
else
{
lean_object* v_val_265_; 
v_val_265_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_val_265_);
lean_dec_ref_known(v___x_263_, 1);
v___y_251_ = v_ref_262_;
v___y_252_ = v___y_259_;
v___y_253_ = v___y_258_;
v___y_254_ = v_val_265_;
goto v___jp_250_;
}
}
else
{
lean_object* v_a_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_273_; 
lean_dec_ref(v_msgData_153_);
v_a_266_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_273_ == 0)
{
v___x_268_ = v___x_260_;
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_a_266_);
lean_dec(v___x_260_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_273_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_271_; 
if (v_isShared_269_ == 0)
{
v___x_271_ = v___x_268_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_a_266_);
v___x_271_ = v_reuseFailAlloc_272_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
return v___x_271_;
}
}
}
}
v___jp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v_scopes_279_; lean_object* v___x_280_; lean_object* v_opts_281_; uint8_t v___x_282_; uint8_t v___x_283_; 
v___x_277_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_278_ = lean_st_ref_get(v___y_157_);
v_scopes_279_ = lean_ctor_get(v___x_278_, 2);
lean_inc(v_scopes_279_);
lean_dec(v___x_278_);
v___x_280_ = l_List_head_x21___redArg(v___x_277_, v_scopes_279_);
lean_dec(v_scopes_279_);
v_opts_281_ = lean_ctor_get(v___x_280_, 1);
lean_inc_ref(v_opts_281_);
lean_dec(v___x_280_);
v___x_282_ = 1;
v___x_283_ = l_Lean_instBEqMessageSeverity_beq(v_severity_154_, v___x_282_);
if (v___x_283_ == 0)
{
lean_dec_ref(v_opts_281_);
v___y_258_ = v___y_276_;
v___y_259_ = v_severity_154_;
goto v___jp_257_;
}
else
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = l_Lean_warningAsError;
v___x_285_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_281_, v___x_284_);
lean_dec_ref(v_opts_281_);
if (v___x_285_ == 0)
{
v___y_258_ = v___y_276_;
v___y_259_ = v_severity_154_;
goto v___jp_257_;
}
else
{
v___y_258_ = v___y_276_;
v___y_259_ = v___x_274_;
goto v___jp_257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_290_, lean_object* v_msgData_291_, lean_object* v_severity_292_, lean_object* v_isSilent_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_){
_start:
{
uint8_t v_severity_boxed_297_; uint8_t v_isSilent_boxed_298_; lean_object* v_res_299_; 
v_severity_boxed_297_ = lean_unbox(v_severity_292_);
v_isSilent_boxed_298_ = lean_unbox(v_isSilent_293_);
v_res_299_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_290_, v_msgData_291_, v_severity_boxed_297_, v_isSilent_boxed_298_, v___y_294_, v___y_295_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
lean_dec(v_ref_290_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(lean_object* v_msgData_300_, uint8_t v_severity_301_, uint8_t v_isSilent_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Elab_Command_getRef___redArg(v___y_303_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v_a_307_; lean_object* v___x_308_; 
v_a_307_ = lean_ctor_get(v___x_306_, 0);
lean_inc(v_a_307_);
lean_dec_ref_known(v___x_306_, 1);
v___x_308_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_a_307_, v_msgData_300_, v_severity_301_, v_isSilent_302_, v___y_303_, v___y_304_);
lean_dec(v_a_307_);
return v___x_308_;
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
lean_dec_ref(v_msgData_300_);
v_a_309_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_306_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_306_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_317_, lean_object* v_severity_318_, lean_object* v_isSilent_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
uint8_t v_severity_boxed_323_; uint8_t v_isSilent_boxed_324_; lean_object* v_res_325_; 
v_severity_boxed_323_ = lean_unbox(v_severity_318_);
v_isSilent_boxed_324_ = lean_unbox(v_isSilent_319_);
v_res_325_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_317_, v_severity_boxed_323_, v_isSilent_boxed_324_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(lean_object* v_msgData_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
uint8_t v___x_330_; uint8_t v___x_331_; lean_object* v___x_332_; 
v___x_330_ = 2;
v___x_331_ = 0;
v___x_332_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_326_, v___x_330_, v___x_331_, v___y_327_, v___y_328_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2___boxed(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v_msgData_333_, v___y_334_, v___y_335_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(lean_object* v_ref_338_, lean_object* v_msgData_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
uint8_t v___x_343_; uint8_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = 2;
v___x_344_ = 0;
v___x_345_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_338_, v_msgData_339_, v___x_343_, v___x_344_, v___y_340_, v___y_341_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1___boxed(lean_object* v_ref_346_, lean_object* v_msgData_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_346_, v_msgData_347_, v___y_348_, v___y_349_);
lean_dec(v___y_349_);
lean_dec_ref(v___y_348_);
lean_dec(v_ref_346_);
return v_res_351_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1(void){
_start:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0));
v___x_354_ = l_Lean_stringToMessageData(v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(lean_object* v_ex_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
if (lean_obj_tag(v_ex_355_) == 0)
{
lean_object* v_ref_362_; lean_object* v_msg_363_; lean_object* v___x_364_; 
v_ref_362_ = lean_ctor_get(v_ex_355_, 0);
lean_inc(v_ref_362_);
v_msg_363_ = lean_ctor_get(v_ex_355_, 1);
lean_inc_ref(v_msg_363_);
lean_dec_ref_known(v_ex_355_, 2);
v___x_364_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_362_, v_msg_363_, v___y_356_, v___y_357_);
lean_dec(v_ref_362_);
return v___x_364_;
}
else
{
lean_object* v_id_365_; uint8_t v___x_366_; 
v_id_365_ = lean_ctor_get(v_ex_355_, 0);
lean_inc(v_id_365_);
v___x_366_ = l_Lean_Elab_isAbortExceptionId(v_id_365_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_392_; 
v___x_367_ = l_Lean_Exception_isInterrupt(v_ex_355_);
v_isSharedCheck_392_ = !lean_is_exclusive(v_ex_355_);
if (v_isSharedCheck_392_ == 0)
{
lean_object* v_unused_393_; lean_object* v_unused_394_; 
v_unused_393_ = lean_ctor_get(v_ex_355_, 1);
lean_dec(v_unused_393_);
v_unused_394_ = lean_ctor_get(v_ex_355_, 0);
lean_dec(v_unused_394_);
v___x_369_ = v_ex_355_;
v_isShared_370_ = v_isSharedCheck_392_;
goto v_resetjp_368_;
}
else
{
lean_dec(v_ex_355_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_392_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
if (v___x_367_ == 0)
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_InternalExceptionId_getName(v_id_365_);
lean_dec(v_id_365_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_del_object(v___x_369_);
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1);
v___x_374_ = l_Lean_MessageData_ofName(v_a_372_);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v___x_375_, v___y_356_, v___y_357_);
return v___x_376_;
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_391_; 
v_a_377_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_391_ == 0)
{
v___x_379_ = v___x_371_;
v_isShared_380_ = v_isSharedCheck_391_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_371_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_391_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_ref_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v_ref_381_ = lean_ctor_get(v___y_356_, 7);
v___x_382_ = lean_io_error_to_string(v_a_377_);
v___x_383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___x_384_ = l_Lean_MessageData_ofFormat(v___x_383_);
lean_inc(v_ref_381_);
if (v_isShared_370_ == 0)
{
lean_ctor_set_tag(v___x_369_, 0);
lean_ctor_set(v___x_369_, 1, v___x_384_);
lean_ctor_set(v___x_369_, 0, v_ref_381_);
v___x_386_ = v___x_369_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_ref_381_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_390_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_388_; 
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_386_);
v___x_388_ = v___x_379_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v___x_386_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
}
else
{
lean_del_object(v___x_369_);
lean_dec(v_id_365_);
goto v___jp_359_;
}
}
}
else
{
lean_dec(v_id_365_);
lean_dec_ref_known(v_ex_355_, 2);
goto v___jp_359_;
}
}
v___jp_359_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
return v___x_361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___boxed(lean_object* v_ex_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_ex_395_, v___y_396_, v___y_397_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(lean_object* v_a_400_, lean_object* v_as_401_, size_t v_sz_402_, size_t v_i_403_, lean_object* v_b_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_a_409_; uint8_t v___x_413_; 
v___x_413_ = lean_usize_dec_lt(v_i_403_, v_sz_402_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; 
lean_dec_ref(v_a_400_);
v___x_414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_414_, 0, v_b_404_);
return v___x_414_;
}
else
{
lean_object* v___x_415_; lean_object* v_a_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_415_ = lean_box(0);
v_a_416_ = lean_array_uget_borrowed(v_as_401_, v_i_403_);
lean_inc(v_a_416_);
lean_inc_ref(v_a_400_);
v___x_417_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed), 5, 2);
lean_closure_set(v___x_417_, 0, v_a_400_);
lean_closure_set(v___x_417_, 1, v_a_416_);
v___x_418_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_417_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_418_) == 0)
{
lean_object* v_a_419_; 
v_a_419_ = lean_ctor_get(v___x_418_, 0);
lean_inc(v_a_419_);
lean_dec_ref_known(v___x_418_, 1);
if (lean_obj_tag(v_a_419_) == 1)
{
lean_object* v_val_420_; lean_object* v___x_421_; lean_object* v_env_422_; lean_object* v_messages_423_; lean_object* v_scopes_424_; lean_object* v_usedQuotCtxts_425_; lean_object* v_nextMacroScope_426_; lean_object* v_maxRecDepth_427_; lean_object* v_ngen_428_; lean_object* v_auxDeclNGen_429_; lean_object* v_infoState_430_; lean_object* v_traceState_431_; lean_object* v_snapshotTasks_432_; lean_object* v_prevLinterStates_433_; lean_object* v_codeQualityEntryTasks_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_443_; 
v_val_420_ = lean_ctor_get(v_a_419_, 0);
lean_inc(v_val_420_);
lean_dec_ref_known(v_a_419_, 1);
v___x_421_ = lean_st_ref_take(v___y_406_);
v_env_422_ = lean_ctor_get(v___x_421_, 0);
v_messages_423_ = lean_ctor_get(v___x_421_, 1);
v_scopes_424_ = lean_ctor_get(v___x_421_, 2);
v_usedQuotCtxts_425_ = lean_ctor_get(v___x_421_, 3);
v_nextMacroScope_426_ = lean_ctor_get(v___x_421_, 4);
v_maxRecDepth_427_ = lean_ctor_get(v___x_421_, 5);
v_ngen_428_ = lean_ctor_get(v___x_421_, 6);
v_auxDeclNGen_429_ = lean_ctor_get(v___x_421_, 7);
v_infoState_430_ = lean_ctor_get(v___x_421_, 8);
v_traceState_431_ = lean_ctor_get(v___x_421_, 9);
v_snapshotTasks_432_ = lean_ctor_get(v___x_421_, 10);
v_prevLinterStates_433_ = lean_ctor_get(v___x_421_, 11);
v_codeQualityEntryTasks_434_ = lean_ctor_get(v___x_421_, 12);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_421_);
if (v_isSharedCheck_443_ == 0)
{
v___x_436_ = v___x_421_;
v_isShared_437_ = v_isSharedCheck_443_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_codeQualityEntryTasks_434_);
lean_inc(v_prevLinterStates_433_);
lean_inc(v_snapshotTasks_432_);
lean_inc(v_traceState_431_);
lean_inc(v_infoState_430_);
lean_inc(v_auxDeclNGen_429_);
lean_inc(v_ngen_428_);
lean_inc(v_maxRecDepth_427_);
lean_inc(v_nextMacroScope_426_);
lean_inc(v_usedQuotCtxts_425_);
lean_inc(v_scopes_424_);
lean_inc(v_messages_423_);
lean_inc(v_env_422_);
lean_dec(v___x_421_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_443_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_438_; lean_object* v___x_440_; 
v___x_438_ = l_Lean_MessageLog_add(v_val_420_, v_messages_423_);
if (v_isShared_437_ == 0)
{
lean_ctor_set(v___x_436_, 1, v___x_438_);
v___x_440_ = v___x_436_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_env_422_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v___x_438_);
lean_ctor_set(v_reuseFailAlloc_442_, 2, v_scopes_424_);
lean_ctor_set(v_reuseFailAlloc_442_, 3, v_usedQuotCtxts_425_);
lean_ctor_set(v_reuseFailAlloc_442_, 4, v_nextMacroScope_426_);
lean_ctor_set(v_reuseFailAlloc_442_, 5, v_maxRecDepth_427_);
lean_ctor_set(v_reuseFailAlloc_442_, 6, v_ngen_428_);
lean_ctor_set(v_reuseFailAlloc_442_, 7, v_auxDeclNGen_429_);
lean_ctor_set(v_reuseFailAlloc_442_, 8, v_infoState_430_);
lean_ctor_set(v_reuseFailAlloc_442_, 9, v_traceState_431_);
lean_ctor_set(v_reuseFailAlloc_442_, 10, v_snapshotTasks_432_);
lean_ctor_set(v_reuseFailAlloc_442_, 11, v_prevLinterStates_433_);
lean_ctor_set(v_reuseFailAlloc_442_, 12, v_codeQualityEntryTasks_434_);
v___x_440_ = v_reuseFailAlloc_442_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_441_; 
v___x_441_ = lean_st_ref_put(v___y_406_, v___x_440_);
v_a_409_ = v___x_415_;
goto v___jp_408_;
}
}
}
else
{
lean_dec(v_a_419_);
v_a_409_ = v___x_415_;
goto v___jp_408_;
}
}
else
{
lean_object* v_a_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_476_; 
v_a_444_ = lean_ctor_get(v___x_418_, 0);
v_isSharedCheck_476_ = !lean_is_exclusive(v___x_418_);
if (v_isSharedCheck_476_ == 0)
{
v___x_446_ = v___x_418_;
v_isShared_447_ = v_isSharedCheck_476_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_a_444_);
lean_dec(v___x_418_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_476_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
uint8_t v___x_448_; 
v___x_448_ = l_Lean_Exception_isInterrupt(v_a_444_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_del_object(v___x_446_);
v___x_449_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_444_, v___y_405_, v___y_406_);
if (lean_obj_tag(v___x_449_) == 0)
{
lean_object* v___x_450_; lean_object* v_env_451_; lean_object* v_messages_452_; lean_object* v_scopes_453_; lean_object* v_usedQuotCtxts_454_; lean_object* v_nextMacroScope_455_; lean_object* v_maxRecDepth_456_; lean_object* v_ngen_457_; lean_object* v_auxDeclNGen_458_; lean_object* v_infoState_459_; lean_object* v_traceState_460_; lean_object* v_snapshotTasks_461_; lean_object* v_prevLinterStates_462_; lean_object* v_codeQualityEntryTasks_463_; lean_object* v___x_465_; uint8_t v_isShared_466_; uint8_t v_isSharedCheck_472_; 
lean_dec_ref_known(v___x_449_, 1);
v___x_450_ = lean_st_ref_take(v___y_406_);
v_env_451_ = lean_ctor_get(v___x_450_, 0);
v_messages_452_ = lean_ctor_get(v___x_450_, 1);
v_scopes_453_ = lean_ctor_get(v___x_450_, 2);
v_usedQuotCtxts_454_ = lean_ctor_get(v___x_450_, 3);
v_nextMacroScope_455_ = lean_ctor_get(v___x_450_, 4);
v_maxRecDepth_456_ = lean_ctor_get(v___x_450_, 5);
v_ngen_457_ = lean_ctor_get(v___x_450_, 6);
v_auxDeclNGen_458_ = lean_ctor_get(v___x_450_, 7);
v_infoState_459_ = lean_ctor_get(v___x_450_, 8);
v_traceState_460_ = lean_ctor_get(v___x_450_, 9);
v_snapshotTasks_461_ = lean_ctor_get(v___x_450_, 10);
v_prevLinterStates_462_ = lean_ctor_get(v___x_450_, 11);
v_codeQualityEntryTasks_463_ = lean_ctor_get(v___x_450_, 12);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_450_);
if (v_isSharedCheck_472_ == 0)
{
v___x_465_ = v___x_450_;
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
else
{
lean_inc(v_codeQualityEntryTasks_463_);
lean_inc(v_prevLinterStates_462_);
lean_inc(v_snapshotTasks_461_);
lean_inc(v_traceState_460_);
lean_inc(v_infoState_459_);
lean_inc(v_auxDeclNGen_458_);
lean_inc(v_ngen_457_);
lean_inc(v_maxRecDepth_456_);
lean_inc(v_nextMacroScope_455_);
lean_inc(v_usedQuotCtxts_454_);
lean_inc(v_scopes_453_);
lean_inc(v_messages_452_);
lean_inc(v_env_451_);
lean_dec(v___x_450_);
v___x_465_ = lean_box(0);
v_isShared_466_ = v_isSharedCheck_472_;
goto v_resetjp_464_;
}
v_resetjp_464_:
{
lean_object* v___x_467_; lean_object* v___x_469_; 
lean_inc(v_a_416_);
v___x_467_ = l_Lean_MessageLog_add(v_a_416_, v_messages_452_);
if (v_isShared_466_ == 0)
{
lean_ctor_set(v___x_465_, 1, v___x_467_);
v___x_469_ = v___x_465_;
goto v_reusejp_468_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_env_451_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_467_);
lean_ctor_set(v_reuseFailAlloc_471_, 2, v_scopes_453_);
lean_ctor_set(v_reuseFailAlloc_471_, 3, v_usedQuotCtxts_454_);
lean_ctor_set(v_reuseFailAlloc_471_, 4, v_nextMacroScope_455_);
lean_ctor_set(v_reuseFailAlloc_471_, 5, v_maxRecDepth_456_);
lean_ctor_set(v_reuseFailAlloc_471_, 6, v_ngen_457_);
lean_ctor_set(v_reuseFailAlloc_471_, 7, v_auxDeclNGen_458_);
lean_ctor_set(v_reuseFailAlloc_471_, 8, v_infoState_459_);
lean_ctor_set(v_reuseFailAlloc_471_, 9, v_traceState_460_);
lean_ctor_set(v_reuseFailAlloc_471_, 10, v_snapshotTasks_461_);
lean_ctor_set(v_reuseFailAlloc_471_, 11, v_prevLinterStates_462_);
lean_ctor_set(v_reuseFailAlloc_471_, 12, v_codeQualityEntryTasks_463_);
v___x_469_ = v_reuseFailAlloc_471_;
goto v_reusejp_468_;
}
v_reusejp_468_:
{
lean_object* v___x_470_; 
v___x_470_ = lean_st_ref_put(v___y_406_, v___x_469_);
v_a_409_ = v___x_415_;
goto v___jp_408_;
}
}
}
else
{
lean_dec_ref(v_a_400_);
return v___x_449_;
}
}
else
{
lean_object* v___x_474_; 
lean_dec_ref(v_a_400_);
if (v_isShared_447_ == 0)
{
v___x_474_ = v___x_446_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_a_444_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
v___jp_408_:
{
size_t v___x_410_; size_t v___x_411_; 
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_403_, v___x_410_);
v_i_403_ = v___x_411_;
v_b_404_ = v_a_409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2___boxed(lean_object* v_a_477_, lean_object* v_as_478_, lean_object* v_sz_479_, lean_object* v_i_480_, lean_object* v_b_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_){
_start:
{
size_t v_sz_boxed_485_; size_t v_i_boxed_486_; lean_object* v_res_487_; 
v_sz_boxed_485_ = lean_unbox_usize(v_sz_479_);
lean_dec(v_sz_479_);
v_i_boxed_486_ = lean_unbox_usize(v_i_480_);
lean_dec(v_i_480_);
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_477_, v_as_478_, v_sz_boxed_485_, v_i_boxed_486_, v_b_481_, v___y_482_, v___y_483_);
lean_dec(v___y_483_);
lean_dec_ref(v___y_482_);
lean_dec_ref(v_as_478_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(lean_object* v_x_489_, lean_object* v_a_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_493_ = ((lean_object*)(l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3));
lean_inc(v_x_489_);
v___x_494_ = l_Lean_Syntax_isOfKind(v_x_489_, v___x_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; 
lean_dec(v_x_489_);
v___x_495_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v___x_495_;
}
else
{
lean_object* v___f_496_; lean_object* v___x_497_; lean_object* v_post_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v_a_502_; lean_object* v___x_525_; 
v___f_496_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___closed__0));
v___x_497_ = lean_unsigned_to_nat(1u);
v_post_498_ = l_Lean_Syntax_getArg(v_x_489_, v___x_497_);
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = l_Lean_Syntax_getArg(v_x_489_, v___x_499_);
lean_dec(v_x_489_);
v___x_525_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_498_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_525_) == 0)
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v___x_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___x_525_, 1);
v_a_502_ = v_a_526_;
goto v___jp_501_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_536_; 
v_a_527_ = lean_ctor_get(v___x_525_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_525_);
if (v_isSharedCheck_536_ == 0)
{
v___x_529_ = v___x_525_;
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_536_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
uint8_t v___x_531_; 
v___x_531_ = l_Lean_Exception_isInterrupt(v_a_527_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
lean_del_object(v___x_529_);
v___x_532_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_527_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_dec_ref_known(v___x_532_, 1);
v_a_502_ = v___f_496_;
goto v___jp_501_;
}
else
{
lean_dec(v___x_500_);
return v___x_532_;
}
}
else
{
lean_object* v___x_534_; 
lean_dec(v___x_500_);
if (v_isShared_530_ == 0)
{
v___x_534_ = v___x_529_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_a_527_);
v___x_534_ = v_reuseFailAlloc_535_;
goto v_reusejp_533_;
}
v_reusejp_533_:
{
return v___x_534_;
}
}
}
}
v___jp_501_:
{
lean_object* v___x_503_; 
v___x_503_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_500_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_503_) == 0)
{
lean_object* v_a_504_; lean_object* v___x_505_; size_t v_sz_506_; size_t v___x_507_; lean_object* v___x_508_; 
v_a_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_a_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = lean_box(0);
v_sz_506_ = lean_array_size(v_a_504_);
v___x_507_ = ((size_t)0ULL);
v___x_508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_502_, v_a_504_, v_sz_506_, v___x_507_, v___x_505_, v_a_490_, v_a_491_);
lean_dec(v_a_504_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_515_; 
v_isSharedCheck_515_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v___x_508_, 0);
lean_dec(v_unused_516_);
v___x_510_ = v___x_508_;
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
else
{
lean_dec(v___x_508_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_515_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
lean_object* v___x_513_; 
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 0, v___x_505_);
v___x_513_ = v___x_510_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_505_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
else
{
return v___x_508_;
}
}
else
{
lean_object* v_a_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_524_; 
lean_dec_ref(v_a_502_);
v_a_517_ = lean_ctor_get(v___x_503_, 0);
v_isSharedCheck_524_ = !lean_is_exclusive(v___x_503_);
if (v_isSharedCheck_524_ == 0)
{
v___x_519_ = v___x_503_;
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_a_517_);
lean_dec(v___x_503_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_524_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___boxed(lean_object* v_x_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(v_x_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(lean_object* v_msgData_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_542_, v___y_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(v_msgData_547_, v___y_548_, v___y_549_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_551_;
}
}
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_PostprocessTraces_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_PostprocessTraces_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_PostprocessTraces_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_PostprocessTraces_PostprocessTracesCommand(builtin);
}
#ifdef __cplusplus
}
#endif
