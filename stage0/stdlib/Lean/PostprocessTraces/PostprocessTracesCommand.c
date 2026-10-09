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
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
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
lean_object* l_Lean_InternalExceptionId_getName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_Elab_isAbortExceptionId(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___closed__0);
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_61_;
v_res_61_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg___boxed(lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v_res_63_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0(lean_object* v_00_u03b1_64_, lean_object* v___y_65_, lean_object* v___y_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v___x_68_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_65_ = stack[1].m_obj;
lean_object* v___y_66_ = stack[2].m_obj;
lean_object* v_res_69_;
v_res_69_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0(lean_box(0), v___y_65_, v___y_66_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___boxed(lean_object* v_00_u03b1_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0(v_00_u03b1_70_, v___y_71_, v___y_72_);
lean_dec(v___y_72_);
lean_dec_ref(v___y_71_);
return v_res_74_;
}
}
lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0(lean_object* v_roots_75_, lean_object* v___y_76_, lean_object* v___y_77_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v_roots_75_);
return v___x_79_;
}
}
LEAN_EXPORT void l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_roots_75_ = stack[0].m_obj;
lean_object* v___y_76_ = stack[1].m_obj;
lean_object* v___y_77_ = stack[2].m_obj;
lean_object* v_res_80_;
v_res_80_ = l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0(v_roots_75_, v___y_76_, v___y_77_);
stack->m_obj
 = v_res_80_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0___boxed(lean_object* v_roots_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___lam__0(v_roots_81_, v___y_82_, v___y_83_);
lean_dec(v___y_83_);
lean_dec_ref(v___y_82_);
return v_res_85_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_86_; 
v___x_86_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_86_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__0);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_89_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_90_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_91_ = lean_unsigned_to_nat(0u);
v___x_92_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set(v___x_92_, 1, v___x_91_);
lean_ctor_set(v___x_92_, 2, v___x_91_);
lean_ctor_set(v___x_92_, 3, v___x_91_);
lean_ctor_set(v___x_92_, 4, v___x_90_);
lean_ctor_set(v___x_92_, 5, v___x_90_);
lean_ctor_set(v___x_92_, 6, v___x_90_);
lean_ctor_set(v___x_92_, 7, v___x_90_);
lean_ctor_set(v___x_92_, 8, v___x_90_);
lean_ctor_set(v___x_92_, 9, v___x_90_);
lean_ctor_set(v___x_92_, 10, v___x_90_);
lean_ctor_set(v___x_92_, 11, v___x_89_);
return v___x_92_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_unsigned_to_nat(32u);
v___x_94_ = lean_mk_empty_array_with_capacity(v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
return v___x_95_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_96_ = ((size_t)5ULL);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_unsigned_to_nat(32u);
v___x_99_ = lean_mk_empty_array_with_capacity(v___x_98_);
v___x_100_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__3);
v___x_101_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v___x_99_);
lean_ctor_set(v___x_101_, 2, v___x_97_);
lean_ctor_set(v___x_101_, 3, v___x_97_);
lean_ctor_set_usize(v___x_101_, 4, v___x_96_);
return v___x_101_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_102_ = lean_box(1);
v___x_103_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__4);
v___x_104_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__1);
v___x_105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___x_103_);
lean_ctor_set(v___x_105_, 2, v___x_102_);
return v___x_105_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_msgData_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; lean_object* v_env_110_; uint8_t v___x_111_; lean_object* v_env_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v_scopes_115_; lean_object* v___x_116_; lean_object* v_opts_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_109_ = lean_st_ref_get(v___y_107_);
v_env_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc_ref(v_env_110_);
lean_dec(v___x_109_);
v___x_111_ = 0;
v_env_112_ = l_Lean_Environment_setRecordingDeps(v_env_110_, v___x_111_);
v___x_113_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_114_ = lean_st_ref_get(v___y_107_);
v_scopes_115_ = lean_ctor_get(v___x_114_, 2);
lean_inc(v_scopes_115_);
lean_dec(v___x_114_);
v___x_116_ = l_List_head_x21___redArg(v___x_113_, v_scopes_115_);
lean_dec(v_scopes_115_);
v_opts_117_ = lean_ctor_get(v___x_116_, 1);
lean_inc_ref(v_opts_117_);
lean_dec(v___x_116_);
v___x_118_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_119_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5);
v___x_120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_120_, 0, v_env_112_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_119_);
lean_ctor_set(v___x_120_, 3, v_opts_117_);
v___x_121_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v_msgData_106_);
v___x_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_122_, 0, v___x_121_);
return v___x_122_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_106_ = stack[0].m_obj;
lean_object* v___y_107_ = stack[1].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_106_, v___y_107_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_124_, v___y_125_);
lean_dec(v___y_125_);
return v_res_127_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_129_, uint8_t v___y_130_, lean_object* v_x_131_){
_start:
{
if (lean_obj_tag(v_x_131_) == 1)
{
lean_object* v_pre_132_; 
v_pre_132_ = lean_ctor_get(v_x_131_, 0);
if (lean_obj_tag(v_pre_132_) == 0)
{
lean_object* v_str_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v_str_133_ = lean_ctor_get(v_x_131_, 1);
v___x_134_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_135_ = lean_string_dec_eq(v_str_133_, v___x_134_);
if (v___x_135_ == 0)
{
return v___x_135_;
}
else
{
return v_suppressElabErrors_129_;
}
}
else
{
return v___y_130_;
}
}
else
{
return v___y_130_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_129_ = stack[0].m_num;
uint8_t v___y_130_ = stack[1].m_num;
lean_object* v_x_131_ = stack[2].m_obj;
uint8_t v_res_136_;
v_res_136_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(v_suppressElabErrors_129_, v___y_130_, v_x_131_);
stack->m_num = v_res_136_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_137_, lean_object* v___y_138_, lean_object* v_x_139_){
_start:
{
uint8_t v_suppressElabErrors_boxed_140_; uint8_t v___y_6063__boxed_141_; uint8_t v_res_142_; lean_object* v_r_143_; 
v_suppressElabErrors_boxed_140_ = lean_unbox(v_suppressElabErrors_137_);
v___y_6063__boxed_141_ = lean_unbox(v___y_138_);
v_res_142_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_140_, v___y_6063__boxed_141_, v_x_139_);
lean_dec(v_x_139_);
v_r_143_ = lean_box(v_res_142_);
return v_r_143_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(lean_object* v_opts_144_, lean_object* v_opt_145_){
_start:
{
lean_object* v_name_146_; lean_object* v_defValue_147_; lean_object* v_map_148_; lean_object* v___x_149_; 
v_name_146_ = lean_ctor_get(v_opt_145_, 0);
v_defValue_147_ = lean_ctor_get(v_opt_145_, 1);
v_map_148_ = lean_ctor_get(v_opts_144_, 0);
v___x_149_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_148_, v_name_146_);
if (lean_obj_tag(v___x_149_) == 0)
{
uint8_t v___x_150_; 
v___x_150_ = lean_unbox(v_defValue_147_);
return v___x_150_;
}
else
{
lean_object* v_val_151_; 
v_val_151_ = lean_ctor_get(v___x_149_, 0);
lean_inc(v_val_151_);
lean_dec_ref_known(v___x_149_, 1);
if (lean_obj_tag(v_val_151_) == 1)
{
uint8_t v_v_152_; 
v_v_152_ = lean_ctor_get_uint8(v_val_151_, 0);
lean_dec_ref_known(v_val_151_, 0);
return v_v_152_;
}
else
{
uint8_t v___x_153_; 
lean_dec(v_val_151_);
v___x_153_ = lean_unbox(v_defValue_147_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_144_ = stack[0].m_obj;
lean_object* v_opt_145_ = stack[1].m_obj;
uint8_t v_res_154_;
v_res_154_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_144_, v_opt_145_);
stack->m_num = v_res_154_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_opts_155_, lean_object* v_opt_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_155_, v_opt_156_);
lean_dec_ref(v_opt_156_);
lean_dec_ref(v_opts_155_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(lean_object* v_ref_160_, lean_object* v_msgData_161_, uint8_t v_severity_162_, uint8_t v_isSilent_163_, lean_object* v___y_164_, lean_object* v___y_165_){
_start:
{
uint8_t v___y_168_; lean_object* v___y_169_; lean_object* v___y_170_; lean_object* v___y_171_; uint8_t v___y_172_; lean_object* v___y_173_; lean_object* v___y_174_; lean_object* v___y_175_; uint8_t v___y_233_; uint8_t v___y_234_; lean_object* v___y_235_; uint8_t v___y_236_; lean_object* v___y_237_; uint8_t v___y_261_; uint8_t v___y_262_; lean_object* v___y_263_; uint8_t v___y_264_; lean_object* v___y_265_; uint8_t v___y_269_; uint8_t v___y_270_; uint8_t v___y_271_; uint8_t v___x_286_; uint8_t v___y_288_; uint8_t v___y_289_; uint8_t v___y_290_; uint8_t v___y_292_; uint8_t v___x_304_; 
v___x_286_ = 2;
v___x_304_ = l_Lean_instBEqMessageSeverity_beq(v_severity_162_, v___x_286_);
if (v___x_304_ == 0)
{
v___y_292_ = v___x_304_;
goto v___jp_291_;
}
else
{
uint8_t v___x_305_; 
lean_inc_ref(v_msgData_161_);
v___x_305_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_161_);
v___y_292_ = v___x_305_;
goto v___jp_291_;
}
v___jp_167_:
{
lean_object* v___x_176_; 
v___x_176_ = l_Lean_Elab_Command_getScope___redArg(v___y_175_);
if (lean_obj_tag(v___x_176_) == 0)
{
lean_object* v_a_177_; lean_object* v_currNamespace_178_; lean_object* v___x_179_; 
v_a_177_ = lean_ctor_get(v___x_176_, 0);
lean_inc(v_a_177_);
lean_dec_ref_known(v___x_176_, 1);
v_currNamespace_178_ = lean_ctor_get(v_a_177_, 2);
lean_inc(v_currNamespace_178_);
lean_dec(v_a_177_);
v___x_179_ = l_Lean_Elab_Command_getScope___redArg(v___y_175_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_215_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_215_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_215_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_215_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v_openDecls_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v_env_189_; lean_object* v_messages_190_; lean_object* v_scopes_191_; lean_object* v_usedQuotCtxts_192_; lean_object* v_nextMacroScope_193_; lean_object* v_maxRecDepth_194_; lean_object* v_ngen_195_; lean_object* v_auxDeclNGen_196_; lean_object* v_infoState_197_; lean_object* v_traceState_198_; lean_object* v_snapshotTasks_199_; lean_object* v_prevLinterStates_200_; lean_object* v_codeQualityEntryTasks_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_214_; 
v_openDecls_184_ = lean_ctor_get(v_a_180_, 3);
lean_inc(v_openDecls_184_);
lean_dec(v_a_180_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_currNamespace_178_);
lean_ctor_set(v___x_185_, 1, v_openDecls_184_);
v___x_186_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___y_170_);
lean_inc_ref(v___y_169_);
lean_inc_ref(v___y_174_);
v___x_187_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_187_, 0, v___y_174_);
lean_ctor_set(v___x_187_, 1, v___y_173_);
lean_ctor_set(v___x_187_, 2, v___y_171_);
lean_ctor_set(v___x_187_, 3, v___y_169_);
lean_ctor_set(v___x_187_, 4, v___x_186_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*5, v___y_172_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*5 + 1, v___y_168_);
lean_ctor_set_uint8(v___x_187_, sizeof(void*)*5 + 2, v_isSilent_163_);
v___x_188_ = lean_st_ref_take(v___y_175_);
v_env_189_ = lean_ctor_get(v___x_188_, 0);
v_messages_190_ = lean_ctor_get(v___x_188_, 1);
v_scopes_191_ = lean_ctor_get(v___x_188_, 2);
v_usedQuotCtxts_192_ = lean_ctor_get(v___x_188_, 3);
v_nextMacroScope_193_ = lean_ctor_get(v___x_188_, 4);
v_maxRecDepth_194_ = lean_ctor_get(v___x_188_, 5);
v_ngen_195_ = lean_ctor_get(v___x_188_, 6);
v_auxDeclNGen_196_ = lean_ctor_get(v___x_188_, 7);
v_infoState_197_ = lean_ctor_get(v___x_188_, 8);
v_traceState_198_ = lean_ctor_get(v___x_188_, 9);
v_snapshotTasks_199_ = lean_ctor_get(v___x_188_, 10);
v_prevLinterStates_200_ = lean_ctor_get(v___x_188_, 11);
v_codeQualityEntryTasks_201_ = lean_ctor_get(v___x_188_, 12);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_214_ == 0)
{
v___x_203_ = v___x_188_;
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_codeQualityEntryTasks_201_);
lean_inc(v_prevLinterStates_200_);
lean_inc(v_snapshotTasks_199_);
lean_inc(v_traceState_198_);
lean_inc(v_infoState_197_);
lean_inc(v_auxDeclNGen_196_);
lean_inc(v_ngen_195_);
lean_inc(v_maxRecDepth_194_);
lean_inc(v_nextMacroScope_193_);
lean_inc(v_usedQuotCtxts_192_);
lean_inc(v_scopes_191_);
lean_inc(v_messages_190_);
lean_inc(v_env_189_);
lean_dec(v___x_188_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_214_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_208_; 
v___x_205_ = lean_box(0);
v___x_206_ = l_Lean_MessageLog_add(v___x_187_, v_messages_190_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___x_206_);
v___x_208_ = v___x_203_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_env_189_);
lean_ctor_set(v_reuseFailAlloc_213_, 1, v___x_206_);
lean_ctor_set(v_reuseFailAlloc_213_, 2, v_scopes_191_);
lean_ctor_set(v_reuseFailAlloc_213_, 3, v_usedQuotCtxts_192_);
lean_ctor_set(v_reuseFailAlloc_213_, 4, v_nextMacroScope_193_);
lean_ctor_set(v_reuseFailAlloc_213_, 5, v_maxRecDepth_194_);
lean_ctor_set(v_reuseFailAlloc_213_, 6, v_ngen_195_);
lean_ctor_set(v_reuseFailAlloc_213_, 7, v_auxDeclNGen_196_);
lean_ctor_set(v_reuseFailAlloc_213_, 8, v_infoState_197_);
lean_ctor_set(v_reuseFailAlloc_213_, 9, v_traceState_198_);
lean_ctor_set(v_reuseFailAlloc_213_, 10, v_snapshotTasks_199_);
lean_ctor_set(v_reuseFailAlloc_213_, 11, v_prevLinterStates_200_);
lean_ctor_set(v_reuseFailAlloc_213_, 12, v_codeQualityEntryTasks_201_);
v___x_208_ = v_reuseFailAlloc_213_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_209_ = lean_st_ref_put(v___y_175_, v___x_208_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_205_);
v___x_211_ = v___x_182_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_205_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec(v_currNamespace_178_);
lean_dec_ref(v___y_173_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
v_a_216_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_179_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_179_);
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
else
{
lean_object* v_a_224_; lean_object* v___x_226_; uint8_t v_isShared_227_; uint8_t v_isSharedCheck_231_; 
lean_dec_ref(v___y_173_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
v_a_224_ = lean_ctor_get(v___x_176_, 0);
v_isSharedCheck_231_ = !lean_is_exclusive(v___x_176_);
if (v_isSharedCheck_231_ == 0)
{
v___x_226_ = v___x_176_;
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
else
{
lean_inc(v_a_224_);
lean_dec(v___x_176_);
v___x_226_ = lean_box(0);
v_isShared_227_ = v_isSharedCheck_231_;
goto v_resetjp_225_;
}
v_resetjp_225_:
{
lean_object* v___x_229_; 
if (v_isShared_227_ == 0)
{
v___x_229_ = v___x_226_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_a_224_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
v___jp_232_:
{
lean_object* v_fileName_238_; lean_object* v_fileMap_239_; uint8_t v_suppressElabErrors_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_259_; 
v_fileName_238_ = lean_ctor_get(v___y_164_, 0);
v_fileMap_239_ = lean_ctor_get(v___y_164_, 1);
v_suppressElabErrors_240_ = lean_ctor_get_uint8(v___y_164_, sizeof(void*)*10);
v___x_241_ = lean_box(v_suppressElabErrors_240_);
v___x_242_ = lean_box(v___y_233_);
v___f_243_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_243_, 0, v___x_241_);
lean_closure_set(v___f_243_, 1, v___x_242_);
v___x_244_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_161_);
v___x_245_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v___x_244_, v___y_165_);
v_a_246_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_259_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_259_ == 0)
{
v___x_248_ = v___x_245_;
v_isShared_249_ = v_isSharedCheck_259_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_245_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_259_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
lean_inc_ref_n(v_fileMap_239_, 2);
v___x_250_ = l_Lean_FileMap_toPosition(v_fileMap_239_, v___y_235_);
lean_dec(v___y_235_);
v___x_251_ = l_Lean_FileMap_toPosition(v_fileMap_239_, v___y_237_);
lean_dec(v___y_237_);
v___x_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
v___x_253_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___closed__0));
if (v_suppressElabErrors_240_ == 0)
{
lean_del_object(v___x_248_);
lean_dec_ref(v___f_243_);
v___y_168_ = v___y_234_;
v___y_169_ = v___x_253_;
v___y_170_ = v_a_246_;
v___y_171_ = v___x_252_;
v___y_172_ = v___y_236_;
v___y_173_ = v___x_250_;
v___y_174_ = v_fileName_238_;
v___y_175_ = v___y_165_;
goto v___jp_167_;
}
else
{
uint8_t v___x_254_; 
lean_inc(v_a_246_);
v___x_254_ = l_Lean_MessageData_hasTag(v___f_243_, v_a_246_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; lean_object* v___x_257_; 
lean_dec_ref_known(v___x_252_, 1);
lean_dec_ref(v___x_250_);
lean_dec(v_a_246_);
v___x_255_ = lean_box(0);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_255_);
v___x_257_ = v___x_248_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
}
}
else
{
lean_del_object(v___x_248_);
v___y_168_ = v___y_234_;
v___y_169_ = v___x_253_;
v___y_170_ = v_a_246_;
v___y_171_ = v___x_252_;
v___y_172_ = v___y_236_;
v___y_173_ = v___x_250_;
v___y_174_ = v_fileName_238_;
v___y_175_ = v___y_165_;
goto v___jp_167_;
}
}
}
}
v___jp_260_:
{
lean_object* v___x_266_; 
v___x_266_ = l_Lean_Syntax_getTailPos_x3f(v___y_263_, v___y_264_);
lean_dec(v___y_263_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_inc(v___y_265_);
v___y_233_ = v___y_261_;
v___y_234_ = v___y_262_;
v___y_235_ = v___y_265_;
v___y_236_ = v___y_264_;
v___y_237_ = v___y_265_;
goto v___jp_232_;
}
else
{
lean_object* v_val_267_; 
v_val_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v___x_266_, 1);
v___y_233_ = v___y_261_;
v___y_234_ = v___y_262_;
v___y_235_ = v___y_265_;
v___y_236_ = v___y_264_;
v___y_237_ = v_val_267_;
goto v___jp_232_;
}
}
v___jp_268_:
{
lean_object* v___x_272_; 
v___x_272_ = l_Lean_Elab_Command_getRef___redArg(v___y_164_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_a_273_; lean_object* v_ref_274_; lean_object* v___x_275_; 
v_a_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_a_273_);
lean_dec_ref_known(v___x_272_, 1);
v_ref_274_ = l_Lean_replaceRef(v_ref_160_, v_a_273_);
lean_dec(v_a_273_);
v___x_275_ = l_Lean_Syntax_getPos_x3f(v_ref_274_, v___y_270_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_276_; 
v___x_276_ = lean_unsigned_to_nat(0u);
v___y_261_ = v___y_269_;
v___y_262_ = v___y_271_;
v___y_263_ = v_ref_274_;
v___y_264_ = v___y_270_;
v___y_265_ = v___x_276_;
goto v___jp_260_;
}
else
{
lean_object* v_val_277_; 
v_val_277_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_val_277_);
lean_dec_ref_known(v___x_275_, 1);
v___y_261_ = v___y_269_;
v___y_262_ = v___y_271_;
v___y_263_ = v_ref_274_;
v___y_264_ = v___y_270_;
v___y_265_ = v_val_277_;
goto v___jp_260_;
}
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
lean_dec_ref(v_msgData_161_);
v_a_278_ = lean_ctor_get(v___x_272_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_272_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_272_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_272_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_283_; 
if (v_isShared_281_ == 0)
{
v___x_283_ = v___x_280_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
v___jp_287_:
{
if (v___y_290_ == 0)
{
v___y_269_ = v___y_288_;
v___y_270_ = v___y_289_;
v___y_271_ = v_severity_162_;
goto v___jp_268_;
}
else
{
v___y_269_ = v___y_288_;
v___y_270_ = v___y_289_;
v___y_271_ = v___x_286_;
goto v___jp_268_;
}
}
v___jp_291_:
{
if (v___y_292_ == 0)
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v_scopes_295_; lean_object* v___x_296_; lean_object* v_opts_297_; uint8_t v___x_298_; uint8_t v___x_299_; 
v___x_293_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_294_ = lean_st_ref_get(v___y_165_);
v_scopes_295_ = lean_ctor_get(v___x_294_, 2);
lean_inc(v_scopes_295_);
lean_dec(v___x_294_);
v___x_296_ = l_List_head_x21___redArg(v___x_293_, v_scopes_295_);
lean_dec(v_scopes_295_);
v_opts_297_ = lean_ctor_get(v___x_296_, 1);
lean_inc_ref(v_opts_297_);
lean_dec(v___x_296_);
v___x_298_ = 1;
v___x_299_ = l_Lean_instBEqMessageSeverity_beq(v_severity_162_, v___x_298_);
if (v___x_299_ == 0)
{
lean_dec_ref(v_opts_297_);
v___y_288_ = v___y_292_;
v___y_289_ = v___y_292_;
v___y_290_ = v___x_299_;
goto v___jp_287_;
}
else
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = l_Lean_warningAsError;
v___x_301_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_297_, v___x_300_);
lean_dec_ref(v_opts_297_);
v___y_288_ = v___y_292_;
v___y_289_ = v___y_292_;
v___y_290_ = v___x_301_;
goto v___jp_287_;
}
}
else
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec_ref(v_msgData_161_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
return v___x_303_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_160_ = stack[0].m_obj;
lean_object* v_msgData_161_ = stack[1].m_obj;
uint8_t v_severity_162_ = stack[2].m_num;
uint8_t v_isSilent_163_ = stack[3].m_num;
lean_object* v___y_164_ = stack[4].m_obj;
lean_object* v___y_165_ = stack[5].m_obj;
lean_object* v_res_306_;
v_res_306_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_160_, v_msgData_161_, v_severity_162_, v_isSilent_163_, v___y_164_, v___y_165_);
stack->m_obj
 = v_res_306_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_307_, lean_object* v_msgData_308_, lean_object* v_severity_309_, lean_object* v_isSilent_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
uint8_t v_severity_boxed_314_; uint8_t v_isSilent_boxed_315_; lean_object* v_res_316_; 
v_severity_boxed_314_ = lean_unbox(v_severity_309_);
v_isSilent_boxed_315_ = lean_unbox(v_isSilent_310_);
v_res_316_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_307_, v_msgData_308_, v_severity_boxed_314_, v_isSilent_boxed_315_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v_ref_307_);
return v_res_316_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(lean_object* v_msgData_317_, uint8_t v_severity_318_, uint8_t v_isSilent_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = l_Lean_Elab_Command_getRef___redArg(v___y_320_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_325_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
lean_inc(v_a_324_);
lean_dec_ref_known(v___x_323_, 1);
v___x_325_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_a_324_, v_msgData_317_, v_severity_318_, v_isSilent_319_, v___y_320_, v___y_321_);
lean_dec(v_a_324_);
return v___x_325_;
}
else
{
lean_object* v_a_326_; lean_object* v___x_328_; uint8_t v_isShared_329_; uint8_t v_isSharedCheck_333_; 
lean_dec_ref(v_msgData_317_);
v_a_326_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_333_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_333_ == 0)
{
v___x_328_ = v___x_323_;
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
else
{
lean_inc(v_a_326_);
lean_dec(v___x_323_);
v___x_328_ = lean_box(0);
v_isShared_329_ = v_isSharedCheck_333_;
goto v_resetjp_327_;
}
v_resetjp_327_:
{
lean_object* v___x_331_; 
if (v_isShared_329_ == 0)
{
v___x_331_ = v___x_328_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_a_326_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_317_ = stack[0].m_obj;
uint8_t v_severity_318_ = stack[1].m_num;
uint8_t v_isSilent_319_ = stack[2].m_num;
lean_object* v___y_320_ = stack[3].m_obj;
lean_object* v___y_321_ = stack[4].m_obj;
lean_object* v_res_334_;
v_res_334_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_317_, v_severity_318_, v_isSilent_319_, v___y_320_, v___y_321_);
stack->m_obj
 = v_res_334_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_335_, lean_object* v_severity_336_, lean_object* v_isSilent_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
uint8_t v_severity_boxed_341_; uint8_t v_isSilent_boxed_342_; lean_object* v_res_343_; 
v_severity_boxed_341_ = lean_unbox(v_severity_336_);
v_isSilent_boxed_342_ = lean_unbox(v_isSilent_337_);
v_res_343_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_335_, v_severity_boxed_341_, v_isSilent_boxed_342_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
return v_res_343_;
}
}
lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
uint8_t v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; 
v___x_348_ = 2;
v___x_349_ = 0;
v___x_350_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_344_, v___x_348_, v___x_349_, v___y_345_, v___y_346_);
return v___x_350_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_344_ = stack[0].m_obj;
lean_object* v___y_345_ = stack[1].m_obj;
lean_object* v___y_346_ = stack[2].m_obj;
lean_object* v_res_351_;
v_res_351_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v_msgData_344_, v___y_345_, v___y_346_);
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2___boxed(lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v_msgData_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
return v_res_356_;
}
}
lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(lean_object* v_ref_357_, lean_object* v_msgData_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
uint8_t v___x_362_; uint8_t v___x_363_; lean_object* v___x_364_; 
v___x_362_ = 2;
v___x_363_ = 0;
v___x_364_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_357_, v_msgData_358_, v___x_362_, v___x_363_, v___y_359_, v___y_360_);
return v___x_364_;
}
}
LEAN_EXPORT void l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_357_ = stack[0].m_obj;
lean_object* v_msgData_358_ = stack[1].m_obj;
lean_object* v___y_359_ = stack[2].m_obj;
lean_object* v___y_360_ = stack[3].m_obj;
lean_object* v_res_365_;
v_res_365_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_357_, v_msgData_358_, v___y_359_, v___y_360_);
stack->m_obj
 = v_res_365_;
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1___boxed(lean_object* v_ref_366_, lean_object* v_msgData_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_366_, v_msgData_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v_ref_366_);
return v_res_371_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1(void){
_start:
{
lean_object* v___x_373_; lean_object* v___x_374_; 
v___x_373_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0));
v___x_374_ = l_Lean_stringToMessageData(v___x_373_);
return v___x_374_;
}
}
lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(lean_object* v_ex_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
if (lean_obj_tag(v_ex_375_) == 0)
{
lean_object* v_ref_379_; lean_object* v_msg_380_; lean_object* v___x_381_; 
v_ref_379_ = lean_ctor_get(v_ex_375_, 0);
lean_inc(v_ref_379_);
v_msg_380_ = lean_ctor_get(v_ex_375_, 1);
lean_inc_ref(v_msg_380_);
lean_dec_ref_known(v_ex_375_, 2);
v___x_381_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_379_, v_msg_380_, v___y_376_, v___y_377_);
lean_dec(v_ref_379_);
return v___x_381_;
}
else
{
lean_object* v_id_382_; uint8_t v___y_384_; uint8_t v___x_406_; 
v_id_382_ = lean_ctor_get(v_ex_375_, 0);
lean_inc(v_id_382_);
v___x_406_ = l_Lean_Elab_isAbortExceptionId(v_id_382_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = l_Lean_Exception_isInterrupt(v_ex_375_);
lean_dec_ref_known(v_ex_375_, 2);
v___y_384_ = v___x_407_;
goto v___jp_383_;
}
else
{
lean_dec_ref_known(v_ex_375_, 2);
v___y_384_ = v___x_406_;
goto v___jp_383_;
}
v___jp_383_:
{
if (v___y_384_ == 0)
{
lean_object* v___x_385_; 
v___x_385_ = l_Lean_InternalExceptionId_getName(v_id_382_);
lean_dec(v_id_382_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v_a_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; 
v_a_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_a_386_);
lean_dec_ref_known(v___x_385_, 1);
v___x_387_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1);
v___x_388_ = l_Lean_MessageData_ofName(v_a_386_);
v___x_389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v___x_389_, v___y_376_, v___y_377_);
return v___x_390_;
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_403_; 
v_a_391_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_403_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_403_ == 0)
{
v___x_393_ = v___x_385_;
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_385_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v_ref_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
v_ref_395_ = lean_ctor_get(v___y_376_, 7);
v___x_396_ = lean_io_error_to_string(v_a_391_);
v___x_397_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_397_, 0, v___x_396_);
v___x_398_ = l_Lean_MessageData_ofFormat(v___x_397_);
lean_inc(v_ref_395_);
v___x_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_399_, 0, v_ref_395_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_399_);
v___x_401_ = v___x_393_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
}
else
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_id_382_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_375_ = stack[0].m_obj;
lean_object* v___y_376_ = stack[1].m_obj;
lean_object* v___y_377_ = stack[2].m_obj;
lean_object* v_res_408_;
v_res_408_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_ex_375_, v___y_376_, v___y_377_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___boxed(lean_object* v_ex_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_ex_409_, v___y_410_, v___y_411_);
lean_dec(v___y_411_);
lean_dec_ref(v___y_410_);
return v_res_413_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(lean_object* v_a_414_, lean_object* v_as_415_, size_t v_sz_416_, size_t v_i_417_, lean_object* v_b_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_a_423_; uint8_t v___x_427_; 
v___x_427_ = lean_usize_dec_lt(v_i_417_, v_sz_416_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec_ref(v_a_414_);
v___x_428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_428_, 0, v_b_418_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v_a_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_429_ = lean_box(0);
v_a_430_ = lean_array_uget_borrowed(v_as_415_, v_i_417_);
lean_inc(v_a_430_);
lean_inc_ref(v_a_414_);
v___x_431_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed), 5, 2);
lean_closure_set(v___x_431_, 0, v_a_414_);
lean_closure_set(v___x_431_, 1, v_a_430_);
v___x_432_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_431_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v_a_433_; 
v_a_433_ = lean_ctor_get(v___x_432_, 0);
lean_inc(v_a_433_);
lean_dec_ref_known(v___x_432_, 1);
if (lean_obj_tag(v_a_433_) == 1)
{
lean_object* v_val_434_; lean_object* v___x_435_; lean_object* v_env_436_; lean_object* v_messages_437_; lean_object* v_scopes_438_; lean_object* v_usedQuotCtxts_439_; lean_object* v_nextMacroScope_440_; lean_object* v_maxRecDepth_441_; lean_object* v_ngen_442_; lean_object* v_auxDeclNGen_443_; lean_object* v_infoState_444_; lean_object* v_traceState_445_; lean_object* v_snapshotTasks_446_; lean_object* v_prevLinterStates_447_; lean_object* v_codeQualityEntryTasks_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_457_; 
v_val_434_ = lean_ctor_get(v_a_433_, 0);
lean_inc(v_val_434_);
lean_dec_ref_known(v_a_433_, 1);
v___x_435_ = lean_st_ref_take(v___y_420_);
v_env_436_ = lean_ctor_get(v___x_435_, 0);
v_messages_437_ = lean_ctor_get(v___x_435_, 1);
v_scopes_438_ = lean_ctor_get(v___x_435_, 2);
v_usedQuotCtxts_439_ = lean_ctor_get(v___x_435_, 3);
v_nextMacroScope_440_ = lean_ctor_get(v___x_435_, 4);
v_maxRecDepth_441_ = lean_ctor_get(v___x_435_, 5);
v_ngen_442_ = lean_ctor_get(v___x_435_, 6);
v_auxDeclNGen_443_ = lean_ctor_get(v___x_435_, 7);
v_infoState_444_ = lean_ctor_get(v___x_435_, 8);
v_traceState_445_ = lean_ctor_get(v___x_435_, 9);
v_snapshotTasks_446_ = lean_ctor_get(v___x_435_, 10);
v_prevLinterStates_447_ = lean_ctor_get(v___x_435_, 11);
v_codeQualityEntryTasks_448_ = lean_ctor_get(v___x_435_, 12);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_435_);
if (v_isSharedCheck_457_ == 0)
{
v___x_450_ = v___x_435_;
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_codeQualityEntryTasks_448_);
lean_inc(v_prevLinterStates_447_);
lean_inc(v_snapshotTasks_446_);
lean_inc(v_traceState_445_);
lean_inc(v_infoState_444_);
lean_inc(v_auxDeclNGen_443_);
lean_inc(v_ngen_442_);
lean_inc(v_maxRecDepth_441_);
lean_inc(v_nextMacroScope_440_);
lean_inc(v_usedQuotCtxts_439_);
lean_inc(v_scopes_438_);
lean_inc(v_messages_437_);
lean_inc(v_env_436_);
lean_dec(v___x_435_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_452_ = l_Lean_MessageLog_add(v_val_434_, v_messages_437_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 1, v___x_452_);
v___x_454_ = v___x_450_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_env_436_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_scopes_438_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_usedQuotCtxts_439_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_nextMacroScope_440_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v_maxRecDepth_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 6, v_ngen_442_);
lean_ctor_set(v_reuseFailAlloc_456_, 7, v_auxDeclNGen_443_);
lean_ctor_set(v_reuseFailAlloc_456_, 8, v_infoState_444_);
lean_ctor_set(v_reuseFailAlloc_456_, 9, v_traceState_445_);
lean_ctor_set(v_reuseFailAlloc_456_, 10, v_snapshotTasks_446_);
lean_ctor_set(v_reuseFailAlloc_456_, 11, v_prevLinterStates_447_);
lean_ctor_set(v_reuseFailAlloc_456_, 12, v_codeQualityEntryTasks_448_);
v___x_454_ = v_reuseFailAlloc_456_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; 
v___x_455_ = lean_st_ref_put(v___y_420_, v___x_454_);
v_a_423_ = v___x_429_;
goto v___jp_422_;
}
}
}
else
{
lean_dec(v_a_433_);
v_a_423_ = v___x_429_;
goto v___jp_422_;
}
}
else
{
lean_object* v_a_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_490_; 
v_a_458_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_490_ == 0)
{
v___x_460_ = v___x_432_;
v_isShared_461_ = v_isSharedCheck_490_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_a_458_);
lean_dec(v___x_432_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_490_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
uint8_t v___x_462_; 
v___x_462_ = l_Lean_Exception_isInterrupt(v_a_458_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_del_object(v___x_460_);
v___x_463_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_458_, v___y_419_, v___y_420_);
if (lean_obj_tag(v___x_463_) == 0)
{
lean_object* v___x_464_; lean_object* v_env_465_; lean_object* v_messages_466_; lean_object* v_scopes_467_; lean_object* v_usedQuotCtxts_468_; lean_object* v_nextMacroScope_469_; lean_object* v_maxRecDepth_470_; lean_object* v_ngen_471_; lean_object* v_auxDeclNGen_472_; lean_object* v_infoState_473_; lean_object* v_traceState_474_; lean_object* v_snapshotTasks_475_; lean_object* v_prevLinterStates_476_; lean_object* v_codeQualityEntryTasks_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_486_; 
lean_dec_ref_known(v___x_463_, 1);
v___x_464_ = lean_st_ref_take(v___y_420_);
v_env_465_ = lean_ctor_get(v___x_464_, 0);
v_messages_466_ = lean_ctor_get(v___x_464_, 1);
v_scopes_467_ = lean_ctor_get(v___x_464_, 2);
v_usedQuotCtxts_468_ = lean_ctor_get(v___x_464_, 3);
v_nextMacroScope_469_ = lean_ctor_get(v___x_464_, 4);
v_maxRecDepth_470_ = lean_ctor_get(v___x_464_, 5);
v_ngen_471_ = lean_ctor_get(v___x_464_, 6);
v_auxDeclNGen_472_ = lean_ctor_get(v___x_464_, 7);
v_infoState_473_ = lean_ctor_get(v___x_464_, 8);
v_traceState_474_ = lean_ctor_get(v___x_464_, 9);
v_snapshotTasks_475_ = lean_ctor_get(v___x_464_, 10);
v_prevLinterStates_476_ = lean_ctor_get(v___x_464_, 11);
v_codeQualityEntryTasks_477_ = lean_ctor_get(v___x_464_, 12);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_464_);
if (v_isSharedCheck_486_ == 0)
{
v___x_479_ = v___x_464_;
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_codeQualityEntryTasks_477_);
lean_inc(v_prevLinterStates_476_);
lean_inc(v_snapshotTasks_475_);
lean_inc(v_traceState_474_);
lean_inc(v_infoState_473_);
lean_inc(v_auxDeclNGen_472_);
lean_inc(v_ngen_471_);
lean_inc(v_maxRecDepth_470_);
lean_inc(v_nextMacroScope_469_);
lean_inc(v_usedQuotCtxts_468_);
lean_inc(v_scopes_467_);
lean_inc(v_messages_466_);
lean_inc(v_env_465_);
lean_dec(v___x_464_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_486_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_inc(v_a_430_);
v___x_481_ = l_Lean_MessageLog_add(v_a_430_, v_messages_466_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_env_465_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_481_);
lean_ctor_set(v_reuseFailAlloc_485_, 2, v_scopes_467_);
lean_ctor_set(v_reuseFailAlloc_485_, 3, v_usedQuotCtxts_468_);
lean_ctor_set(v_reuseFailAlloc_485_, 4, v_nextMacroScope_469_);
lean_ctor_set(v_reuseFailAlloc_485_, 5, v_maxRecDepth_470_);
lean_ctor_set(v_reuseFailAlloc_485_, 6, v_ngen_471_);
lean_ctor_set(v_reuseFailAlloc_485_, 7, v_auxDeclNGen_472_);
lean_ctor_set(v_reuseFailAlloc_485_, 8, v_infoState_473_);
lean_ctor_set(v_reuseFailAlloc_485_, 9, v_traceState_474_);
lean_ctor_set(v_reuseFailAlloc_485_, 10, v_snapshotTasks_475_);
lean_ctor_set(v_reuseFailAlloc_485_, 11, v_prevLinterStates_476_);
lean_ctor_set(v_reuseFailAlloc_485_, 12, v_codeQualityEntryTasks_477_);
v___x_483_ = v_reuseFailAlloc_485_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; 
v___x_484_ = lean_st_ref_put(v___y_420_, v___x_483_);
v_a_423_ = v___x_429_;
goto v___jp_422_;
}
}
}
else
{
if (lean_obj_tag(v___x_463_) == 0)
{
lean_dec_ref_known(v___x_463_, 1);
v_a_423_ = v___x_429_;
goto v___jp_422_;
}
else
{
lean_dec_ref(v_a_414_);
return v___x_463_;
}
}
}
else
{
lean_object* v___x_488_; 
lean_dec_ref(v_a_414_);
if (v_isShared_461_ == 0)
{
v___x_488_ = v___x_460_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_458_);
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
v___jp_422_:
{
size_t v___x_424_; size_t v___x_425_; 
v___x_424_ = ((size_t)1ULL);
v___x_425_ = lean_usize_add(v_i_417_, v___x_424_);
v_i_417_ = v___x_425_;
v_b_418_ = v_a_423_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_414_ = stack[0].m_obj;
lean_object* v_as_415_ = stack[1].m_obj;
size_t v_sz_416_ = stack[2].m_num;
size_t v_i_417_ = stack[3].m_num;
lean_object* v_b_418_ = stack[4].m_obj;
lean_object* v___y_419_ = stack[5].m_obj;
lean_object* v___y_420_ = stack[6].m_obj;
lean_object* v_res_491_;
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_414_, v_as_415_, v_sz_416_, v_i_417_, v_b_418_, v___y_419_, v___y_420_);
stack->m_obj
 = v_res_491_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2___boxed(lean_object* v_a_492_, lean_object* v_as_493_, lean_object* v_sz_494_, lean_object* v_i_495_, lean_object* v_b_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
size_t v_sz_boxed_500_; size_t v_i_boxed_501_; lean_object* v_res_502_; 
v_sz_boxed_500_ = lean_unbox_usize(v_sz_494_);
lean_dec(v_sz_494_);
v_i_boxed_501_ = lean_unbox_usize(v_i_495_);
lean_dec(v_i_495_);
v_res_502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_492_, v_as_493_, v_sz_boxed_500_, v_i_boxed_501_, v_b_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec_ref(v_as_493_);
return v_res_502_;
}
}
lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(lean_object* v_x_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = ((lean_object*)(l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3));
lean_inc(v_x_504_);
v___x_509_ = l_Lean_Syntax_isOfKind(v_x_504_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; 
lean_dec(v_x_504_);
v___x_510_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v___x_510_;
}
else
{
lean_object* v___f_511_; lean_object* v___x_512_; lean_object* v_post_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_a_517_; lean_object* v___y_541_; lean_object* v___x_551_; 
v___f_511_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___closed__0));
v___x_512_ = lean_unsigned_to_nat(1u);
v_post_513_ = l_Lean_Syntax_getArg(v_x_504_, v___x_512_);
v___x_514_ = lean_unsigned_to_nat(3u);
v___x_515_ = l_Lean_Syntax_getArg(v_x_504_, v___x_514_);
lean_dec(v_x_504_);
v___x_551_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_513_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_551_) == 0)
{
v___y_541_ = v___x_551_;
goto v___jp_540_;
}
else
{
lean_object* v_a_552_; uint8_t v___x_553_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v___x_553_ = l_Lean_Exception_isInterrupt(v_a_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; 
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_554_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_552_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_dec_ref_known(v___x_554_, 1);
v_a_517_ = v___f_511_;
goto v___jp_516_;
}
else
{
lean_dec(v___x_515_);
return v___x_554_;
}
}
else
{
v___y_541_ = v___x_551_;
goto v___jp_540_;
}
}
v___jp_516_:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_515_, v_a_505_, v_a_506_);
if (lean_obj_tag(v___x_518_) == 0)
{
lean_object* v_a_519_; lean_object* v___x_520_; size_t v_sz_521_; size_t v___x_522_; lean_object* v___x_523_; 
v_a_519_ = lean_ctor_get(v___x_518_, 0);
lean_inc(v_a_519_);
lean_dec_ref_known(v___x_518_, 1);
v___x_520_ = lean_box(0);
v_sz_521_ = lean_array_size(v_a_519_);
v___x_522_ = ((size_t)0ULL);
v___x_523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_517_, v_a_519_, v_sz_521_, v___x_522_, v___x_520_, v_a_505_, v_a_506_);
lean_dec(v_a_519_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_523_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v___x_523_, 0);
lean_dec(v_unused_531_);
v___x_525_ = v___x_523_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_dec(v___x_523_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_520_);
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_520_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
else
{
return v___x_523_;
}
}
else
{
lean_object* v_a_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec_ref(v_a_517_);
v_a_532_ = lean_ctor_get(v___x_518_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_518_);
if (v_isSharedCheck_539_ == 0)
{
v___x_534_ = v___x_518_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_a_532_);
lean_dec(v___x_518_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_532_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
v___jp_540_:
{
if (lean_obj_tag(v___y_541_) == 0)
{
lean_object* v_a_542_; 
v_a_542_ = lean_ctor_get(v___y_541_, 0);
lean_inc(v_a_542_);
lean_dec_ref_known(v___y_541_, 1);
v_a_517_ = v_a_542_;
goto v___jp_516_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_550_; 
lean_dec(v___x_515_);
v_a_543_ = lean_ctor_get(v___y_541_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___y_541_);
if (v_isSharedCheck_550_ == 0)
{
v___x_545_ = v___y_541_;
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_a_543_);
lean_dec(v___y_541_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_550_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v___x_548_; 
if (v_isShared_546_ == 0)
{
v___x_548_ = v___x_545_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_a_543_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_PostprocessTraces_elabPostprocessTraces_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_504_ = stack[0].m_obj;
lean_object* v_a_505_ = stack[1].m_obj;
lean_object* v_a_506_ = stack[2].m_obj;
lean_object* v_res_555_;
v_res_555_ = l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(v_x_504_, v_a_505_, v_a_506_);
stack->m_obj
 = v_res_555_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___boxed(lean_object* v_x_556_, lean_object* v_a_557_, lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(v_x_556_, v_a_557_, v_a_558_);
lean_dec(v_a_558_);
lean_dec_ref(v_a_557_);
return v_res_560_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(lean_object* v_msgData_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_561_, v___y_563_);
return v___x_565_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_561_ = stack[0].m_obj;
lean_object* v___y_562_ = stack[1].m_obj;
lean_object* v___y_563_ = stack[2].m_obj;
lean_object* v_res_566_;
v_res_566_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(v_msgData_561_, v___y_562_, v___y_563_);
stack->m_obj
 = v_res_566_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(v_msgData_567_, v___y_568_, v___y_569_);
lean_dec(v___y_569_);
lean_dec_ref(v___y_568_);
return v_res_571_;
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
