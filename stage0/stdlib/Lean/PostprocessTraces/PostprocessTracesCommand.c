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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
v___x_83_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
v___x_88_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___x_105_; lean_object* v_env_106_; lean_object* v___x_107_; lean_object* v_scopes_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v_opts_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_105_ = lean_st_ref_get(v___y_103_);
v_env_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc_ref(v_env_106_);
lean_dec(v___x_105_);
v___x_107_ = lean_st_ref_get(v___y_103_);
v_scopes_108_ = lean_ctor_get(v___x_107_, 2);
lean_inc(v_scopes_108_);
lean_dec(v___x_107_);
v___x_109_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_110_ = l_List_head_x21___redArg(v___x_109_, v_scopes_108_);
lean_dec(v_scopes_108_);
v_opts_111_ = lean_ctor_get(v___x_110_, 1);
lean_inc_ref(v_opts_111_);
lean_dec(v___x_110_);
v___x_112_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__2);
v___x_113_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___closed__5);
v___x_114_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_114_, 0, v_env_106_);
lean_ctor_set(v___x_114_, 1, v___x_112_);
lean_ctor_set(v___x_114_, 2, v___x_113_);
lean_ctor_set(v___x_114_, 3, v_opts_111_);
v___x_115_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_msgData_102_);
v___x_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg___boxed(lean_object* v_msgData_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_117_, v___y_118_);
lean_dec(v___y_118_);
return v_res_120_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(uint8_t v___y_122_, uint8_t v_suppressElabErrors_123_, lean_object* v_x_124_){
_start:
{
if (lean_obj_tag(v_x_124_) == 1)
{
lean_object* v_pre_125_; 
v_pre_125_ = lean_ctor_get(v_x_124_, 0);
if (lean_obj_tag(v_pre_125_) == 0)
{
lean_object* v_str_126_; lean_object* v___x_127_; uint8_t v___x_128_; 
v_str_126_ = lean_ctor_get(v_x_124_, 1);
v___x_127_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___closed__0));
v___x_128_ = lean_string_dec_eq(v_str_126_, v___x_127_);
if (v___x_128_ == 0)
{
return v___y_122_;
}
else
{
return v_suppressElabErrors_123_;
}
}
else
{
return v___y_122_;
}
}
else
{
return v___y_122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v___y_129_, lean_object* v_suppressElabErrors_130_, lean_object* v_x_131_){
_start:
{
uint8_t v___y_6288__boxed_132_; uint8_t v_suppressElabErrors_boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v___y_6288__boxed_132_ = lean_unbox(v___y_129_);
v_suppressElabErrors_boxed_133_ = lean_unbox(v_suppressElabErrors_130_);
v_res_134_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(v___y_6288__boxed_132_, v_suppressElabErrors_boxed_133_, v_x_131_);
lean_dec(v_x_131_);
v_r_135_ = lean_box(v_res_134_);
return v_r_135_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(lean_object* v_opts_136_, lean_object* v_opt_137_){
_start:
{
lean_object* v_name_138_; lean_object* v_defValue_139_; lean_object* v_map_140_; lean_object* v___x_141_; 
v_name_138_ = lean_ctor_get(v_opt_137_, 0);
v_defValue_139_ = lean_ctor_get(v_opt_137_, 1);
v_map_140_ = lean_ctor_get(v_opts_136_, 0);
v___x_141_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_140_, v_name_138_);
if (lean_obj_tag(v___x_141_) == 0)
{
uint8_t v___x_142_; 
v___x_142_ = lean_unbox(v_defValue_139_);
return v___x_142_;
}
else
{
lean_object* v_val_143_; 
v_val_143_ = lean_ctor_get(v___x_141_, 0);
lean_inc(v_val_143_);
lean_dec_ref_known(v___x_141_, 1);
if (lean_obj_tag(v_val_143_) == 1)
{
uint8_t v_v_144_; 
v_v_144_ = lean_ctor_get_uint8(v_val_143_, 0);
lean_dec_ref_known(v_val_143_, 0);
return v_v_144_;
}
else
{
uint8_t v___x_145_; 
lean_dec(v_val_143_);
v___x_145_ = lean_unbox(v_defValue_139_);
return v___x_145_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_opts_146_, lean_object* v_opt_147_){
_start:
{
uint8_t v_res_148_; lean_object* v_r_149_; 
v_res_148_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_146_, v_opt_147_);
lean_dec_ref(v_opt_147_);
lean_dec_ref(v_opts_146_);
v_r_149_ = lean_box(v_res_148_);
return v_r_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(lean_object* v_ref_151_, lean_object* v_msgData_152_, uint8_t v_severity_153_, uint8_t v_isSilent_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v___y_159_; lean_object* v___y_160_; uint8_t v___y_161_; lean_object* v___y_162_; uint8_t v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; uint8_t v___y_222_; uint8_t v___y_223_; uint8_t v___y_224_; lean_object* v___y_225_; lean_object* v___y_226_; uint8_t v___y_250_; uint8_t v___y_251_; lean_object* v___y_252_; uint8_t v___y_253_; lean_object* v___y_254_; uint8_t v___y_258_; uint8_t v___y_259_; uint8_t v___y_260_; uint8_t v___x_275_; uint8_t v___y_277_; uint8_t v___y_278_; uint8_t v___y_279_; uint8_t v___y_281_; uint8_t v___x_293_; 
v___x_275_ = 2;
v___x_293_ = l_Lean_instBEqMessageSeverity_beq(v_severity_153_, v___x_275_);
if (v___x_293_ == 0)
{
v___y_281_ = v___x_293_;
goto v___jp_280_;
}
else
{
uint8_t v___x_294_; 
lean_inc_ref(v_msgData_152_);
v___x_294_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_152_);
v___y_281_ = v___x_294_;
goto v___jp_280_;
}
v___jp_158_:
{
lean_object* v___x_167_; 
v___x_167_ = l_Lean_Elab_Command_getScope___redArg(v___y_166_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_object* v_a_168_; lean_object* v___x_169_; 
v_a_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_a_168_);
lean_dec_ref_known(v___x_167_, 1);
v___x_169_ = l_Lean_Elab_Command_getScope___redArg(v___y_166_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_204_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_204_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_204_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_204_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v_currNamespace_175_; lean_object* v_openDecls_176_; lean_object* v_env_177_; lean_object* v_messages_178_; lean_object* v_scopes_179_; lean_object* v_usedQuotCtxts_180_; lean_object* v_nextMacroScope_181_; lean_object* v_maxRecDepth_182_; lean_object* v_ngen_183_; lean_object* v_auxDeclNGen_184_; lean_object* v_infoState_185_; lean_object* v_traceState_186_; lean_object* v_snapshotTasks_187_; lean_object* v___x_189_; uint8_t v_isShared_190_; uint8_t v_isSharedCheck_203_; 
v___x_174_ = lean_st_ref_take(v___y_166_);
v_currNamespace_175_ = lean_ctor_get(v_a_168_, 2);
lean_inc(v_currNamespace_175_);
lean_dec(v_a_168_);
v_openDecls_176_ = lean_ctor_get(v_a_170_, 3);
lean_inc(v_openDecls_176_);
lean_dec(v_a_170_);
v_env_177_ = lean_ctor_get(v___x_174_, 0);
v_messages_178_ = lean_ctor_get(v___x_174_, 1);
v_scopes_179_ = lean_ctor_get(v___x_174_, 2);
v_usedQuotCtxts_180_ = lean_ctor_get(v___x_174_, 3);
v_nextMacroScope_181_ = lean_ctor_get(v___x_174_, 4);
v_maxRecDepth_182_ = lean_ctor_get(v___x_174_, 5);
v_ngen_183_ = lean_ctor_get(v___x_174_, 6);
v_auxDeclNGen_184_ = lean_ctor_get(v___x_174_, 7);
v_infoState_185_ = lean_ctor_get(v___x_174_, 8);
v_traceState_186_ = lean_ctor_get(v___x_174_, 9);
v_snapshotTasks_187_ = lean_ctor_get(v___x_174_, 10);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_203_ == 0)
{
v___x_189_ = v___x_174_;
v_isShared_190_ = v_isSharedCheck_203_;
goto v_resetjp_188_;
}
else
{
lean_inc(v_snapshotTasks_187_);
lean_inc(v_traceState_186_);
lean_inc(v_infoState_185_);
lean_inc(v_auxDeclNGen_184_);
lean_inc(v_ngen_183_);
lean_inc(v_maxRecDepth_182_);
lean_inc(v_nextMacroScope_181_);
lean_inc(v_usedQuotCtxts_180_);
lean_inc(v_scopes_179_);
lean_inc(v_messages_178_);
lean_inc(v_env_177_);
lean_dec(v___x_174_);
v___x_189_ = lean_box(0);
v_isShared_190_ = v_isSharedCheck_203_;
goto v_resetjp_188_;
}
v_resetjp_188_:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_191_, 0, v_currNamespace_175_);
lean_ctor_set(v___x_191_, 1, v_openDecls_176_);
v___x_192_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___y_159_);
lean_inc_ref(v___y_165_);
lean_inc_ref(v___y_164_);
v___x_193_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_193_, 0, v___y_164_);
lean_ctor_set(v___x_193_, 1, v___y_162_);
lean_ctor_set(v___x_193_, 2, v___y_160_);
lean_ctor_set(v___x_193_, 3, v___y_165_);
lean_ctor_set(v___x_193_, 4, v___x_192_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*5, v___y_161_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*5 + 1, v___y_163_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*5 + 2, v_isSilent_154_);
v___x_194_ = l_Lean_MessageLog_add(v___x_193_, v_messages_178_);
if (v_isShared_190_ == 0)
{
lean_ctor_set(v___x_189_, 1, v___x_194_);
v___x_196_ = v___x_189_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_env_177_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_scopes_179_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_usedQuotCtxts_180_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_nextMacroScope_181_);
lean_ctor_set(v_reuseFailAlloc_202_, 5, v_maxRecDepth_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 6, v_ngen_183_);
lean_ctor_set(v_reuseFailAlloc_202_, 7, v_auxDeclNGen_184_);
lean_ctor_set(v_reuseFailAlloc_202_, 8, v_infoState_185_);
lean_ctor_set(v_reuseFailAlloc_202_, 9, v_traceState_186_);
lean_ctor_set(v_reuseFailAlloc_202_, 10, v_snapshotTasks_187_);
v___x_196_ = v_reuseFailAlloc_202_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_197_ = lean_st_ref_set(v___y_166_, v___x_196_);
v___x_198_ = lean_box(0);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_198_);
v___x_200_ = v___x_172_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_dec(v_a_168_);
lean_dec_ref(v___y_162_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
v_a_205_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_169_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_169_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v___y_162_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
v_a_213_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_167_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_167_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
v___jp_221_:
{
lean_object* v_fileName_227_; lean_object* v_fileMap_228_; uint8_t v_suppressElabErrors_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_a_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_248_; 
v_fileName_227_ = lean_ctor_get(v___y_155_, 0);
v_fileMap_228_ = lean_ctor_get(v___y_155_, 1);
v_suppressElabErrors_229_ = lean_ctor_get_uint8(v___y_155_, sizeof(void*)*10);
v___x_230_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_152_);
v___x_231_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v___x_230_, v___y_156_);
v_a_232_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_248_ == 0)
{
v___x_234_ = v___x_231_;
v_isShared_235_ = v_isSharedCheck_248_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_a_232_);
lean_dec(v___x_231_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_248_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
lean_inc_ref_n(v_fileMap_228_, 2);
v___x_236_ = l_Lean_FileMap_toPosition(v_fileMap_228_, v___y_225_);
lean_dec(v___y_225_);
v___x_237_ = l_Lean_FileMap_toPosition(v_fileMap_228_, v___y_226_);
lean_dec(v___y_226_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
v___x_239_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___closed__0));
if (v_suppressElabErrors_229_ == 0)
{
lean_del_object(v___x_234_);
v___y_159_ = v_a_232_;
v___y_160_ = v___x_238_;
v___y_161_ = v___y_223_;
v___y_162_ = v___x_236_;
v___y_163_ = v___y_224_;
v___y_164_ = v_fileName_227_;
v___y_165_ = v___x_239_;
v___y_166_ = v___y_156_;
goto v___jp_158_;
}
else
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___f_242_; uint8_t v___x_243_; 
v___x_240_ = lean_box(v___y_222_);
v___x_241_ = lean_box(v_suppressElabErrors_229_);
v___f_242_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_242_, 0, v___x_240_);
lean_closure_set(v___f_242_, 1, v___x_241_);
lean_inc(v_a_232_);
v___x_243_ = l_Lean_MessageData_hasTag(v___f_242_, v_a_232_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_246_; 
lean_dec_ref_known(v___x_238_, 1);
lean_dec_ref(v___x_236_);
lean_dec(v_a_232_);
v___x_244_ = lean_box(0);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 0, v___x_244_);
v___x_246_ = v___x_234_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
else
{
lean_del_object(v___x_234_);
v___y_159_ = v_a_232_;
v___y_160_ = v___x_238_;
v___y_161_ = v___y_223_;
v___y_162_ = v___x_236_;
v___y_163_ = v___y_224_;
v___y_164_ = v_fileName_227_;
v___y_165_ = v___x_239_;
v___y_166_ = v___y_156_;
goto v___jp_158_;
}
}
}
}
v___jp_249_:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Syntax_getTailPos_x3f(v___y_252_, v___y_251_);
lean_dec(v___y_252_);
if (lean_obj_tag(v___x_255_) == 0)
{
lean_inc(v___y_254_);
v___y_222_ = v___y_250_;
v___y_223_ = v___y_251_;
v___y_224_ = v___y_253_;
v___y_225_ = v___y_254_;
v___y_226_ = v___y_254_;
goto v___jp_221_;
}
else
{
lean_object* v_val_256_; 
v_val_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_val_256_);
lean_dec_ref_known(v___x_255_, 1);
v___y_222_ = v___y_250_;
v___y_223_ = v___y_251_;
v___y_224_ = v___y_253_;
v___y_225_ = v___y_254_;
v___y_226_ = v_val_256_;
goto v___jp_221_;
}
}
v___jp_257_:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_Elab_Command_getRef___redArg(v___y_155_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_a_262_; lean_object* v_ref_263_; lean_object* v___x_264_; 
v_a_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_a_262_);
lean_dec_ref_known(v___x_261_, 1);
v_ref_263_ = l_Lean_replaceRef(v_ref_151_, v_a_262_);
lean_dec(v_a_262_);
v___x_264_ = l_Lean_Syntax_getPos_x3f(v_ref_263_, v___y_259_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v___x_265_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___y_250_ = v___y_258_;
v___y_251_ = v___y_259_;
v___y_252_ = v_ref_263_;
v___y_253_ = v___y_260_;
v___y_254_ = v___x_265_;
goto v___jp_249_;
}
else
{
lean_object* v_val_266_; 
v_val_266_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v___x_264_, 1);
v___y_250_ = v___y_258_;
v___y_251_ = v___y_259_;
v___y_252_ = v_ref_263_;
v___y_253_ = v___y_260_;
v___y_254_ = v_val_266_;
goto v___jp_249_;
}
}
else
{
lean_object* v_a_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_274_; 
lean_dec_ref(v_msgData_152_);
v_a_267_ = lean_ctor_get(v___x_261_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v___x_261_);
if (v_isSharedCheck_274_ == 0)
{
v___x_269_ = v___x_261_;
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_a_267_);
lean_dec(v___x_261_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_274_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_270_ == 0)
{
v___x_272_ = v___x_269_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v_a_267_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
v___jp_276_:
{
if (v___y_279_ == 0)
{
v___y_258_ = v___y_277_;
v___y_259_ = v___y_278_;
v___y_260_ = v_severity_153_;
goto v___jp_257_;
}
else
{
v___y_258_ = v___y_277_;
v___y_259_ = v___y_278_;
v___y_260_ = v___x_275_;
goto v___jp_257_;
}
}
v___jp_280_:
{
if (v___y_281_ == 0)
{
lean_object* v___x_282_; lean_object* v_scopes_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v_opts_286_; uint8_t v___x_287_; uint8_t v___x_288_; 
v___x_282_ = lean_st_ref_get(v___y_156_);
v_scopes_283_ = lean_ctor_get(v___x_282_, 2);
lean_inc(v_scopes_283_);
lean_dec(v___x_282_);
v___x_284_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_285_ = l_List_head_x21___redArg(v___x_284_, v_scopes_283_);
lean_dec(v_scopes_283_);
v_opts_286_ = lean_ctor_get(v___x_285_, 1);
lean_inc_ref(v_opts_286_);
lean_dec(v___x_285_);
v___x_287_ = 1;
v___x_288_ = l_Lean_instBEqMessageSeverity_beq(v_severity_153_, v___x_287_);
if (v___x_288_ == 0)
{
lean_dec_ref(v_opts_286_);
v___y_277_ = v___y_281_;
v___y_278_ = v___y_281_;
v___y_279_ = v___x_288_;
goto v___jp_276_;
}
else
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = l_Lean_warningAsError;
v___x_290_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_286_, v___x_289_);
lean_dec_ref(v_opts_286_);
v___y_277_ = v___y_281_;
v___y_278_ = v___y_281_;
v___y_279_ = v___x_290_;
goto v___jp_276_;
}
}
else
{
lean_object* v___x_291_; lean_object* v___x_292_; 
lean_dec_ref(v_msgData_152_);
v___x_291_ = lean_box(0);
v___x_292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_295_, lean_object* v_msgData_296_, lean_object* v_severity_297_, lean_object* v_isSilent_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
uint8_t v_severity_boxed_302_; uint8_t v_isSilent_boxed_303_; lean_object* v_res_304_; 
v_severity_boxed_302_ = lean_unbox(v_severity_297_);
v_isSilent_boxed_303_ = lean_unbox(v_isSilent_298_);
v_res_304_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_295_, v_msgData_296_, v_severity_boxed_302_, v_isSilent_boxed_303_, v___y_299_, v___y_300_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v_ref_295_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(lean_object* v_msgData_305_, uint8_t v_severity_306_, uint8_t v_isSilent_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_Elab_Command_getRef___redArg(v___y_308_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_313_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v___x_313_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_a_312_, v_msgData_305_, v_severity_306_, v_isSilent_307_, v___y_308_, v___y_309_);
lean_dec(v_a_312_);
return v___x_313_;
}
else
{
lean_object* v_a_314_; lean_object* v___x_316_; uint8_t v_isShared_317_; uint8_t v_isSharedCheck_321_; 
lean_dec_ref(v_msgData_305_);
v_a_314_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_321_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_321_ == 0)
{
v___x_316_ = v___x_311_;
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
else
{
lean_inc(v_a_314_);
lean_dec(v___x_311_);
v___x_316_ = lean_box(0);
v_isShared_317_ = v_isSharedCheck_321_;
goto v_resetjp_315_;
}
v_resetjp_315_:
{
lean_object* v___x_319_; 
if (v_isShared_317_ == 0)
{
v___x_319_ = v___x_316_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_a_314_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_322_, lean_object* v_severity_323_, lean_object* v_isSilent_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_){
_start:
{
uint8_t v_severity_boxed_328_; uint8_t v_isSilent_boxed_329_; lean_object* v_res_330_; 
v_severity_boxed_328_ = lean_unbox(v_severity_323_);
v_isSilent_boxed_329_ = lean_unbox(v_isSilent_324_);
v_res_330_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_322_, v_severity_boxed_328_, v_isSilent_boxed_329_, v___y_325_, v___y_326_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(lean_object* v_msgData_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
uint8_t v___x_335_; uint8_t v___x_336_; lean_object* v___x_337_; 
v___x_335_ = 2;
v___x_336_ = 0;
v___x_337_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_331_, v___x_335_, v___x_336_, v___y_332_, v___y_333_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2___boxed(lean_object* v_msgData_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v_msgData_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(lean_object* v_ref_343_, lean_object* v_msgData_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
uint8_t v___x_348_; uint8_t v___x_349_; lean_object* v___x_350_; 
v___x_348_ = 2;
v___x_349_ = 0;
v___x_350_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_343_, v_msgData_344_, v___x_348_, v___x_349_, v___y_345_, v___y_346_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1___boxed(lean_object* v_ref_351_, lean_object* v_msgData_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_351_, v_msgData_352_, v___y_353_, v___y_354_);
lean_dec(v___y_354_);
lean_dec_ref(v___y_353_);
lean_dec(v_ref_351_);
return v_res_356_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0));
v___x_359_ = l_Lean_stringToMessageData(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(lean_object* v_ex_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
if (lean_obj_tag(v_ex_360_) == 0)
{
lean_object* v_ref_364_; lean_object* v_msg_365_; lean_object* v___x_366_; 
v_ref_364_ = lean_ctor_get(v_ex_360_, 0);
lean_inc(v_ref_364_);
v_msg_365_ = lean_ctor_get(v_ex_360_, 1);
lean_inc_ref(v_msg_365_);
lean_dec_ref_known(v_ex_360_, 2);
v___x_366_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_364_, v_msg_365_, v___y_361_, v___y_362_);
lean_dec(v_ref_364_);
return v___x_366_;
}
else
{
lean_object* v_id_367_; uint8_t v___y_369_; uint8_t v___x_391_; 
v_id_367_ = lean_ctor_get(v_ex_360_, 0);
lean_inc(v_id_367_);
v___x_391_ = l_Lean_Elab_isAbortExceptionId(v_id_367_);
if (v___x_391_ == 0)
{
uint8_t v___x_392_; 
v___x_392_ = l_Lean_Exception_isInterrupt(v_ex_360_);
lean_dec_ref_known(v_ex_360_, 2);
v___y_369_ = v___x_392_;
goto v___jp_368_;
}
else
{
lean_dec_ref_known(v_ex_360_, 2);
v___y_369_ = v___x_391_;
goto v___jp_368_;
}
v___jp_368_:
{
if (v___y_369_ == 0)
{
lean_object* v___x_370_; 
v___x_370_ = l_Lean_InternalExceptionId_getName(v_id_367_);
lean_dec(v_id_367_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v_a_371_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_371_);
lean_dec_ref_known(v___x_370_, 1);
v___x_372_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1);
v___x_373_ = l_Lean_MessageData_ofName(v_a_371_);
v___x_374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v___x_374_, v___y_361_, v___y_362_);
return v___x_375_;
}
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_388_; 
v_a_376_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_388_ == 0)
{
v___x_378_ = v___x_370_;
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_370_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_388_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v_ref_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_386_; 
v_ref_380_ = lean_ctor_get(v___y_361_, 7);
v___x_381_ = lean_io_error_to_string(v_a_376_);
v___x_382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
v___x_383_ = l_Lean_MessageData_ofFormat(v___x_382_);
lean_inc(v_ref_380_);
v___x_384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_384_, 0, v_ref_380_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
if (v_isShared_379_ == 0)
{
lean_ctor_set(v___x_378_, 0, v___x_384_);
v___x_386_ = v___x_378_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v___x_389_; lean_object* v___x_390_; 
lean_dec(v_id_367_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___boxed(lean_object* v_ex_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_ex_393_, v___y_394_, v___y_395_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(lean_object* v_a_398_, lean_object* v_as_399_, size_t v_sz_400_, size_t v_i_401_, lean_object* v_b_402_, lean_object* v___y_403_, lean_object* v___y_404_){
_start:
{
lean_object* v_a_407_; uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_lt(v_i_401_, v_sz_400_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; 
lean_dec_ref(v_a_398_);
v___x_412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_412_, 0, v_b_402_);
return v___x_412_;
}
else
{
lean_object* v___x_413_; lean_object* v_a_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v___x_413_ = lean_box(0);
v_a_414_ = lean_array_uget_borrowed(v_as_399_, v_i_401_);
lean_inc(v_a_414_);
lean_inc_ref(v_a_398_);
v___x_415_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed), 5, 2);
lean_closure_set(v___x_415_, 0, v_a_398_);
lean_closure_set(v___x_415_, 1, v_a_414_);
v___x_416_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_415_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_416_) == 0)
{
lean_object* v_a_417_; 
v_a_417_ = lean_ctor_get(v___x_416_, 0);
lean_inc(v_a_417_);
lean_dec_ref_known(v___x_416_, 1);
if (lean_obj_tag(v_a_417_) == 1)
{
lean_object* v_val_418_; lean_object* v___x_419_; lean_object* v_env_420_; lean_object* v_messages_421_; lean_object* v_scopes_422_; lean_object* v_usedQuotCtxts_423_; lean_object* v_nextMacroScope_424_; lean_object* v_maxRecDepth_425_; lean_object* v_ngen_426_; lean_object* v_auxDeclNGen_427_; lean_object* v_infoState_428_; lean_object* v_traceState_429_; lean_object* v_snapshotTasks_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_439_; 
v_val_418_ = lean_ctor_get(v_a_417_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v_a_417_, 1);
v___x_419_ = lean_st_ref_take(v___y_404_);
v_env_420_ = lean_ctor_get(v___x_419_, 0);
v_messages_421_ = lean_ctor_get(v___x_419_, 1);
v_scopes_422_ = lean_ctor_get(v___x_419_, 2);
v_usedQuotCtxts_423_ = lean_ctor_get(v___x_419_, 3);
v_nextMacroScope_424_ = lean_ctor_get(v___x_419_, 4);
v_maxRecDepth_425_ = lean_ctor_get(v___x_419_, 5);
v_ngen_426_ = lean_ctor_get(v___x_419_, 6);
v_auxDeclNGen_427_ = lean_ctor_get(v___x_419_, 7);
v_infoState_428_ = lean_ctor_get(v___x_419_, 8);
v_traceState_429_ = lean_ctor_get(v___x_419_, 9);
v_snapshotTasks_430_ = lean_ctor_get(v___x_419_, 10);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_419_);
if (v_isSharedCheck_439_ == 0)
{
v___x_432_ = v___x_419_;
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_snapshotTasks_430_);
lean_inc(v_traceState_429_);
lean_inc(v_infoState_428_);
lean_inc(v_auxDeclNGen_427_);
lean_inc(v_ngen_426_);
lean_inc(v_maxRecDepth_425_);
lean_inc(v_nextMacroScope_424_);
lean_inc(v_usedQuotCtxts_423_);
lean_inc(v_scopes_422_);
lean_inc(v_messages_421_);
lean_inc(v_env_420_);
lean_dec(v___x_419_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_439_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_434_ = l_Lean_MessageLog_add(v_val_418_, v_messages_421_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v___x_434_);
v___x_436_ = v___x_432_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_env_420_);
lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_438_, 2, v_scopes_422_);
lean_ctor_set(v_reuseFailAlloc_438_, 3, v_usedQuotCtxts_423_);
lean_ctor_set(v_reuseFailAlloc_438_, 4, v_nextMacroScope_424_);
lean_ctor_set(v_reuseFailAlloc_438_, 5, v_maxRecDepth_425_);
lean_ctor_set(v_reuseFailAlloc_438_, 6, v_ngen_426_);
lean_ctor_set(v_reuseFailAlloc_438_, 7, v_auxDeclNGen_427_);
lean_ctor_set(v_reuseFailAlloc_438_, 8, v_infoState_428_);
lean_ctor_set(v_reuseFailAlloc_438_, 9, v_traceState_429_);
lean_ctor_set(v_reuseFailAlloc_438_, 10, v_snapshotTasks_430_);
v___x_436_ = v_reuseFailAlloc_438_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; 
v___x_437_ = lean_st_ref_set(v___y_404_, v___x_436_);
v_a_407_ = v___x_413_;
goto v___jp_406_;
}
}
}
else
{
lean_dec(v_a_417_);
v_a_407_ = v___x_413_;
goto v___jp_406_;
}
}
else
{
lean_object* v_a_440_; lean_object* v___x_442_; uint8_t v_isShared_443_; uint8_t v_isSharedCheck_470_; 
v_a_440_ = lean_ctor_get(v___x_416_, 0);
v_isSharedCheck_470_ = !lean_is_exclusive(v___x_416_);
if (v_isSharedCheck_470_ == 0)
{
v___x_442_ = v___x_416_;
v_isShared_443_ = v_isSharedCheck_470_;
goto v_resetjp_441_;
}
else
{
lean_inc(v_a_440_);
lean_dec(v___x_416_);
v___x_442_ = lean_box(0);
v_isShared_443_ = v_isSharedCheck_470_;
goto v_resetjp_441_;
}
v_resetjp_441_:
{
uint8_t v___x_444_; 
v___x_444_ = l_Lean_Exception_isInterrupt(v_a_440_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_del_object(v___x_442_);
v___x_445_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_440_, v___y_403_, v___y_404_);
if (lean_obj_tag(v___x_445_) == 0)
{
lean_object* v___x_446_; lean_object* v_env_447_; lean_object* v_messages_448_; lean_object* v_scopes_449_; lean_object* v_usedQuotCtxts_450_; lean_object* v_nextMacroScope_451_; lean_object* v_maxRecDepth_452_; lean_object* v_ngen_453_; lean_object* v_auxDeclNGen_454_; lean_object* v_infoState_455_; lean_object* v_traceState_456_; lean_object* v_snapshotTasks_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_466_; 
lean_dec_ref_known(v___x_445_, 1);
v___x_446_ = lean_st_ref_take(v___y_404_);
v_env_447_ = lean_ctor_get(v___x_446_, 0);
v_messages_448_ = lean_ctor_get(v___x_446_, 1);
v_scopes_449_ = lean_ctor_get(v___x_446_, 2);
v_usedQuotCtxts_450_ = lean_ctor_get(v___x_446_, 3);
v_nextMacroScope_451_ = lean_ctor_get(v___x_446_, 4);
v_maxRecDepth_452_ = lean_ctor_get(v___x_446_, 5);
v_ngen_453_ = lean_ctor_get(v___x_446_, 6);
v_auxDeclNGen_454_ = lean_ctor_get(v___x_446_, 7);
v_infoState_455_ = lean_ctor_get(v___x_446_, 8);
v_traceState_456_ = lean_ctor_get(v___x_446_, 9);
v_snapshotTasks_457_ = lean_ctor_get(v___x_446_, 10);
v_isSharedCheck_466_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_466_ == 0)
{
v___x_459_ = v___x_446_;
v_isShared_460_ = v_isSharedCheck_466_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_snapshotTasks_457_);
lean_inc(v_traceState_456_);
lean_inc(v_infoState_455_);
lean_inc(v_auxDeclNGen_454_);
lean_inc(v_ngen_453_);
lean_inc(v_maxRecDepth_452_);
lean_inc(v_nextMacroScope_451_);
lean_inc(v_usedQuotCtxts_450_);
lean_inc(v_scopes_449_);
lean_inc(v_messages_448_);
lean_inc(v_env_447_);
lean_dec(v___x_446_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_466_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_463_; 
lean_inc(v_a_414_);
v___x_461_ = l_Lean_MessageLog_add(v_a_414_, v_messages_448_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v___x_461_);
v___x_463_ = v___x_459_;
goto v_reusejp_462_;
}
else
{
lean_object* v_reuseFailAlloc_465_; 
v_reuseFailAlloc_465_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_465_, 0, v_env_447_);
lean_ctor_set(v_reuseFailAlloc_465_, 1, v___x_461_);
lean_ctor_set(v_reuseFailAlloc_465_, 2, v_scopes_449_);
lean_ctor_set(v_reuseFailAlloc_465_, 3, v_usedQuotCtxts_450_);
lean_ctor_set(v_reuseFailAlloc_465_, 4, v_nextMacroScope_451_);
lean_ctor_set(v_reuseFailAlloc_465_, 5, v_maxRecDepth_452_);
lean_ctor_set(v_reuseFailAlloc_465_, 6, v_ngen_453_);
lean_ctor_set(v_reuseFailAlloc_465_, 7, v_auxDeclNGen_454_);
lean_ctor_set(v_reuseFailAlloc_465_, 8, v_infoState_455_);
lean_ctor_set(v_reuseFailAlloc_465_, 9, v_traceState_456_);
lean_ctor_set(v_reuseFailAlloc_465_, 10, v_snapshotTasks_457_);
v___x_463_ = v_reuseFailAlloc_465_;
goto v_reusejp_462_;
}
v_reusejp_462_:
{
lean_object* v___x_464_; 
v___x_464_ = lean_st_ref_set(v___y_404_, v___x_463_);
v_a_407_ = v___x_413_;
goto v___jp_406_;
}
}
}
else
{
if (lean_obj_tag(v___x_445_) == 0)
{
lean_dec_ref_known(v___x_445_, 1);
v_a_407_ = v___x_413_;
goto v___jp_406_;
}
else
{
lean_dec_ref(v_a_398_);
return v___x_445_;
}
}
}
else
{
lean_object* v___x_468_; 
lean_dec_ref(v_a_398_);
if (v_isShared_443_ == 0)
{
v___x_468_ = v___x_442_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_a_440_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
return v___x_468_;
}
}
}
}
}
v___jp_406_:
{
size_t v___x_408_; size_t v___x_409_; 
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_add(v_i_401_, v___x_408_);
v_i_401_ = v___x_409_;
v_b_402_ = v_a_407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2___boxed(lean_object* v_a_471_, lean_object* v_as_472_, lean_object* v_sz_473_, lean_object* v_i_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
size_t v_sz_boxed_479_; size_t v_i_boxed_480_; lean_object* v_res_481_; 
v_sz_boxed_479_ = lean_unbox_usize(v_sz_473_);
lean_dec(v_sz_473_);
v_i_boxed_480_ = lean_unbox_usize(v_i_474_);
lean_dec(v_i_474_);
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_471_, v_as_472_, v_sz_boxed_479_, v_i_boxed_480_, v_b_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec_ref(v_as_472_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(lean_object* v_x_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_487_ = ((lean_object*)(l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3));
lean_inc(v_x_483_);
v___x_488_ = l_Lean_Syntax_isOfKind(v_x_483_, v___x_487_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; 
lean_dec(v_x_483_);
v___x_489_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v___x_489_;
}
else
{
lean_object* v___x_490_; lean_object* v_post_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_a_495_; lean_object* v___y_519_; lean_object* v___x_529_; 
v___x_490_ = lean_unsigned_to_nat(1u);
v_post_491_ = l_Lean_Syntax_getArg(v_x_483_, v___x_490_);
v___x_492_ = lean_unsigned_to_nat(3u);
v___x_493_ = l_Lean_Syntax_getArg(v_x_483_, v___x_492_);
lean_dec(v_x_483_);
v___x_529_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_491_, v_a_484_, v_a_485_);
if (lean_obj_tag(v___x_529_) == 0)
{
v___y_519_ = v___x_529_;
goto v___jp_518_;
}
else
{
lean_object* v_a_530_; uint8_t v___x_531_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
v___x_531_ = l_Lean_Exception_isInterrupt(v_a_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
lean_dec_ref_known(v___x_529_, 1);
v___x_532_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_530_, v_a_484_, v_a_485_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v___f_533_; 
lean_dec_ref_known(v___x_532_, 1);
v___f_533_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___closed__0));
v_a_495_ = v___f_533_;
goto v___jp_494_;
}
else
{
lean_dec(v___x_493_);
return v___x_532_;
}
}
else
{
lean_dec(v_a_530_);
v___y_519_ = v___x_529_;
goto v___jp_518_;
}
}
v___jp_494_:
{
lean_object* v___x_496_; 
v___x_496_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_493_, v_a_484_, v_a_485_);
if (lean_obj_tag(v___x_496_) == 0)
{
lean_object* v_a_497_; lean_object* v___x_498_; size_t v_sz_499_; size_t v___x_500_; lean_object* v___x_501_; 
v_a_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_a_497_);
lean_dec_ref_known(v___x_496_, 1);
v___x_498_ = lean_box(0);
v_sz_499_ = lean_array_size(v_a_497_);
v___x_500_ = ((size_t)0ULL);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_495_, v_a_497_, v_sz_499_, v___x_500_, v___x_498_, v_a_484_, v_a_485_);
lean_dec(v_a_497_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_508_; 
v_isSharedCheck_508_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; 
v_unused_509_ = lean_ctor_get(v___x_501_, 0);
lean_dec(v_unused_509_);
v___x_503_ = v___x_501_;
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
else
{
lean_dec(v___x_501_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_508_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 0, v___x_498_);
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_498_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
return v___x_501_;
}
}
else
{
lean_object* v_a_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_517_; 
lean_dec_ref(v_a_495_);
v_a_510_ = lean_ctor_get(v___x_496_, 0);
v_isSharedCheck_517_ = !lean_is_exclusive(v___x_496_);
if (v_isSharedCheck_517_ == 0)
{
v___x_512_ = v___x_496_;
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_a_510_);
lean_dec(v___x_496_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_517_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_515_; 
if (v_isShared_513_ == 0)
{
v___x_515_ = v___x_512_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_a_510_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
return v___x_515_;
}
}
}
}
v___jp_518_:
{
if (lean_obj_tag(v___y_519_) == 0)
{
lean_object* v_a_520_; 
v_a_520_ = lean_ctor_get(v___y_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___y_519_, 1);
v_a_495_ = v_a_520_;
goto v___jp_494_;
}
else
{
lean_object* v_a_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_528_; 
lean_dec(v___x_493_);
v_a_521_ = lean_ctor_get(v___y_519_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___y_519_);
if (v_isSharedCheck_528_ == 0)
{
v___x_523_ = v___y_519_;
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_a_521_);
lean_dec(v___y_519_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_528_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v___x_526_; 
if (v_isShared_524_ == 0)
{
v___x_526_ = v___x_523_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_a_521_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___boxed(lean_object* v_x_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_){
_start:
{
lean_object* v_res_538_; 
v_res_538_ = l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(v_x_534_, v_a_535_, v_a_536_);
lean_dec(v_a_536_);
lean_dec_ref(v_a_535_);
return v_res_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(lean_object* v_msgData_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_539_, v___y_541_);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(v_msgData_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
return v_res_548_;
}
}
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_PostprocessTraces_PostprocessTracesCommand(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
