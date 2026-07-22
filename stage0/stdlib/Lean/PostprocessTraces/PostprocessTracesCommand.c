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
uint8_t v___y_6351__boxed_132_; uint8_t v_suppressElabErrors_boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v___y_6351__boxed_132_ = lean_unbox(v___y_129_);
v_suppressElabErrors_boxed_133_ = lean_unbox(v_suppressElabErrors_130_);
v_res_134_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(v___y_6351__boxed_132_, v_suppressElabErrors_boxed_133_, v_x_131_);
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
lean_object* v___y_159_; lean_object* v___y_160_; lean_object* v___y_161_; uint8_t v___y_162_; lean_object* v___y_163_; uint8_t v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; uint8_t v___y_223_; uint8_t v___y_224_; uint8_t v___y_225_; lean_object* v___y_226_; lean_object* v___y_227_; uint8_t v___y_251_; uint8_t v___y_252_; uint8_t v___y_253_; lean_object* v___y_254_; lean_object* v___y_255_; uint8_t v___y_259_; uint8_t v___y_260_; uint8_t v___y_261_; uint8_t v___x_276_; uint8_t v___y_278_; uint8_t v___y_279_; uint8_t v___y_280_; uint8_t v___y_282_; uint8_t v___x_294_; 
v___x_276_ = 2;
v___x_294_ = l_Lean_instBEqMessageSeverity_beq(v_severity_153_, v___x_276_);
if (v___x_294_ == 0)
{
v___y_282_ = v___x_294_;
goto v___jp_281_;
}
else
{
uint8_t v___x_295_; 
lean_inc_ref(v_msgData_152_);
v___x_295_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_152_);
v___y_282_ = v___x_295_;
goto v___jp_281_;
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
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_205_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_205_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_205_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_205_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v_currNamespace_175_; lean_object* v_openDecls_176_; lean_object* v_env_177_; lean_object* v_messages_178_; lean_object* v_scopes_179_; lean_object* v_usedQuotCtxts_180_; lean_object* v_nextMacroScope_181_; lean_object* v_maxRecDepth_182_; lean_object* v_ngen_183_; lean_object* v_auxDeclNGen_184_; lean_object* v_infoState_185_; lean_object* v_traceState_186_; lean_object* v_snapshotTasks_187_; lean_object* v_prevLinterStates_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_204_; 
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
v_prevLinterStates_188_ = lean_ctor_get(v___x_174_, 11);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_204_ == 0)
{
v___x_190_ = v___x_174_;
v_isShared_191_ = v_isSharedCheck_204_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_prevLinterStates_188_);
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
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_204_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_192_, 0, v_currNamespace_175_);
lean_ctor_set(v___x_192_, 1, v_openDecls_176_);
v___x_193_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___y_161_);
lean_inc_ref(v___y_163_);
lean_inc_ref(v___y_165_);
v___x_194_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_194_, 0, v___y_165_);
lean_ctor_set(v___x_194_, 1, v___y_159_);
lean_ctor_set(v___x_194_, 2, v___y_160_);
lean_ctor_set(v___x_194_, 3, v___y_163_);
lean_ctor_set(v___x_194_, 4, v___x_193_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*5, v___y_162_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*5 + 1, v___y_164_);
lean_ctor_set_uint8(v___x_194_, sizeof(void*)*5 + 2, v_isSilent_154_);
v___x_195_ = l_Lean_MessageLog_add(v___x_194_, v_messages_178_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 1, v___x_195_);
v___x_197_ = v___x_190_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_env_177_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_scopes_179_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_usedQuotCtxts_180_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v_nextMacroScope_181_);
lean_ctor_set(v_reuseFailAlloc_203_, 5, v_maxRecDepth_182_);
lean_ctor_set(v_reuseFailAlloc_203_, 6, v_ngen_183_);
lean_ctor_set(v_reuseFailAlloc_203_, 7, v_auxDeclNGen_184_);
lean_ctor_set(v_reuseFailAlloc_203_, 8, v_infoState_185_);
lean_ctor_set(v_reuseFailAlloc_203_, 9, v_traceState_186_);
lean_ctor_set(v_reuseFailAlloc_203_, 10, v_snapshotTasks_187_);
lean_ctor_set(v_reuseFailAlloc_203_, 11, v_prevLinterStates_188_);
v___x_197_ = v_reuseFailAlloc_203_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_198_ = lean_st_ref_set(v___y_166_, v___x_197_);
v___x_199_ = lean_box(0);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_199_);
v___x_201_ = v___x_172_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec(v_a_168_);
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
v_a_206_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_169_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_169_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
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
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec_ref(v___y_161_);
lean_dec(v___y_160_);
lean_dec_ref(v___y_159_);
v_a_214_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_167_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_167_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
v___jp_222_:
{
lean_object* v_fileName_228_; lean_object* v_fileMap_229_; uint8_t v_suppressElabErrors_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v_a_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_249_; 
v_fileName_228_ = lean_ctor_get(v___y_155_, 0);
v_fileMap_229_ = lean_ctor_get(v___y_155_, 1);
v_suppressElabErrors_230_ = lean_ctor_get_uint8(v___y_155_, sizeof(void*)*10);
v___x_231_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_152_);
v___x_232_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v___x_231_, v___y_156_);
v_a_233_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_249_ == 0)
{
v___x_235_ = v___x_232_;
v_isShared_236_ = v_isSharedCheck_249_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_a_233_);
lean_dec(v___x_232_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_249_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; 
lean_inc_ref_n(v_fileMap_229_, 2);
v___x_237_ = l_Lean_FileMap_toPosition(v_fileMap_229_, v___y_226_);
lean_dec(v___y_226_);
v___x_238_ = l_Lean_FileMap_toPosition(v_fileMap_229_, v___y_227_);
lean_dec(v___y_227_);
v___x_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_239_, 0, v___x_238_);
v___x_240_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___closed__0));
if (v_suppressElabErrors_230_ == 0)
{
lean_del_object(v___x_235_);
v___y_159_ = v___x_237_;
v___y_160_ = v___x_239_;
v___y_161_ = v_a_233_;
v___y_162_ = v___y_224_;
v___y_163_ = v___x_240_;
v___y_164_ = v___y_225_;
v___y_165_ = v_fileName_228_;
v___y_166_ = v___y_156_;
goto v___jp_158_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___f_243_; uint8_t v___x_244_; 
v___x_241_ = lean_box(v___y_223_);
v___x_242_ = lean_box(v_suppressElabErrors_230_);
v___f_243_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_243_, 0, v___x_241_);
lean_closure_set(v___f_243_, 1, v___x_242_);
lean_inc(v_a_233_);
v___x_244_ = l_Lean_MessageData_hasTag(v___f_243_, v_a_233_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v___x_247_; 
lean_dec_ref_known(v___x_239_, 1);
lean_dec_ref(v___x_237_);
lean_dec(v_a_233_);
v___x_245_ = lean_box(0);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 0, v___x_245_);
v___x_247_ = v___x_235_;
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
lean_del_object(v___x_235_);
v___y_159_ = v___x_237_;
v___y_160_ = v___x_239_;
v___y_161_ = v_a_233_;
v___y_162_ = v___y_224_;
v___y_163_ = v___x_240_;
v___y_164_ = v___y_225_;
v___y_165_ = v_fileName_228_;
v___y_166_ = v___y_156_;
goto v___jp_158_;
}
}
}
}
v___jp_250_:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_Syntax_getTailPos_x3f(v___y_254_, v___y_252_);
lean_dec(v___y_254_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_inc(v___y_255_);
v___y_223_ = v___y_251_;
v___y_224_ = v___y_252_;
v___y_225_ = v___y_253_;
v___y_226_ = v___y_255_;
v___y_227_ = v___y_255_;
goto v___jp_222_;
}
else
{
lean_object* v_val_257_; 
v_val_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_val_257_);
lean_dec_ref_known(v___x_256_, 1);
v___y_223_ = v___y_251_;
v___y_224_ = v___y_252_;
v___y_225_ = v___y_253_;
v___y_226_ = v___y_255_;
v___y_227_ = v_val_257_;
goto v___jp_222_;
}
}
v___jp_258_:
{
lean_object* v___x_262_; 
v___x_262_ = l_Lean_Elab_Command_getRef___redArg(v___y_155_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v_a_263_; lean_object* v_ref_264_; lean_object* v___x_265_; 
v_a_263_ = lean_ctor_get(v___x_262_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v___x_262_, 1);
v_ref_264_ = l_Lean_replaceRef(v_ref_151_, v_a_263_);
lean_dec(v_a_263_);
v___x_265_ = l_Lean_Syntax_getPos_x3f(v_ref_264_, v___y_260_);
if (lean_obj_tag(v___x_265_) == 0)
{
lean_object* v___x_266_; 
v___x_266_ = lean_unsigned_to_nat(0u);
v___y_251_ = v___y_259_;
v___y_252_ = v___y_260_;
v___y_253_ = v___y_261_;
v___y_254_ = v_ref_264_;
v___y_255_ = v___x_266_;
goto v___jp_250_;
}
else
{
lean_object* v_val_267_; 
v_val_267_ = lean_ctor_get(v___x_265_, 0);
lean_inc(v_val_267_);
lean_dec_ref_known(v___x_265_, 1);
v___y_251_ = v___y_259_;
v___y_252_ = v___y_260_;
v___y_253_ = v___y_261_;
v___y_254_ = v_ref_264_;
v___y_255_ = v_val_267_;
goto v___jp_250_;
}
}
else
{
lean_object* v_a_268_; lean_object* v___x_270_; uint8_t v_isShared_271_; uint8_t v_isSharedCheck_275_; 
lean_dec_ref(v_msgData_152_);
v_a_268_ = lean_ctor_get(v___x_262_, 0);
v_isSharedCheck_275_ = !lean_is_exclusive(v___x_262_);
if (v_isSharedCheck_275_ == 0)
{
v___x_270_ = v___x_262_;
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
else
{
lean_inc(v_a_268_);
lean_dec(v___x_262_);
v___x_270_ = lean_box(0);
v_isShared_271_ = v_isSharedCheck_275_;
goto v_resetjp_269_;
}
v_resetjp_269_:
{
lean_object* v___x_273_; 
if (v_isShared_271_ == 0)
{
v___x_273_ = v___x_270_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
}
v___jp_277_:
{
if (v___y_280_ == 0)
{
v___y_259_ = v___y_278_;
v___y_260_ = v___y_279_;
v___y_261_ = v_severity_153_;
goto v___jp_258_;
}
else
{
v___y_259_ = v___y_278_;
v___y_260_ = v___y_279_;
v___y_261_ = v___x_276_;
goto v___jp_258_;
}
}
v___jp_281_:
{
if (v___y_282_ == 0)
{
lean_object* v___x_283_; lean_object* v_scopes_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v_opts_287_; uint8_t v___x_288_; uint8_t v___x_289_; 
v___x_283_ = lean_st_ref_get(v___y_156_);
v_scopes_284_ = lean_ctor_get(v___x_283_, 2);
lean_inc(v_scopes_284_);
lean_dec(v___x_283_);
v___x_285_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_286_ = l_List_head_x21___redArg(v___x_285_, v_scopes_284_);
lean_dec(v_scopes_284_);
v_opts_287_ = lean_ctor_get(v___x_286_, 1);
lean_inc_ref(v_opts_287_);
lean_dec(v___x_286_);
v___x_288_ = 1;
v___x_289_ = l_Lean_instBEqMessageSeverity_beq(v_severity_153_, v___x_288_);
if (v___x_289_ == 0)
{
lean_dec_ref(v_opts_287_);
v___y_278_ = v___y_282_;
v___y_279_ = v___y_282_;
v___y_280_ = v___x_289_;
goto v___jp_277_;
}
else
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = l_Lean_warningAsError;
v___x_291_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_287_, v___x_290_);
lean_dec_ref(v_opts_287_);
v___y_278_ = v___y_282_;
v___y_279_ = v___y_282_;
v___y_280_ = v___x_291_;
goto v___jp_277_;
}
}
else
{
lean_object* v___x_292_; lean_object* v___x_293_; 
lean_dec_ref(v_msgData_152_);
v___x_292_ = lean_box(0);
v___x_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_296_, lean_object* v_msgData_297_, lean_object* v_severity_298_, lean_object* v_isSilent_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
uint8_t v_severity_boxed_303_; uint8_t v_isSilent_boxed_304_; lean_object* v_res_305_; 
v_severity_boxed_303_ = lean_unbox(v_severity_298_);
v_isSilent_boxed_304_ = lean_unbox(v_isSilent_299_);
v_res_305_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_296_, v_msgData_297_, v_severity_boxed_303_, v_isSilent_boxed_304_, v___y_300_, v___y_301_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v_ref_296_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(lean_object* v_msgData_306_, uint8_t v_severity_307_, uint8_t v_isSilent_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; 
v___x_312_ = l_Lean_Elab_Command_getRef___redArg(v___y_309_);
if (lean_obj_tag(v___x_312_) == 0)
{
lean_object* v_a_313_; lean_object* v___x_314_; 
v_a_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc(v_a_313_);
lean_dec_ref_known(v___x_312_, 1);
v___x_314_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_a_313_, v_msgData_306_, v_severity_307_, v_isSilent_308_, v___y_309_, v___y_310_);
lean_dec(v_a_313_);
return v___x_314_;
}
else
{
lean_object* v_a_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_322_; 
lean_dec_ref(v_msgData_306_);
v_a_315_ = lean_ctor_get(v___x_312_, 0);
v_isSharedCheck_322_ = !lean_is_exclusive(v___x_312_);
if (v_isSharedCheck_322_ == 0)
{
v___x_317_ = v___x_312_;
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_a_315_);
lean_dec(v___x_312_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_322_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_320_; 
if (v_isShared_318_ == 0)
{
v___x_320_ = v___x_317_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v_a_315_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_323_, lean_object* v_severity_324_, lean_object* v_isSilent_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
uint8_t v_severity_boxed_329_; uint8_t v_isSilent_boxed_330_; lean_object* v_res_331_; 
v_severity_boxed_329_ = lean_unbox(v_severity_324_);
v_isSilent_boxed_330_ = lean_unbox(v_isSilent_325_);
v_res_331_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_323_, v_severity_boxed_329_, v_isSilent_boxed_330_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(lean_object* v_msgData_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
uint8_t v___x_336_; uint8_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = 2;
v___x_337_ = 0;
v___x_338_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_332_, v___x_336_, v___x_337_, v___y_333_, v___y_334_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2___boxed(lean_object* v_msgData_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v_msgData_339_, v___y_340_, v___y_341_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(lean_object* v_ref_344_, lean_object* v_msgData_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
uint8_t v___x_349_; uint8_t v___x_350_; lean_object* v___x_351_; 
v___x_349_ = 2;
v___x_350_ = 0;
v___x_351_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_344_, v_msgData_345_, v___x_349_, v___x_350_, v___y_346_, v___y_347_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1___boxed(lean_object* v_ref_352_, lean_object* v_msgData_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_352_, v_msgData_353_, v___y_354_, v___y_355_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v_ref_352_);
return v_res_357_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0));
v___x_360_ = l_Lean_stringToMessageData(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(lean_object* v_ex_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
if (lean_obj_tag(v_ex_361_) == 0)
{
lean_object* v_ref_365_; lean_object* v_msg_366_; lean_object* v___x_367_; 
v_ref_365_ = lean_ctor_get(v_ex_361_, 0);
lean_inc(v_ref_365_);
v_msg_366_ = lean_ctor_get(v_ex_361_, 1);
lean_inc_ref(v_msg_366_);
lean_dec_ref_known(v_ex_361_, 2);
v___x_367_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_365_, v_msg_366_, v___y_362_, v___y_363_);
lean_dec(v_ref_365_);
return v___x_367_;
}
else
{
lean_object* v_id_368_; uint8_t v___y_370_; uint8_t v___x_392_; 
v_id_368_ = lean_ctor_get(v_ex_361_, 0);
lean_inc(v_id_368_);
v___x_392_ = l_Lean_Elab_isAbortExceptionId(v_id_368_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
v___x_393_ = l_Lean_Exception_isInterrupt(v_ex_361_);
lean_dec_ref_known(v_ex_361_, 2);
v___y_370_ = v___x_393_;
goto v___jp_369_;
}
else
{
lean_dec_ref_known(v_ex_361_, 2);
v___y_370_ = v___x_392_;
goto v___jp_369_;
}
v___jp_369_:
{
if (v___y_370_ == 0)
{
lean_object* v___x_371_; 
v___x_371_ = l_Lean_InternalExceptionId_getName(v_id_368_);
lean_dec(v_id_368_);
if (lean_obj_tag(v___x_371_) == 0)
{
lean_object* v_a_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_a_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_a_372_);
lean_dec_ref_known(v___x_371_, 1);
v___x_373_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1);
v___x_374_ = l_Lean_MessageData_ofName(v_a_372_);
v___x_375_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v___x_375_, v___y_362_, v___y_363_);
return v___x_376_;
}
else
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_389_; 
v_a_377_ = lean_ctor_get(v___x_371_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_371_);
if (v_isSharedCheck_389_ == 0)
{
v___x_379_ = v___x_371_;
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_371_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
lean_object* v_ref_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v_ref_381_ = lean_ctor_get(v___y_362_, 7);
v___x_382_ = lean_io_error_to_string(v_a_377_);
v___x_383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
v___x_384_ = l_Lean_MessageData_ofFormat(v___x_383_);
lean_inc(v_ref_381_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v_ref_381_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_385_);
v___x_387_ = v___x_379_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_id_368_);
v___x_390_ = lean_box(0);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___boxed(lean_object* v_ex_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_ex_394_, v___y_395_, v___y_396_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(lean_object* v_a_399_, lean_object* v_as_400_, size_t v_sz_401_, size_t v_i_402_, lean_object* v_b_403_, lean_object* v___y_404_, lean_object* v___y_405_){
_start:
{
lean_object* v_a_408_; uint8_t v___x_412_; 
v___x_412_ = lean_usize_dec_lt(v_i_402_, v_sz_401_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; 
lean_dec_ref(v_a_399_);
v___x_413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_413_, 0, v_b_403_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v_a_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_414_ = lean_box(0);
v_a_415_ = lean_array_uget_borrowed(v_as_400_, v_i_402_);
lean_inc(v_a_415_);
lean_inc_ref(v_a_399_);
v___x_416_ = lean_alloc_closure((void*)(l_Lean_Elab_PostprocessTraces_postprocessMessage___boxed), 5, 2);
lean_closure_set(v___x_416_, 0, v_a_399_);
lean_closure_set(v___x_416_, 1, v_a_415_);
v___x_417_ = l_Lean_Elab_Command_liftCoreM___redArg(v___x_416_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_417_) == 0)
{
lean_object* v_a_418_; 
v_a_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_a_418_);
lean_dec_ref_known(v___x_417_, 1);
if (lean_obj_tag(v_a_418_) == 1)
{
lean_object* v_val_419_; lean_object* v___x_420_; lean_object* v_env_421_; lean_object* v_messages_422_; lean_object* v_scopes_423_; lean_object* v_usedQuotCtxts_424_; lean_object* v_nextMacroScope_425_; lean_object* v_maxRecDepth_426_; lean_object* v_ngen_427_; lean_object* v_auxDeclNGen_428_; lean_object* v_infoState_429_; lean_object* v_traceState_430_; lean_object* v_snapshotTasks_431_; lean_object* v_prevLinterStates_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_441_; 
v_val_419_ = lean_ctor_get(v_a_418_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_a_418_, 1);
v___x_420_ = lean_st_ref_take(v___y_405_);
v_env_421_ = lean_ctor_get(v___x_420_, 0);
v_messages_422_ = lean_ctor_get(v___x_420_, 1);
v_scopes_423_ = lean_ctor_get(v___x_420_, 2);
v_usedQuotCtxts_424_ = lean_ctor_get(v___x_420_, 3);
v_nextMacroScope_425_ = lean_ctor_get(v___x_420_, 4);
v_maxRecDepth_426_ = lean_ctor_get(v___x_420_, 5);
v_ngen_427_ = lean_ctor_get(v___x_420_, 6);
v_auxDeclNGen_428_ = lean_ctor_get(v___x_420_, 7);
v_infoState_429_ = lean_ctor_get(v___x_420_, 8);
v_traceState_430_ = lean_ctor_get(v___x_420_, 9);
v_snapshotTasks_431_ = lean_ctor_get(v___x_420_, 10);
v_prevLinterStates_432_ = lean_ctor_get(v___x_420_, 11);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_441_ == 0)
{
v___x_434_ = v___x_420_;
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_prevLinterStates_432_);
lean_inc(v_snapshotTasks_431_);
lean_inc(v_traceState_430_);
lean_inc(v_infoState_429_);
lean_inc(v_auxDeclNGen_428_);
lean_inc(v_ngen_427_);
lean_inc(v_maxRecDepth_426_);
lean_inc(v_nextMacroScope_425_);
lean_inc(v_usedQuotCtxts_424_);
lean_inc(v_scopes_423_);
lean_inc(v_messages_422_);
lean_inc(v_env_421_);
lean_dec(v___x_420_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_441_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_438_; 
v___x_436_ = l_Lean_MessageLog_add(v_val_419_, v_messages_422_);
if (v_isShared_435_ == 0)
{
lean_ctor_set(v___x_434_, 1, v___x_436_);
v___x_438_ = v___x_434_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_env_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_scopes_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_usedQuotCtxts_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_nextMacroScope_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_maxRecDepth_426_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_ngen_427_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_auxDeclNGen_428_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v_infoState_429_);
lean_ctor_set(v_reuseFailAlloc_440_, 9, v_traceState_430_);
lean_ctor_set(v_reuseFailAlloc_440_, 10, v_snapshotTasks_431_);
lean_ctor_set(v_reuseFailAlloc_440_, 11, v_prevLinterStates_432_);
v___x_438_ = v_reuseFailAlloc_440_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_439_; 
v___x_439_ = lean_st_ref_set(v___y_405_, v___x_438_);
v_a_408_ = v___x_414_;
goto v___jp_407_;
}
}
}
else
{
lean_dec(v_a_418_);
v_a_408_ = v___x_414_;
goto v___jp_407_;
}
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_473_; 
v_a_442_ = lean_ctor_get(v___x_417_, 0);
v_isSharedCheck_473_ = !lean_is_exclusive(v___x_417_);
if (v_isSharedCheck_473_ == 0)
{
v___x_444_ = v___x_417_;
v_isShared_445_ = v_isSharedCheck_473_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_417_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_473_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
uint8_t v___x_446_; 
v___x_446_ = l_Lean_Exception_isInterrupt(v_a_442_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_del_object(v___x_444_);
v___x_447_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_442_, v___y_404_, v___y_405_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; lean_object* v_env_449_; lean_object* v_messages_450_; lean_object* v_scopes_451_; lean_object* v_usedQuotCtxts_452_; lean_object* v_nextMacroScope_453_; lean_object* v_maxRecDepth_454_; lean_object* v_ngen_455_; lean_object* v_auxDeclNGen_456_; lean_object* v_infoState_457_; lean_object* v_traceState_458_; lean_object* v_snapshotTasks_459_; lean_object* v_prevLinterStates_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
lean_dec_ref_known(v___x_447_, 1);
v___x_448_ = lean_st_ref_take(v___y_405_);
v_env_449_ = lean_ctor_get(v___x_448_, 0);
v_messages_450_ = lean_ctor_get(v___x_448_, 1);
v_scopes_451_ = lean_ctor_get(v___x_448_, 2);
v_usedQuotCtxts_452_ = lean_ctor_get(v___x_448_, 3);
v_nextMacroScope_453_ = lean_ctor_get(v___x_448_, 4);
v_maxRecDepth_454_ = lean_ctor_get(v___x_448_, 5);
v_ngen_455_ = lean_ctor_get(v___x_448_, 6);
v_auxDeclNGen_456_ = lean_ctor_get(v___x_448_, 7);
v_infoState_457_ = lean_ctor_get(v___x_448_, 8);
v_traceState_458_ = lean_ctor_get(v___x_448_, 9);
v_snapshotTasks_459_ = lean_ctor_get(v___x_448_, 10);
v_prevLinterStates_460_ = lean_ctor_get(v___x_448_, 11);
v_isSharedCheck_469_ = !lean_is_exclusive(v___x_448_);
if (v_isSharedCheck_469_ == 0)
{
v___x_462_ = v___x_448_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_prevLinterStates_460_);
lean_inc(v_snapshotTasks_459_);
lean_inc(v_traceState_458_);
lean_inc(v_infoState_457_);
lean_inc(v_auxDeclNGen_456_);
lean_inc(v_ngen_455_);
lean_inc(v_maxRecDepth_454_);
lean_inc(v_nextMacroScope_453_);
lean_inc(v_usedQuotCtxts_452_);
lean_inc(v_scopes_451_);
lean_inc(v_messages_450_);
lean_inc(v_env_449_);
lean_dec(v___x_448_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_466_; 
lean_inc(v_a_415_);
v___x_464_ = l_Lean_MessageLog_add(v_a_415_, v_messages_450_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 1, v___x_464_);
v___x_466_ = v___x_462_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_env_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_scopes_451_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_usedQuotCtxts_452_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_nextMacroScope_453_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_maxRecDepth_454_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v_ngen_455_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_auxDeclNGen_456_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_infoState_457_);
lean_ctor_set(v_reuseFailAlloc_468_, 9, v_traceState_458_);
lean_ctor_set(v_reuseFailAlloc_468_, 10, v_snapshotTasks_459_);
lean_ctor_set(v_reuseFailAlloc_468_, 11, v_prevLinterStates_460_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; 
v___x_467_ = lean_st_ref_set(v___y_405_, v___x_466_);
v_a_408_ = v___x_414_;
goto v___jp_407_;
}
}
}
else
{
if (lean_obj_tag(v___x_447_) == 0)
{
lean_dec_ref_known(v___x_447_, 1);
v_a_408_ = v___x_414_;
goto v___jp_407_;
}
else
{
lean_dec_ref(v_a_399_);
return v___x_447_;
}
}
}
else
{
lean_object* v___x_471_; 
lean_dec_ref(v_a_399_);
if (v_isShared_445_ == 0)
{
v___x_471_ = v___x_444_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v_a_442_);
v___x_471_ = v_reuseFailAlloc_472_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
return v___x_471_;
}
}
}
}
}
v___jp_407_:
{
size_t v___x_409_; size_t v___x_410_; 
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_add(v_i_402_, v___x_409_);
v_i_402_ = v___x_410_;
v_b_403_ = v_a_408_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2___boxed(lean_object* v_a_474_, lean_object* v_as_475_, lean_object* v_sz_476_, lean_object* v_i_477_, lean_object* v_b_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
size_t v_sz_boxed_482_; size_t v_i_boxed_483_; lean_object* v_res_484_; 
v_sz_boxed_482_ = lean_unbox_usize(v_sz_476_);
lean_dec(v_sz_476_);
v_i_boxed_483_ = lean_unbox_usize(v_i_477_);
lean_dec(v_i_477_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_474_, v_as_475_, v_sz_boxed_482_, v_i_boxed_483_, v_b_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v_as_475_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(lean_object* v_x_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_PostprocessTraces_postprocessTracesCmd___closed__3));
lean_inc(v_x_486_);
v___x_491_ = l_Lean_Syntax_isOfKind(v_x_486_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; 
lean_dec(v_x_486_);
v___x_492_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__0___redArg();
return v___x_492_;
}
else
{
lean_object* v___x_493_; lean_object* v_post_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v_a_498_; lean_object* v___y_522_; lean_object* v___x_532_; 
v___x_493_ = lean_unsigned_to_nat(1u);
v_post_494_ = l_Lean_Syntax_getArg(v_x_486_, v___x_493_);
v___x_495_ = lean_unsigned_to_nat(3u);
v___x_496_ = l_Lean_Syntax_getArg(v_x_486_, v___x_495_);
lean_dec(v_x_486_);
v___x_532_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_494_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_532_) == 0)
{
v___y_522_ = v___x_532_;
goto v___jp_521_;
}
else
{
lean_object* v_a_533_; uint8_t v___x_534_; 
v_a_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_a_533_);
v___x_534_ = l_Lean_Exception_isInterrupt(v_a_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_dec_ref_known(v___x_532_, 1);
v___x_535_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_533_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_535_) == 0)
{
lean_object* v___f_536_; 
lean_dec_ref_known(v___x_535_, 1);
v___f_536_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___closed__0));
v_a_498_ = v___f_536_;
goto v___jp_497_;
}
else
{
lean_dec(v___x_496_);
return v___x_535_;
}
}
else
{
lean_dec(v_a_533_);
v___y_522_ = v___x_532_;
goto v___jp_521_;
}
}
v___jp_497_:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_496_, v_a_487_, v_a_488_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___x_501_; size_t v_sz_502_; size_t v___x_503_; lean_object* v___x_504_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v___x_501_ = lean_box(0);
v_sz_502_ = lean_array_size(v_a_500_);
v___x_503_ = ((size_t)0ULL);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_498_, v_a_500_, v_sz_502_, v___x_503_, v___x_501_, v_a_487_, v_a_488_);
lean_dec(v_a_500_);
if (lean_obj_tag(v___x_504_) == 0)
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_511_; 
v_isSharedCheck_511_ = !lean_is_exclusive(v___x_504_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v___x_504_, 0);
lean_dec(v_unused_512_);
v___x_506_ = v___x_504_;
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
else
{
lean_dec(v___x_504_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_511_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_509_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 0, v___x_501_);
v___x_509_ = v___x_506_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_501_);
v___x_509_ = v_reuseFailAlloc_510_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
return v___x_509_;
}
}
}
else
{
return v___x_504_;
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec_ref(v_a_498_);
v_a_513_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_499_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_499_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
v___jp_521_:
{
if (lean_obj_tag(v___y_522_) == 0)
{
lean_object* v_a_523_; 
v_a_523_ = lean_ctor_get(v___y_522_, 0);
lean_inc(v_a_523_);
lean_dec_ref_known(v___y_522_, 1);
v_a_498_ = v_a_523_;
goto v___jp_497_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_531_; 
lean_dec(v___x_496_);
v_a_524_ = lean_ctor_get(v___y_522_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v___y_522_);
if (v_isSharedCheck_531_ == 0)
{
v___x_526_ = v___y_522_;
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_a_524_);
lean_dec(v___y_522_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_531_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_529_; 
if (v_isShared_527_ == 0)
{
v___x_529_ = v___x_526_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v_a_524_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
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
