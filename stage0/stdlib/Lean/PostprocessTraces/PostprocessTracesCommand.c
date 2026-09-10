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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(uint8_t v_suppressElabErrors_122_, uint8_t v___y_123_, lean_object* v_x_124_){
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
return v___x_128_;
}
else
{
return v_suppressElabErrors_122_;
}
}
else
{
return v___y_123_;
}
}
else
{
return v___y_123_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_suppressElabErrors_129_, lean_object* v___y_130_, lean_object* v_x_131_){
_start:
{
uint8_t v_suppressElabErrors_boxed_132_; uint8_t v___y_5976__boxed_133_; uint8_t v_res_134_; lean_object* v_r_135_; 
v_suppressElabErrors_boxed_132_ = lean_unbox(v_suppressElabErrors_129_);
v___y_5976__boxed_133_ = lean_unbox(v___y_130_);
v_res_134_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0(v_suppressElabErrors_boxed_132_, v___y_5976__boxed_133_, v_x_131_);
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
uint8_t v___y_159_; uint8_t v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; lean_object* v___y_163_; lean_object* v___y_164_; lean_object* v___y_165_; lean_object* v___y_166_; uint8_t v___y_224_; uint8_t v___y_225_; uint8_t v___y_226_; lean_object* v___y_227_; lean_object* v___y_228_; uint8_t v___y_252_; uint8_t v___y_253_; uint8_t v___y_254_; lean_object* v___y_255_; lean_object* v___y_256_; uint8_t v___y_260_; uint8_t v___y_261_; uint8_t v___y_262_; uint8_t v___x_277_; uint8_t v___y_279_; uint8_t v___y_280_; uint8_t v___y_281_; uint8_t v___y_283_; uint8_t v___x_295_; 
v___x_277_ = 2;
v___x_295_ = l_Lean_instBEqMessageSeverity_beq(v_severity_153_, v___x_277_);
if (v___x_295_ == 0)
{
v___y_283_ = v___x_295_;
goto v___jp_282_;
}
else
{
uint8_t v___x_296_; 
lean_inc_ref(v_msgData_152_);
v___x_296_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_152_);
v___y_283_ = v___x_296_;
goto v___jp_282_;
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
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_206_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_206_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_206_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_206_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v_currNamespace_175_; lean_object* v_openDecls_176_; lean_object* v_env_177_; lean_object* v_messages_178_; lean_object* v_scopes_179_; lean_object* v_usedQuotCtxts_180_; lean_object* v_nextMacroScope_181_; lean_object* v_maxRecDepth_182_; lean_object* v_ngen_183_; lean_object* v_auxDeclNGen_184_; lean_object* v_infoState_185_; lean_object* v_traceState_186_; lean_object* v_snapshotTasks_187_; lean_object* v_prevLinterStates_188_; lean_object* v_codeQualityEntryTasks_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_205_; 
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
v_codeQualityEntryTasks_189_ = lean_ctor_get(v___x_174_, 12);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_205_ == 0)
{
v___x_191_ = v___x_174_;
v_isShared_192_ = v_isSharedCheck_205_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_codeQualityEntryTasks_189_);
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
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_205_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
v___x_193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_193_, 0, v_currNamespace_175_);
lean_ctor_set(v___x_193_, 1, v_openDecls_176_);
v___x_194_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___y_162_);
lean_inc_ref(v___y_164_);
lean_inc_ref(v___y_165_);
v___x_195_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_195_, 0, v___y_165_);
lean_ctor_set(v___x_195_, 1, v___y_161_);
lean_ctor_set(v___x_195_, 2, v___y_163_);
lean_ctor_set(v___x_195_, 3, v___y_164_);
lean_ctor_set(v___x_195_, 4, v___x_194_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*5, v___y_160_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*5 + 1, v___y_159_);
lean_ctor_set_uint8(v___x_195_, sizeof(void*)*5 + 2, v_isSilent_154_);
v___x_196_ = l_Lean_MessageLog_add(v___x_195_, v_messages_178_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_196_);
v___x_198_ = v___x_191_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_env_177_);
lean_ctor_set(v_reuseFailAlloc_204_, 1, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_204_, 2, v_scopes_179_);
lean_ctor_set(v_reuseFailAlloc_204_, 3, v_usedQuotCtxts_180_);
lean_ctor_set(v_reuseFailAlloc_204_, 4, v_nextMacroScope_181_);
lean_ctor_set(v_reuseFailAlloc_204_, 5, v_maxRecDepth_182_);
lean_ctor_set(v_reuseFailAlloc_204_, 6, v_ngen_183_);
lean_ctor_set(v_reuseFailAlloc_204_, 7, v_auxDeclNGen_184_);
lean_ctor_set(v_reuseFailAlloc_204_, 8, v_infoState_185_);
lean_ctor_set(v_reuseFailAlloc_204_, 9, v_traceState_186_);
lean_ctor_set(v_reuseFailAlloc_204_, 10, v_snapshotTasks_187_);
lean_ctor_set(v_reuseFailAlloc_204_, 11, v_prevLinterStates_188_);
lean_ctor_set(v_reuseFailAlloc_204_, 12, v_codeQualityEntryTasks_189_);
v___x_198_ = v_reuseFailAlloc_204_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_202_; 
v___x_199_ = lean_st_ref_put(v___y_166_, v___x_198_);
v___x_200_ = lean_box(0);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_200_);
v___x_202_ = v___x_172_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_200_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_a_168_);
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec_ref(v___y_161_);
v_a_207_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_169_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_169_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec(v___y_163_);
lean_dec_ref(v___y_162_);
lean_dec_ref(v___y_161_);
v_a_215_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_167_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_167_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
}
}
}
}
v___jp_223_:
{
lean_object* v_fileName_229_; lean_object* v_fileMap_230_; uint8_t v_suppressElabErrors_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v_a_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_250_; 
v_fileName_229_ = lean_ctor_get(v___y_155_, 0);
v_fileMap_230_ = lean_ctor_get(v___y_155_, 1);
v_suppressElabErrors_231_ = lean_ctor_get_uint8(v___y_155_, sizeof(void*)*10);
v___x_232_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_152_);
v___x_233_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v___x_232_, v___y_156_);
v_a_234_ = lean_ctor_get(v___x_233_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v___x_233_);
if (v_isSharedCheck_250_ == 0)
{
v___x_236_ = v___x_233_;
v_isShared_237_ = v_isSharedCheck_250_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_a_234_);
lean_dec(v___x_233_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_250_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; 
lean_inc_ref_n(v_fileMap_230_, 2);
v___x_238_ = l_Lean_FileMap_toPosition(v_fileMap_230_, v___y_227_);
lean_dec(v___y_227_);
v___x_239_ = l_Lean_FileMap_toPosition(v_fileMap_230_, v___y_228_);
lean_dec(v___y_228_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
v___x_241_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___closed__0));
if (v_suppressElabErrors_231_ == 0)
{
lean_del_object(v___x_236_);
v___y_159_ = v___y_225_;
v___y_160_ = v___y_226_;
v___y_161_ = v___x_238_;
v___y_162_ = v_a_234_;
v___y_163_ = v___x_240_;
v___y_164_ = v___x_241_;
v___y_165_ = v_fileName_229_;
v___y_166_ = v___y_156_;
goto v___jp_158_;
}
else
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___f_244_; uint8_t v___x_245_; 
v___x_242_ = lean_box(v_suppressElabErrors_231_);
v___x_243_ = lean_box(v___y_224_);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___lam__0___boxed), 3, 2);
lean_closure_set(v___f_244_, 0, v___x_242_);
lean_closure_set(v___f_244_, 1, v___x_243_);
lean_inc(v_a_234_);
v___x_245_ = l_Lean_MessageData_hasTag(v___f_244_, v_a_234_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_248_; 
lean_dec_ref_known(v___x_240_, 1);
lean_dec_ref(v___x_238_);
lean_dec(v_a_234_);
v___x_246_ = lean_box(0);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_246_);
v___x_248_ = v___x_236_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
return v___x_248_;
}
}
else
{
lean_del_object(v___x_236_);
v___y_159_ = v___y_225_;
v___y_160_ = v___y_226_;
v___y_161_ = v___x_238_;
v___y_162_ = v_a_234_;
v___y_163_ = v___x_240_;
v___y_164_ = v___x_241_;
v___y_165_ = v_fileName_229_;
v___y_166_ = v___y_156_;
goto v___jp_158_;
}
}
}
}
v___jp_251_:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_Syntax_getTailPos_x3f(v___y_255_, v___y_254_);
lean_dec(v___y_255_);
if (lean_obj_tag(v___x_257_) == 0)
{
lean_inc(v___y_256_);
v___y_224_ = v___y_252_;
v___y_225_ = v___y_253_;
v___y_226_ = v___y_254_;
v___y_227_ = v___y_256_;
v___y_228_ = v___y_256_;
goto v___jp_223_;
}
else
{
lean_object* v_val_258_; 
v_val_258_ = lean_ctor_get(v___x_257_, 0);
lean_inc(v_val_258_);
lean_dec_ref_known(v___x_257_, 1);
v___y_224_ = v___y_252_;
v___y_225_ = v___y_253_;
v___y_226_ = v___y_254_;
v___y_227_ = v___y_256_;
v___y_228_ = v_val_258_;
goto v___jp_223_;
}
}
v___jp_259_:
{
lean_object* v___x_263_; 
v___x_263_ = l_Lean_Elab_Command_getRef___redArg(v___y_155_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v_a_264_; lean_object* v_ref_265_; lean_object* v___x_266_; 
v_a_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_a_264_);
lean_dec_ref_known(v___x_263_, 1);
v_ref_265_ = l_Lean_replaceRef(v_ref_151_, v_a_264_);
lean_dec(v_a_264_);
v___x_266_ = l_Lean_Syntax_getPos_x3f(v_ref_265_, v___y_261_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_unsigned_to_nat(0u);
v___y_252_ = v___y_260_;
v___y_253_ = v___y_262_;
v___y_254_ = v___y_261_;
v___y_255_ = v_ref_265_;
v___y_256_ = v___x_267_;
goto v___jp_251_;
}
else
{
lean_object* v_val_268_; 
v_val_268_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_val_268_);
lean_dec_ref_known(v___x_266_, 1);
v___y_252_ = v___y_260_;
v___y_253_ = v___y_262_;
v___y_254_ = v___y_261_;
v___y_255_ = v_ref_265_;
v___y_256_ = v_val_268_;
goto v___jp_251_;
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec_ref(v_msgData_152_);
v_a_269_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_263_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_263_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
v___jp_278_:
{
if (v___y_281_ == 0)
{
v___y_260_ = v___y_279_;
v___y_261_ = v___y_280_;
v___y_262_ = v_severity_153_;
goto v___jp_259_;
}
else
{
v___y_260_ = v___y_279_;
v___y_261_ = v___y_280_;
v___y_262_ = v___x_277_;
goto v___jp_259_;
}
}
v___jp_282_:
{
if (v___y_283_ == 0)
{
lean_object* v___x_284_; lean_object* v_scopes_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v_opts_288_; uint8_t v___x_289_; uint8_t v___x_290_; 
v___x_284_ = lean_st_ref_get(v___y_156_);
v_scopes_285_ = lean_ctor_get(v___x_284_, 2);
lean_inc(v_scopes_285_);
lean_dec(v___x_284_);
v___x_286_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_287_ = l_List_head_x21___redArg(v___x_286_, v_scopes_285_);
lean_dec(v_scopes_285_);
v_opts_288_ = lean_ctor_get(v___x_287_, 1);
lean_inc_ref(v_opts_288_);
lean_dec(v___x_287_);
v___x_289_ = 1;
v___x_290_ = l_Lean_instBEqMessageSeverity_beq(v_severity_153_, v___x_289_);
if (v___x_290_ == 0)
{
lean_dec_ref(v_opts_288_);
v___y_279_ = v___y_283_;
v___y_280_ = v___y_283_;
v___y_281_ = v___x_290_;
goto v___jp_278_;
}
else
{
lean_object* v___x_291_; uint8_t v___x_292_; 
v___x_291_ = l_Lean_warningAsError;
v___x_292_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__5(v_opts_288_, v___x_291_);
lean_dec_ref(v_opts_288_);
v___y_279_ = v___y_283_;
v___y_280_ = v___y_283_;
v___y_281_ = v___x_292_;
goto v___jp_278_;
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec_ref(v_msgData_152_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2___boxed(lean_object* v_ref_297_, lean_object* v_msgData_298_, lean_object* v_severity_299_, lean_object* v_isSilent_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
uint8_t v_severity_boxed_304_; uint8_t v_isSilent_boxed_305_; lean_object* v_res_306_; 
v_severity_boxed_304_ = lean_unbox(v_severity_299_);
v_isSilent_boxed_305_ = lean_unbox(v_isSilent_300_);
v_res_306_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_297_, v_msgData_298_, v_severity_boxed_304_, v_isSilent_boxed_305_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v_ref_297_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(lean_object* v_msgData_307_, uint8_t v_severity_308_, uint8_t v_isSilent_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_Elab_Command_getRef___redArg(v___y_310_);
if (lean_obj_tag(v___x_313_) == 0)
{
lean_object* v_a_314_; lean_object* v___x_315_; 
v_a_314_ = lean_ctor_get(v___x_313_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v___x_313_, 1);
v___x_315_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_a_314_, v_msgData_307_, v_severity_308_, v_isSilent_309_, v___y_310_, v___y_311_);
lean_dec(v_a_314_);
return v___x_315_;
}
else
{
lean_object* v_a_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_323_; 
lean_dec_ref(v_msgData_307_);
v_a_316_ = lean_ctor_get(v___x_313_, 0);
v_isSharedCheck_323_ = !lean_is_exclusive(v___x_313_);
if (v_isSharedCheck_323_ == 0)
{
v___x_318_ = v___x_313_;
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_a_316_);
lean_dec(v___x_313_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_323_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
lean_object* v___x_321_; 
if (v_isShared_319_ == 0)
{
v___x_321_ = v___x_318_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_a_316_);
v___x_321_ = v_reuseFailAlloc_322_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_324_, lean_object* v_severity_325_, lean_object* v_isSilent_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
uint8_t v_severity_boxed_330_; uint8_t v_isSilent_boxed_331_; lean_object* v_res_332_; 
v_severity_boxed_330_ = lean_unbox(v_severity_325_);
v_isSilent_boxed_331_ = lean_unbox(v_isSilent_326_);
v_res_332_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_324_, v_severity_boxed_330_, v_isSilent_boxed_331_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(lean_object* v_msgData_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
uint8_t v___x_337_; uint8_t v___x_338_; lean_object* v___x_339_; 
v___x_337_ = 2;
v___x_338_ = 0;
v___x_339_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2_spec__4(v_msgData_333_, v___x_337_, v___x_338_, v___y_334_, v___y_335_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2___boxed(lean_object* v_msgData_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v_msgData_340_, v___y_341_, v___y_342_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(lean_object* v_ref_345_, lean_object* v_msgData_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
uint8_t v___x_350_; uint8_t v___x_351_; lean_object* v___x_352_; 
v___x_350_ = 2;
v___x_351_ = 0;
v___x_352_ = l_Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2(v_ref_345_, v_msgData_346_, v___x_350_, v___x_351_, v___y_347_, v___y_348_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1___boxed(lean_object* v_ref_353_, lean_object* v_msgData_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_353_, v_msgData_354_, v___y_355_, v___y_356_);
lean_dec(v___y_356_);
lean_dec_ref(v___y_355_);
lean_dec(v_ref_353_);
return v_res_358_;
}
}
static lean_object* _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1(void){
_start:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = ((lean_object*)(l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__0));
v___x_361_ = l_Lean_stringToMessageData(v___x_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(lean_object* v_ex_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
if (lean_obj_tag(v_ex_362_) == 0)
{
lean_object* v_ref_366_; lean_object* v_msg_367_; lean_object* v___x_368_; 
v_ref_366_ = lean_ctor_get(v_ex_362_, 0);
lean_inc(v_ref_366_);
v_msg_367_ = lean_ctor_get(v_ex_362_, 1);
lean_inc_ref(v_msg_367_);
lean_dec_ref_known(v_ex_362_, 2);
v___x_368_ = l_Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1(v_ref_366_, v_msg_367_, v___y_363_, v___y_364_);
lean_dec(v_ref_366_);
return v___x_368_;
}
else
{
lean_object* v_id_369_; uint8_t v___y_371_; uint8_t v___x_393_; 
v_id_369_ = lean_ctor_get(v_ex_362_, 0);
lean_inc(v_id_369_);
v___x_393_ = l_Lean_Elab_isAbortExceptionId(v_id_369_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; 
v___x_394_ = l_Lean_Exception_isInterrupt(v_ex_362_);
lean_dec_ref_known(v_ex_362_, 2);
v___y_371_ = v___x_394_;
goto v___jp_370_;
}
else
{
lean_dec_ref_known(v_ex_362_, 2);
v___y_371_ = v___x_393_;
goto v___jp_370_;
}
v___jp_370_:
{
if (v___y_371_ == 0)
{
lean_object* v___x_372_; 
v___x_372_ = l_Lean_InternalExceptionId_getName(v_id_369_);
lean_dec(v_id_369_);
if (lean_obj_tag(v___x_372_) == 0)
{
lean_object* v_a_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
v_a_373_ = lean_ctor_get(v___x_372_, 0);
lean_inc(v_a_373_);
lean_dec_ref_known(v___x_372_, 1);
v___x_374_ = lean_obj_once(&l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1, &l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1_once, _init_l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1___closed__1);
v___x_375_ = l_Lean_MessageData_ofName(v_a_373_);
v___x_376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = l_Lean_logError___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__2(v___x_376_, v___y_363_, v___y_364_);
return v___x_377_;
}
else
{
lean_object* v_a_378_; lean_object* v___x_380_; uint8_t v_isShared_381_; uint8_t v_isSharedCheck_390_; 
v_a_378_ = lean_ctor_get(v___x_372_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_372_);
if (v_isSharedCheck_390_ == 0)
{
v___x_380_ = v___x_372_;
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
else
{
lean_inc(v_a_378_);
lean_dec(v___x_372_);
v___x_380_ = lean_box(0);
v_isShared_381_ = v_isSharedCheck_390_;
goto v_resetjp_379_;
}
v_resetjp_379_:
{
lean_object* v_ref_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
v_ref_382_ = lean_ctor_get(v___y_363_, 7);
v___x_383_ = lean_io_error_to_string(v_a_378_);
v___x_384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_384_, 0, v___x_383_);
v___x_385_ = l_Lean_MessageData_ofFormat(v___x_384_);
lean_inc(v_ref_382_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_ref_382_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
if (v_isShared_381_ == 0)
{
lean_ctor_set(v___x_380_, 0, v___x_386_);
v___x_388_ = v___x_380_;
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
else
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v_id_369_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
return v___x_392_;
}
}
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
if (lean_obj_tag(v___x_449_) == 0)
{
lean_dec_ref_known(v___x_449_, 1);
v_a_409_ = v___x_415_;
goto v___jp_408_;
}
else
{
lean_dec_ref(v_a_400_);
return v___x_449_;
}
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
lean_object* v___x_496_; lean_object* v_post_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_a_501_; lean_object* v___y_525_; lean_object* v___x_535_; 
v___x_496_ = lean_unsigned_to_nat(1u);
v_post_497_ = l_Lean_Syntax_getArg(v_x_489_, v___x_496_);
v___x_498_ = lean_unsigned_to_nat(3u);
v___x_499_ = l_Lean_Syntax_getArg(v_x_489_, v___x_498_);
lean_dec(v_x_489_);
v___x_535_ = l_Lean_Elab_PostprocessTraces_evalPostprocessorTopLevel(v_post_497_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_535_) == 0)
{
v___y_525_ = v___x_535_;
goto v___jp_524_;
}
else
{
lean_object* v_a_536_; uint8_t v___x_537_; 
v_a_536_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_a_536_);
v___x_537_ = l_Lean_Exception_isInterrupt(v_a_536_);
if (v___x_537_ == 0)
{
lean_object* v___x_538_; 
lean_dec_ref_known(v___x_535_, 1);
v___x_538_ = l_Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1(v_a_536_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___f_539_; 
lean_dec_ref_known(v___x_538_, 1);
v___f_539_ = ((lean_object*)(l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___closed__0));
v_a_501_ = v___f_539_;
goto v___jp_500_;
}
else
{
lean_dec(v___x_499_);
return v___x_538_;
}
}
else
{
lean_dec(v_a_536_);
v___y_525_ = v___x_535_;
goto v___jp_524_;
}
}
v___jp_500_:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_Elab_PostprocessTraces_runAndCollectMessages(v___x_499_, v_a_490_, v_a_491_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v___x_504_; size_t v_sz_505_; size_t v___x_506_; lean_object* v___x_507_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref_known(v___x_502_, 1);
v___x_504_ = lean_box(0);
v_sz_505_ = lean_array_size(v_a_503_);
v___x_506_ = ((size_t)0ULL);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__2(v_a_501_, v_a_503_, v_sz_505_, v___x_506_, v___x_504_, v_a_490_, v_a_491_);
lean_dec(v_a_503_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v___x_507_, 0);
lean_dec(v_unused_515_);
v___x_509_ = v___x_507_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_dec(v___x_507_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 0, v___x_504_);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_504_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
return v___x_507_;
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref(v_a_501_);
v_a_516_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_502_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_502_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
v___jp_524_:
{
if (lean_obj_tag(v___y_525_) == 0)
{
lean_object* v_a_526_; 
v_a_526_ = lean_ctor_get(v___y_525_, 0);
lean_inc(v_a_526_);
lean_dec_ref_known(v___y_525_, 1);
v_a_501_ = v_a_526_;
goto v___jp_500_;
}
else
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v___x_499_);
v_a_527_ = lean_ctor_get(v___y_525_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v___y_525_);
if (v_isSharedCheck_534_ == 0)
{
v___x_529_ = v___y_525_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___y_525_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_527_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_PostprocessTraces_elabPostprocessTraces___boxed(lean_object* v_x_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Lean_Elab_PostprocessTraces_elabPostprocessTraces(v_x_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(lean_object* v_msgData_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___redArg(v_msgData_545_, v___y_547_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4___boxed(lean_object* v_msgData_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logErrorAt___at___00Lean_Elab_logException___at___00Lean_Elab_PostprocessTraces_elabPostprocessTraces_spec__1_spec__1_spec__2_spec__4(v_msgData_550_, v___y_551_, v___y_552_);
lean_dec(v___y_552_);
lean_dec_ref(v___y_551_);
return v_res_554_;
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
