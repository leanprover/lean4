// Lean compiler output
// Module: Lean.Elab.InfoTrees
// Imports: public import Lean.Elab.Command
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
lean_object* l_Lean_Elab_Command_getScope___redArg(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_Command_getRef___redArg(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_InfoTree_format(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_error_to_string(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object*);
lean_object* lean_task_get_own(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "infoTreesCmd"};
static const lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 96, 116, 19, 43, 63, 104, 107)}};
static const lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 51, .m_data = "Info trees are disabled, can not use `#info_trees`."};
static const lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__3_value)}};
static const lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__0_value;
static const lean_string_object l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "InfoTrees"};
static const lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "elabInfoTrees"};
static const lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__3 = (const lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__3_value;
static const lean_ctor_object l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_1),((lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(161, 230, 229, 85, 182, 144, 182, 176)}};
static const lean_ctor_object l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_2),((lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(145, 196, 130, 195, 127, 154, 35, 89)}};
static const lean_ctor_object l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value_aux_3),((lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(211, 70, 3, 71, 156, 165, 10, 229)}};
static const lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4 = (const lean_object*)&l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_7_;
v_res_7_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
stack->m_obj
 = v_res_7_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___boxed(lean_object* v___y_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
return v_res_9_;
}
}
lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0(lean_object* v_00_u03b1_10_, lean_object* v___y_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
return v___x_14_;
}
}
LEAN_EXPORT void l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_11_ = stack[1].m_obj;
lean_object* v___y_12_ = stack[2].m_obj;
lean_object* v_res_15_;
v_res_15_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0(lean_box(0), v___y_11_, v___y_12_);
stack->m_obj
 = v_res_15_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___boxed(lean_object* v_00_u03b1_16_, lean_object* v___y_17_, lean_object* v___y_18_, lean_object* v___y_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0(v_00_u03b1_16_, v___y_17_, v___y_18_);
lean_dec(v___y_18_);
lean_dec_ref(v___y_17_);
return v_res_20_;
}
}
uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(lean_object* v_opts_21_, lean_object* v_opt_22_){
_start:
{
lean_object* v_name_23_; lean_object* v_defValue_24_; lean_object* v_map_25_; lean_object* v___x_26_; 
v_name_23_ = lean_ctor_get(v_opt_22_, 0);
v_defValue_24_ = lean_ctor_get(v_opt_22_, 1);
v_map_25_ = lean_ctor_get(v_opts_21_, 0);
v___x_26_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_25_, v_name_23_);
if (lean_obj_tag(v___x_26_) == 0)
{
uint8_t v___x_27_; 
v___x_27_ = lean_unbox(v_defValue_24_);
return v___x_27_;
}
else
{
lean_object* v_val_28_; 
v_val_28_ = lean_ctor_get(v___x_26_, 0);
lean_inc(v_val_28_);
lean_dec_ref_known(v___x_26_, 1);
if (lean_obj_tag(v_val_28_) == 1)
{
uint8_t v_v_29_; 
v_v_29_ = lean_ctor_get_uint8(v_val_28_, 0);
lean_dec_ref_known(v_val_28_, 0);
return v_v_29_;
}
else
{
uint8_t v___x_30_; 
lean_dec(v_val_28_);
v___x_30_ = lean_unbox(v_defValue_24_);
return v___x_30_;
}
}
}
}
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_21_ = stack[0].m_obj;
lean_object* v_opt_22_ = stack[1].m_obj;
uint8_t v_res_31_;
v_res_31_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(v_opts_21_, v_opt_22_);
stack->m_num = v_res_31_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_32_, lean_object* v_opt_33_){
_start:
{
uint8_t v_res_34_; lean_object* v_r_35_; 
v_res_34_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(v_opts_32_, v_opt_33_);
lean_dec_ref(v_opt_33_);
lean_dec_ref(v_opts_32_);
v_r_35_ = lean_box(v_res_34_);
return v_r_35_;
}
}
uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(uint8_t v_suppressElabErrors_37_, uint8_t v___y_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_39_) == 1)
{
lean_object* v_pre_40_; 
v_pre_40_ = lean_ctor_get(v_x_39_, 0);
if (lean_obj_tag(v_pre_40_) == 0)
{
lean_object* v_str_41_; lean_object* v___x_42_; uint8_t v___x_43_; 
v_str_41_ = lean_ctor_get(v_x_39_, 1);
v___x_42_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___closed__0));
v___x_43_ = lean_string_dec_eq(v_str_41_, v___x_42_);
if (v___x_43_ == 0)
{
return v___x_43_;
}
else
{
return v_suppressElabErrors_37_;
}
}
else
{
return v___y_38_;
}
}
else
{
return v___y_38_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_37_ = stack[0].m_num;
uint8_t v___y_38_ = stack[1].m_num;
lean_object* v_x_39_ = stack[2].m_obj;
uint8_t v_res_44_;
v_res_44_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(v_suppressElabErrors_37_, v___y_38_, v_x_39_);
stack->m_num = v_res_44_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_45_, lean_object* v___y_46_, lean_object* v_x_47_){
_start:
{
uint8_t v_suppressElabErrors_boxed_48_; uint8_t v___y_6339__boxed_49_; uint8_t v_res_50_; lean_object* v_r_51_; 
v_suppressElabErrors_boxed_48_ = lean_unbox(v_suppressElabErrors_45_);
v___y_6339__boxed_49_ = lean_unbox(v___y_46_);
v_res_50_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_48_, v___y_6339__boxed_49_, v_x_47_);
lean_dec(v_x_47_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_52_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_55_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_56_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___x_57_);
lean_ctor_set(v___x_58_, 2, v___x_57_);
lean_ctor_set(v___x_58_, 3, v___x_57_);
lean_ctor_set(v___x_58_, 4, v___x_56_);
lean_ctor_set(v___x_58_, 5, v___x_56_);
lean_ctor_set(v___x_58_, 6, v___x_56_);
lean_ctor_set(v___x_58_, 7, v___x_56_);
lean_ctor_set(v___x_58_, 8, v___x_56_);
lean_ctor_set(v___x_58_, 9, v___x_56_);
lean_ctor_set(v___x_58_, 10, v___x_56_);
lean_ctor_set(v___x_58_, 11, v___x_55_);
return v___x_58_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_59_ = lean_unsigned_to_nat(32u);
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_61_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_61_, 0, v___x_60_);
return v___x_61_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_62_ = ((size_t)5ULL);
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_unsigned_to_nat(32u);
v___x_65_ = lean_mk_empty_array_with_capacity(v___x_64_);
v___x_66_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_67_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_63_);
lean_ctor_set(v___x_67_, 3, v___x_63_);
lean_ctor_set_usize(v___x_67_, 4, v___x_62_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_68_ = lean_box(1);
v___x_69_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_70_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___x_69_);
lean_ctor_set(v___x_71_, 2, v___x_68_);
return v___x_71_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v_env_76_; uint8_t v___x_77_; lean_object* v_env_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v_scopes_81_; lean_object* v___x_82_; lean_object* v_opts_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_75_ = lean_st_ref_get(v___y_73_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_env_76_);
lean_dec(v___x_75_);
v___x_77_ = 0;
v_env_78_ = l_Lean_Environment_setRecordingDeps(v_env_76_, v___x_77_);
v___x_79_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_80_ = lean_st_ref_get(v___y_73_);
v_scopes_81_ = lean_ctor_get(v___x_80_, 2);
lean_inc(v_scopes_81_);
lean_dec(v___x_80_);
v___x_82_ = l_List_head_x21___redArg(v___x_79_, v_scopes_81_);
lean_dec(v_scopes_81_);
v_opts_83_ = lean_ctor_get(v___x_82_, 1);
lean_inc_ref(v_opts_83_);
lean_dec(v___x_82_);
v___x_84_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_85_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5);
v___x_86_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_86_, 0, v_env_78_);
lean_ctor_set(v___x_86_, 1, v___x_84_);
lean_ctor_set(v___x_86_, 2, v___x_85_);
lean_ctor_set(v___x_86_, 3, v_opts_83_);
v___x_87_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_msgData_72_);
v___x_88_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_72_ = stack[0].m_obj;
lean_object* v___y_73_ = stack[1].m_obj;
lean_object* v_res_89_;
v_res_89_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v_msgData_72_, v___y_73_);
stack->m_obj
 = v_res_89_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v_msgData_90_, v___y_91_);
lean_dec(v___y_91_);
return v_res_93_;
}
}
lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(lean_object* v_ref_95_, lean_object* v_msgData_96_, uint8_t v_severity_97_, uint8_t v_isSilent_98_, lean_object* v___y_99_, lean_object* v___y_100_){
_start:
{
lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; uint8_t v___y_106_; lean_object* v___y_107_; uint8_t v___y_108_; lean_object* v___y_109_; lean_object* v___y_110_; uint8_t v___y_168_; lean_object* v___y_169_; uint8_t v___y_170_; uint8_t v___y_171_; lean_object* v___y_172_; uint8_t v___y_196_; lean_object* v___y_197_; uint8_t v___y_198_; uint8_t v___y_199_; lean_object* v___y_200_; uint8_t v___y_204_; uint8_t v___y_205_; uint8_t v___y_206_; uint8_t v___x_221_; uint8_t v___y_223_; uint8_t v___y_224_; uint8_t v___y_225_; uint8_t v___y_227_; uint8_t v___x_239_; 
v___x_221_ = 2;
v___x_239_ = l_Lean_instBEqMessageSeverity_beq(v_severity_97_, v___x_221_);
if (v___x_239_ == 0)
{
v___y_227_ = v___x_239_;
goto v___jp_226_;
}
else
{
uint8_t v___x_240_; 
lean_inc_ref(v_msgData_96_);
v___x_240_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_96_);
v___y_227_ = v___x_240_;
goto v___jp_226_;
}
v___jp_102_:
{
lean_object* v___x_111_; 
v___x_111_ = l_Lean_Elab_Command_getScope___redArg(v___y_110_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v_currNamespace_113_; lean_object* v___x_114_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v___x_111_, 1);
v_currNamespace_113_ = lean_ctor_get(v_a_112_, 2);
lean_inc(v_currNamespace_113_);
lean_dec(v_a_112_);
v___x_114_ = l_Lean_Elab_Command_getScope___redArg(v___y_110_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_150_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_150_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_150_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_150_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v_openDecls_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_env_124_; lean_object* v_messages_125_; lean_object* v_scopes_126_; lean_object* v_usedQuotCtxts_127_; lean_object* v_nextMacroScope_128_; lean_object* v_maxRecDepth_129_; lean_object* v_ngen_130_; lean_object* v_auxDeclNGen_131_; lean_object* v_infoState_132_; lean_object* v_traceState_133_; lean_object* v_snapshotTasks_134_; lean_object* v_prevLinterStates_135_; lean_object* v_codeQualityEntryTasks_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_149_; 
v_openDecls_119_ = lean_ctor_get(v_a_115_, 3);
lean_inc(v_openDecls_119_);
lean_dec(v_a_115_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v_currNamespace_113_);
lean_ctor_set(v___x_120_, 1, v_openDecls_119_);
v___x_121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v___y_105_);
lean_inc_ref(v___y_103_);
lean_inc_ref(v___y_109_);
v___x_122_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_122_, 0, v___y_109_);
lean_ctor_set(v___x_122_, 1, v___y_104_);
lean_ctor_set(v___x_122_, 2, v___y_107_);
lean_ctor_set(v___x_122_, 3, v___y_103_);
lean_ctor_set(v___x_122_, 4, v___x_121_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*5, v___y_106_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*5 + 1, v___y_108_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*5 + 2, v_isSilent_98_);
v___x_123_ = lean_st_ref_take(v___y_110_);
v_env_124_ = lean_ctor_get(v___x_123_, 0);
v_messages_125_ = lean_ctor_get(v___x_123_, 1);
v_scopes_126_ = lean_ctor_get(v___x_123_, 2);
v_usedQuotCtxts_127_ = lean_ctor_get(v___x_123_, 3);
v_nextMacroScope_128_ = lean_ctor_get(v___x_123_, 4);
v_maxRecDepth_129_ = lean_ctor_get(v___x_123_, 5);
v_ngen_130_ = lean_ctor_get(v___x_123_, 6);
v_auxDeclNGen_131_ = lean_ctor_get(v___x_123_, 7);
v_infoState_132_ = lean_ctor_get(v___x_123_, 8);
v_traceState_133_ = lean_ctor_get(v___x_123_, 9);
v_snapshotTasks_134_ = lean_ctor_get(v___x_123_, 10);
v_prevLinterStates_135_ = lean_ctor_get(v___x_123_, 11);
v_codeQualityEntryTasks_136_ = lean_ctor_get(v___x_123_, 12);
v_isSharedCheck_149_ = !lean_is_exclusive(v___x_123_);
if (v_isSharedCheck_149_ == 0)
{
v___x_138_ = v___x_123_;
v_isShared_139_ = v_isSharedCheck_149_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_codeQualityEntryTasks_136_);
lean_inc(v_prevLinterStates_135_);
lean_inc(v_snapshotTasks_134_);
lean_inc(v_traceState_133_);
lean_inc(v_infoState_132_);
lean_inc(v_auxDeclNGen_131_);
lean_inc(v_ngen_130_);
lean_inc(v_maxRecDepth_129_);
lean_inc(v_nextMacroScope_128_);
lean_inc(v_usedQuotCtxts_127_);
lean_inc(v_scopes_126_);
lean_inc(v_messages_125_);
lean_inc(v_env_124_);
lean_dec(v___x_123_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_149_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_box(0);
v___x_141_ = l_Lean_MessageLog_add(v___x_122_, v_messages_125_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_env_124_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_scopes_126_);
lean_ctor_set(v_reuseFailAlloc_148_, 3, v_usedQuotCtxts_127_);
lean_ctor_set(v_reuseFailAlloc_148_, 4, v_nextMacroScope_128_);
lean_ctor_set(v_reuseFailAlloc_148_, 5, v_maxRecDepth_129_);
lean_ctor_set(v_reuseFailAlloc_148_, 6, v_ngen_130_);
lean_ctor_set(v_reuseFailAlloc_148_, 7, v_auxDeclNGen_131_);
lean_ctor_set(v_reuseFailAlloc_148_, 8, v_infoState_132_);
lean_ctor_set(v_reuseFailAlloc_148_, 9, v_traceState_133_);
lean_ctor_set(v_reuseFailAlloc_148_, 10, v_snapshotTasks_134_);
lean_ctor_set(v_reuseFailAlloc_148_, 11, v_prevLinterStates_135_);
lean_ctor_set(v_reuseFailAlloc_148_, 12, v_codeQualityEntryTasks_136_);
v___x_143_ = v_reuseFailAlloc_148_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_st_ref_put(v___y_110_, v___x_143_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_140_);
v___x_146_ = v___x_117_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_140_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_dec(v_currNamespace_113_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_105_);
lean_dec_ref(v___y_104_);
v_a_151_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_114_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_114_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
lean_dec(v___y_107_);
lean_dec_ref(v___y_105_);
lean_dec_ref(v___y_104_);
v_a_159_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_111_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_111_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
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
v___jp_167_:
{
lean_object* v_fileName_173_; lean_object* v_fileMap_174_; uint8_t v_suppressElabErrors_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___f_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_194_; 
v_fileName_173_ = lean_ctor_get(v___y_99_, 0);
v_fileMap_174_ = lean_ctor_get(v___y_99_, 1);
v_suppressElabErrors_175_ = lean_ctor_get_uint8(v___y_99_, sizeof(void*)*10);
v___x_176_ = lean_box(v_suppressElabErrors_175_);
v___x_177_ = lean_box(v___y_168_);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_178_, 0, v___x_176_);
lean_closure_set(v___f_178_, 1, v___x_177_);
v___x_179_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_96_);
v___x_180_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v___x_179_, v___y_100_);
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_194_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_194_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_194_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
lean_inc_ref_n(v_fileMap_174_, 2);
v___x_185_ = l_Lean_FileMap_toPosition(v_fileMap_174_, v___y_169_);
lean_dec(v___y_169_);
v___x_186_ = l_Lean_FileMap_toPosition(v_fileMap_174_, v___y_172_);
lean_dec(v___y_172_);
v___x_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
v___x_188_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0));
if (v_suppressElabErrors_175_ == 0)
{
lean_del_object(v___x_183_);
lean_dec_ref(v___f_178_);
v___y_103_ = v___x_188_;
v___y_104_ = v___x_185_;
v___y_105_ = v_a_181_;
v___y_106_ = v___y_170_;
v___y_107_ = v___x_187_;
v___y_108_ = v___y_171_;
v___y_109_ = v_fileName_173_;
v___y_110_ = v___y_100_;
goto v___jp_102_;
}
else
{
uint8_t v___x_189_; 
lean_inc(v_a_181_);
v___x_189_ = l_Lean_MessageData_hasTag(v___f_178_, v_a_181_);
if (v___x_189_ == 0)
{
lean_object* v___x_190_; lean_object* v___x_192_; 
lean_dec_ref_known(v___x_187_, 1);
lean_dec_ref(v___x_185_);
lean_dec(v_a_181_);
v___x_190_ = lean_box(0);
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 0, v___x_190_);
v___x_192_ = v___x_183_;
goto v_reusejp_191_;
}
else
{
lean_object* v_reuseFailAlloc_193_; 
v_reuseFailAlloc_193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
v___x_192_ = v_reuseFailAlloc_193_;
goto v_reusejp_191_;
}
v_reusejp_191_:
{
return v___x_192_;
}
}
else
{
lean_del_object(v___x_183_);
v___y_103_ = v___x_188_;
v___y_104_ = v___x_185_;
v___y_105_ = v_a_181_;
v___y_106_ = v___y_170_;
v___y_107_ = v___x_187_;
v___y_108_ = v___y_171_;
v___y_109_ = v_fileName_173_;
v___y_110_ = v___y_100_;
goto v___jp_102_;
}
}
}
}
v___jp_195_:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_Syntax_getTailPos_x3f(v___y_197_, v___y_198_);
lean_dec(v___y_197_);
if (lean_obj_tag(v___x_201_) == 0)
{
lean_inc(v___y_200_);
v___y_168_ = v___y_196_;
v___y_169_ = v___y_200_;
v___y_170_ = v___y_198_;
v___y_171_ = v___y_199_;
v___y_172_ = v___y_200_;
goto v___jp_167_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v___x_201_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_201_, 1);
v___y_168_ = v___y_196_;
v___y_169_ = v___y_200_;
v___y_170_ = v___y_198_;
v___y_171_ = v___y_199_;
v___y_172_ = v_val_202_;
goto v___jp_167_;
}
}
v___jp_203_:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_Elab_Command_getRef___redArg(v___y_99_);
if (lean_obj_tag(v___x_207_) == 0)
{
lean_object* v_a_208_; lean_object* v_ref_209_; lean_object* v___x_210_; 
v_a_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_a_208_);
lean_dec_ref_known(v___x_207_, 1);
v_ref_209_ = l_Lean_replaceRef(v_ref_95_, v_a_208_);
lean_dec(v_a_208_);
v___x_210_ = l_Lean_Syntax_getPos_x3f(v_ref_209_, v___y_205_);
if (lean_obj_tag(v___x_210_) == 0)
{
lean_object* v___x_211_; 
v___x_211_ = lean_unsigned_to_nat(0u);
v___y_196_ = v___y_204_;
v___y_197_ = v_ref_209_;
v___y_198_ = v___y_205_;
v___y_199_ = v___y_206_;
v___y_200_ = v___x_211_;
goto v___jp_195_;
}
else
{
lean_object* v_val_212_; 
v_val_212_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_val_212_);
lean_dec_ref_known(v___x_210_, 1);
v___y_196_ = v___y_204_;
v___y_197_ = v_ref_209_;
v___y_198_ = v___y_205_;
v___y_199_ = v___y_206_;
v___y_200_ = v_val_212_;
goto v___jp_195_;
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec_ref(v_msgData_96_);
v_a_213_ = lean_ctor_get(v___x_207_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_207_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_207_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_207_);
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
v___jp_222_:
{
if (v___y_225_ == 0)
{
v___y_204_ = v___y_223_;
v___y_205_ = v___y_224_;
v___y_206_ = v_severity_97_;
goto v___jp_203_;
}
else
{
v___y_204_ = v___y_223_;
v___y_205_ = v___y_224_;
v___y_206_ = v___x_221_;
goto v___jp_203_;
}
}
v___jp_226_:
{
if (v___y_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v_scopes_230_; lean_object* v___x_231_; lean_object* v_opts_232_; uint8_t v___x_233_; uint8_t v___x_234_; 
v___x_228_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_229_ = lean_st_ref_get(v___y_100_);
v_scopes_230_ = lean_ctor_get(v___x_229_, 2);
lean_inc(v_scopes_230_);
lean_dec(v___x_229_);
v___x_231_ = l_List_head_x21___redArg(v___x_228_, v_scopes_230_);
lean_dec(v_scopes_230_);
v_opts_232_ = lean_ctor_get(v___x_231_, 1);
lean_inc_ref(v_opts_232_);
lean_dec(v___x_231_);
v___x_233_ = 1;
v___x_234_ = l_Lean_instBEqMessageSeverity_beq(v_severity_97_, v___x_233_);
if (v___x_234_ == 0)
{
lean_dec_ref(v_opts_232_);
v___y_223_ = v___y_227_;
v___y_224_ = v___y_227_;
v___y_225_ = v___x_234_;
goto v___jp_222_;
}
else
{
lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_235_ = l_Lean_warningAsError;
v___x_236_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(v_opts_232_, v___x_235_);
lean_dec_ref(v_opts_232_);
v___y_223_ = v___y_227_;
v___y_224_ = v___y_227_;
v___y_225_ = v___x_236_;
goto v___jp_222_;
}
}
else
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec_ref(v_msgData_96_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_95_ = stack[0].m_obj;
lean_object* v_msgData_96_ = stack[1].m_obj;
uint8_t v_severity_97_ = stack[2].m_num;
uint8_t v_isSilent_98_ = stack[3].m_num;
lean_object* v___y_99_ = stack[4].m_obj;
lean_object* v___y_100_ = stack[5].m_obj;
lean_object* v_res_241_;
v_res_241_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_ref_95_, v_msgData_96_, v_severity_97_, v_isSilent_98_, v___y_99_, v___y_100_);
stack->m_obj
 = v_res_241_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___boxed(lean_object* v_ref_242_, lean_object* v_msgData_243_, lean_object* v_severity_244_, lean_object* v_isSilent_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
uint8_t v_severity_boxed_249_; uint8_t v_isSilent_boxed_250_; lean_object* v_res_251_; 
v_severity_boxed_249_ = lean_unbox(v_severity_244_);
v_isSilent_boxed_250_ = lean_unbox(v_isSilent_245_);
v_res_251_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_ref_242_, v_msgData_243_, v_severity_boxed_249_, v_isSilent_boxed_250_, v___y_246_, v___y_247_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v_ref_242_);
return v_res_251_;
}
}
lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(lean_object* v_ref_252_, lean_object* v_msgData_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
uint8_t v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; 
v___x_257_ = 0;
v___x_258_ = 0;
v___x_259_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_ref_252_, v_msgData_253_, v___x_257_, v___x_258_, v___y_254_, v___y_255_);
return v___x_259_;
}
}
LEAN_EXPORT void l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_252_ = stack[0].m_obj;
lean_object* v_msgData_253_ = stack[1].m_obj;
lean_object* v___y_254_ = stack[2].m_obj;
lean_object* v___y_255_ = stack[3].m_obj;
lean_object* v_res_260_;
v_res_260_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_ref_252_, v_msgData_253_, v___y_254_, v___y_255_);
stack->m_obj
 = v_res_260_;
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1___boxed(lean_object* v_ref_261_, lean_object* v_msgData_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_ref_261_, v_msgData_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v_ref_261_);
return v_res_266_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(lean_object* v_tk_270_, lean_object* v_as_271_, size_t v_sz_272_, size_t v_i_273_, lean_object* v_b_274_, lean_object* v___y_275_, lean_object* v___y_276_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = lean_usize_dec_lt(v_i_273_, v_sz_272_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
v___x_279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_279_, 0, v_b_274_);
return v___x_279_;
}
else
{
lean_object* v___x_280_; lean_object* v_a_281_; lean_object* v___x_282_; 
lean_dec_ref(v_b_274_);
v___x_280_ = lean_box(0);
v_a_281_ = lean_array_uget_borrowed(v_as_271_, v_i_273_);
lean_inc(v_a_281_);
v___x_282_ = l_Lean_Elab_InfoTree_format(v_a_281_, v___x_280_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v_a_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v___x_282_, 1);
v___x_284_ = l_Lean_MessageData_ofFormat(v_a_283_);
v___x_285_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_270_, v___x_284_, v___y_275_, v___y_276_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v___x_286_; size_t v___x_287_; size_t v___x_288_; 
lean_dec_ref_known(v___x_285_, 1);
v___x_286_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0));
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_add(v_i_273_, v___x_287_);
v_i_273_ = v___x_288_;
v_b_274_ = v___x_286_;
goto _start;
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
v_a_290_ = lean_ctor_get(v___x_285_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_285_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_285_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_285_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_310_; 
v_a_298_ = lean_ctor_get(v___x_282_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_282_);
if (v_isSharedCheck_310_ == 0)
{
v___x_300_ = v___x_282_;
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_282_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_310_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_ref_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
v_ref_302_ = lean_ctor_get(v___y_275_, 7);
v___x_303_ = lean_io_error_to_string(v_a_298_);
v___x_304_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
v___x_305_ = l_Lean_MessageData_ofFormat(v___x_304_);
lean_inc(v_ref_302_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v_ref_302_);
lean_ctor_set(v___x_306_, 1, v___x_305_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 0, v___x_306_);
v___x_308_ = v___x_300_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v___x_306_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_270_ = stack[0].m_obj;
lean_object* v_as_271_ = stack[1].m_obj;
size_t v_sz_272_ = stack[2].m_num;
size_t v_i_273_ = stack[3].m_num;
lean_object* v_b_274_ = stack[4].m_obj;
lean_object* v___y_275_ = stack[5].m_obj;
lean_object* v___y_276_ = stack[6].m_obj;
lean_object* v_res_311_;
v_res_311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(v_tk_270_, v_as_271_, v_sz_272_, v_i_273_, v_b_274_, v___y_275_, v___y_276_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___boxed(lean_object* v_tk_312_, lean_object* v_as_313_, lean_object* v_sz_314_, lean_object* v_i_315_, lean_object* v_b_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_){
_start:
{
size_t v_sz_boxed_320_; size_t v_i_boxed_321_; lean_object* v_res_322_; 
v_sz_boxed_320_ = lean_unbox_usize(v_sz_314_);
lean_dec(v_sz_314_);
v_i_boxed_321_ = lean_unbox_usize(v_i_315_);
lean_dec(v_i_315_);
v_res_322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(v_tk_312_, v_as_313_, v_sz_boxed_320_, v_i_boxed_321_, v_b_316_, v___y_317_, v___y_318_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec_ref(v_as_313_);
lean_dec(v_tk_312_);
return v_res_322_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(lean_object* v_tk_323_, lean_object* v_as_324_, size_t v_sz_325_, size_t v_i_326_, lean_object* v_b_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
uint8_t v___x_331_; 
v___x_331_ = lean_usize_dec_lt(v_i_326_, v_sz_325_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; 
v___x_332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_332_, 0, v_b_327_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v_a_334_; lean_object* v___x_335_; 
lean_dec_ref(v_b_327_);
v___x_333_ = lean_box(0);
v_a_334_ = lean_array_uget_borrowed(v_as_324_, v_i_326_);
lean_inc(v_a_334_);
v___x_335_ = l_Lean_Elab_InfoTree_format(v_a_334_, v___x_333_);
if (lean_obj_tag(v___x_335_) == 0)
{
lean_object* v_a_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_a_336_ = lean_ctor_get(v___x_335_, 0);
lean_inc(v_a_336_);
lean_dec_ref_known(v___x_335_, 1);
v___x_337_ = l_Lean_MessageData_ofFormat(v_a_336_);
v___x_338_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_323_, v___x_337_, v___y_328_, v___y_329_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v___x_339_; size_t v___x_340_; size_t v___x_341_; lean_object* v___x_342_; 
lean_dec_ref_known(v___x_338_, 1);
v___x_339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0));
v___x_340_ = ((size_t)1ULL);
v___x_341_ = lean_usize_add(v_i_326_, v___x_340_);
v___x_342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(v_tk_323_, v_as_324_, v_sz_325_, v___x_341_, v___x_339_, v___y_328_, v___y_329_);
return v___x_342_;
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
v_a_343_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_338_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_338_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_363_; 
v_a_351_ = lean_ctor_get(v___x_335_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_363_ == 0)
{
v___x_353_ = v___x_335_;
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_335_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v_ref_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v_ref_355_ = lean_ctor_get(v___y_328_, 7);
v___x_356_ = lean_io_error_to_string(v_a_351_);
v___x_357_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_357_, 0, v___x_356_);
v___x_358_ = l_Lean_MessageData_ofFormat(v___x_357_);
lean_inc(v_ref_355_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v_ref_355_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v___x_359_);
v___x_361_ = v___x_353_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_323_ = stack[0].m_obj;
lean_object* v_as_324_ = stack[1].m_obj;
size_t v_sz_325_ = stack[2].m_num;
size_t v_i_326_ = stack[3].m_num;
lean_object* v_b_327_ = stack[4].m_obj;
lean_object* v___y_328_ = stack[5].m_obj;
lean_object* v___y_329_ = stack[6].m_obj;
lean_object* v_res_364_;
v_res_364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(v_tk_323_, v_as_324_, v_sz_325_, v_i_326_, v_b_327_, v___y_328_, v___y_329_);
stack->m_obj
 = v_res_364_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4___boxed(lean_object* v_tk_365_, lean_object* v_as_366_, lean_object* v_sz_367_, lean_object* v_i_368_, lean_object* v_b_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
size_t v_sz_boxed_373_; size_t v_i_boxed_374_; lean_object* v_res_375_; 
v_sz_boxed_373_ = lean_unbox_usize(v_sz_367_);
lean_dec(v_sz_367_);
v_i_boxed_374_ = lean_unbox_usize(v_i_368_);
lean_dec(v_i_368_);
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(v_tk_365_, v_as_366_, v_sz_boxed_373_, v_i_boxed_374_, v_b_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec_ref(v_as_366_);
lean_dec(v_tk_365_);
return v_res_375_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(lean_object* v_tk_379_, lean_object* v_as_380_, size_t v_sz_381_, size_t v_i_382_, lean_object* v_b_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = lean_usize_dec_lt(v_i_382_, v_sz_381_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_388_, 0, v_b_383_);
return v___x_388_;
}
else
{
lean_object* v___x_389_; lean_object* v_a_390_; lean_object* v___x_391_; 
lean_dec_ref(v_b_383_);
v___x_389_ = lean_box(0);
v_a_390_ = lean_array_uget_borrowed(v_as_380_, v_i_382_);
lean_inc(v_a_390_);
v___x_391_ = l_Lean_Elab_InfoTree_format(v_a_390_, v___x_389_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
v___x_393_ = l_Lean_MessageData_ofFormat(v_a_392_);
v___x_394_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_379_, v___x_393_, v___y_384_, v___y_385_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v___x_395_; size_t v___x_396_; size_t v___x_397_; 
lean_dec_ref_known(v___x_394_, 1);
v___x_395_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0));
v___x_396_ = ((size_t)1ULL);
v___x_397_ = lean_usize_add(v_i_382_, v___x_396_);
v_i_382_ = v___x_397_;
v_b_383_ = v___x_395_;
goto _start;
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
v_a_399_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_394_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_394_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
else
{
lean_object* v_a_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_419_; 
v_a_407_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_419_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_419_ == 0)
{
v___x_409_ = v___x_391_;
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_a_407_);
lean_dec(v___x_391_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_419_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v_ref_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v_ref_411_ = lean_ctor_get(v___y_384_, 7);
v___x_412_ = lean_io_error_to_string(v_a_407_);
v___x_413_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
v___x_414_ = l_Lean_MessageData_ofFormat(v___x_413_);
lean_inc(v_ref_411_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v_ref_411_);
lean_ctor_set(v___x_415_, 1, v___x_414_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 0, v___x_415_);
v___x_417_ = v___x_409_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_379_ = stack[0].m_obj;
lean_object* v_as_380_ = stack[1].m_obj;
size_t v_sz_381_ = stack[2].m_num;
size_t v_i_382_ = stack[3].m_num;
lean_object* v_b_383_ = stack[4].m_obj;
lean_object* v___y_384_ = stack[5].m_obj;
lean_object* v___y_385_ = stack[6].m_obj;
lean_object* v_res_420_;
v_res_420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(v_tk_379_, v_as_380_, v_sz_381_, v_i_382_, v_b_383_, v___y_384_, v___y_385_);
stack->m_obj
 = v_res_420_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___boxed(lean_object* v_tk_421_, lean_object* v_as_422_, lean_object* v_sz_423_, lean_object* v_i_424_, lean_object* v_b_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
size_t v_sz_boxed_429_; size_t v_i_boxed_430_; lean_object* v_res_431_; 
v_sz_boxed_429_ = lean_unbox_usize(v_sz_423_);
lean_dec(v_sz_423_);
v_i_boxed_430_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_res_431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(v_tk_421_, v_as_422_, v_sz_boxed_429_, v_i_boxed_430_, v_b_425_, v___y_426_, v___y_427_);
lean_dec(v___y_427_);
lean_dec_ref(v___y_426_);
lean_dec_ref(v_as_422_);
lean_dec(v_tk_421_);
return v_res_431_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(lean_object* v_tk_432_, lean_object* v_as_433_, size_t v_sz_434_, size_t v_i_435_, lean_object* v_b_436_, lean_object* v___y_437_, lean_object* v___y_438_){
_start:
{
uint8_t v___x_440_; 
v___x_440_ = lean_usize_dec_lt(v_i_435_, v_sz_434_);
if (v___x_440_ == 0)
{
lean_object* v___x_441_; 
v___x_441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_441_, 0, v_b_436_);
return v___x_441_;
}
else
{
lean_object* v___x_442_; lean_object* v_a_443_; lean_object* v___x_444_; 
lean_dec_ref(v_b_436_);
v___x_442_ = lean_box(0);
v_a_443_ = lean_array_uget_borrowed(v_as_433_, v_i_435_);
lean_inc(v_a_443_);
v___x_444_ = l_Lean_Elab_InfoTree_format(v_a_443_, v___x_442_);
if (lean_obj_tag(v___x_444_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v_a_445_ = lean_ctor_get(v___x_444_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v___x_444_, 1);
v___x_446_ = l_Lean_MessageData_ofFormat(v_a_445_);
v___x_447_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_432_, v___x_446_, v___y_437_, v___y_438_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
lean_dec_ref_known(v___x_447_, 1);
v___x_448_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0));
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_435_, v___x_449_);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(v_tk_432_, v_as_433_, v_sz_434_, v___x_450_, v___x_448_, v___y_437_, v___y_438_);
return v___x_451_;
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_447_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_447_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_457_; 
if (v_isShared_455_ == 0)
{
v___x_457_ = v___x_454_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_a_452_);
v___x_457_ = v_reuseFailAlloc_458_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
return v___x_457_;
}
}
}
}
else
{
lean_object* v_a_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_472_; 
v_a_460_ = lean_ctor_get(v___x_444_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v___x_444_);
if (v_isSharedCheck_472_ == 0)
{
v___x_462_ = v___x_444_;
v_isShared_463_ = v_isSharedCheck_472_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_a_460_);
lean_dec(v___x_444_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_472_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v_ref_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_470_; 
v_ref_464_ = lean_ctor_get(v___y_437_, 7);
v___x_465_ = lean_io_error_to_string(v_a_460_);
v___x_466_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_466_, 0, v___x_465_);
v___x_467_ = l_Lean_MessageData_ofFormat(v___x_466_);
lean_inc(v_ref_464_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v_ref_464_);
lean_ctor_set(v___x_468_, 1, v___x_467_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 0, v___x_468_);
v___x_470_ = v___x_462_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_432_ = stack[0].m_obj;
lean_object* v_as_433_ = stack[1].m_obj;
size_t v_sz_434_ = stack[2].m_num;
size_t v_i_435_ = stack[3].m_num;
lean_object* v_b_436_ = stack[4].m_obj;
lean_object* v___y_437_ = stack[5].m_obj;
lean_object* v___y_438_ = stack[6].m_obj;
lean_object* v_res_473_;
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(v_tk_432_, v_as_433_, v_sz_434_, v_i_435_, v_b_436_, v___y_437_, v___y_438_);
stack->m_obj
 = v_res_473_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7___boxed(lean_object* v_tk_474_, lean_object* v_as_475_, lean_object* v_sz_476_, lean_object* v_i_477_, lean_object* v_b_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
size_t v_sz_boxed_482_; size_t v_i_boxed_483_; lean_object* v_res_484_; 
v_sz_boxed_482_ = lean_unbox_usize(v_sz_476_);
lean_dec(v_sz_476_);
v_i_boxed_483_ = lean_unbox_usize(v_i_477_);
lean_dec(v_i_477_);
v_res_484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(v_tk_474_, v_as_475_, v_sz_boxed_482_, v_i_boxed_483_, v_b_478_, v___y_479_, v___y_480_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec_ref(v_as_475_);
lean_dec(v_tk_474_);
return v_res_484_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(lean_object* v_init_485_, lean_object* v_tk_486_, lean_object* v_n_487_, lean_object* v_b_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
if (lean_obj_tag(v_n_487_) == 0)
{
lean_object* v_cs_492_; lean_object* v___x_493_; lean_object* v___x_494_; size_t v_sz_495_; size_t v___x_496_; lean_object* v___x_497_; 
v_cs_492_ = lean_ctor_get(v_n_487_, 0);
v___x_493_ = lean_box(0);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v_b_488_);
v_sz_495_ = lean_array_size(v_cs_492_);
v___x_496_ = ((size_t)0ULL);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(v_init_485_, v_tk_486_, v_cs_492_, v_sz_495_, v___x_496_, v___x_494_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_512_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_512_ == 0)
{
v___x_500_ = v___x_497_;
v_isShared_501_ = v_isSharedCheck_512_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_512_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v_fst_502_; 
v_fst_502_ = lean_ctor_get(v_a_498_, 0);
if (lean_obj_tag(v_fst_502_) == 0)
{
lean_object* v_snd_503_; lean_object* v___x_504_; lean_object* v___x_506_; 
v_snd_503_ = lean_ctor_get(v_a_498_, 1);
lean_inc(v_snd_503_);
lean_dec(v_a_498_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v_snd_503_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v___x_504_);
v___x_506_ = v___x_500_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
else
{
lean_object* v_val_508_; lean_object* v___x_510_; 
lean_inc_ref(v_fst_502_);
lean_dec(v_a_498_);
v_val_508_ = lean_ctor_get(v_fst_502_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v_fst_502_, 1);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v_val_508_);
v___x_510_ = v___x_500_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_val_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
else
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
v_a_513_ = lean_ctor_get(v___x_497_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_497_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_497_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_497_);
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
else
{
lean_object* v_vs_521_; lean_object* v___x_522_; lean_object* v___x_523_; size_t v_sz_524_; size_t v___x_525_; lean_object* v___x_526_; 
v_vs_521_ = lean_ctor_get(v_n_487_, 0);
v___x_522_ = lean_box(0);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_b_488_);
v_sz_524_ = lean_array_size(v_vs_521_);
v___x_525_ = ((size_t)0ULL);
v___x_526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(v_tk_486_, v_vs_521_, v_sz_524_, v___x_525_, v___x_523_, v___y_489_, v___y_490_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_541_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_541_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_541_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_541_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_a_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_541_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_fst_531_; 
v_fst_531_ = lean_ctor_get(v_a_527_, 0);
if (lean_obj_tag(v_fst_531_) == 0)
{
lean_object* v_snd_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v_snd_532_ = lean_ctor_get(v_a_527_, 1);
lean_inc(v_snd_532_);
lean_dec(v_a_527_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v_snd_532_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v___x_533_);
v___x_535_ = v___x_529_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v___x_533_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
else
{
lean_object* v_val_537_; lean_object* v___x_539_; 
lean_inc_ref(v_fst_531_);
lean_dec(v_a_527_);
v_val_537_ = lean_ctor_get(v_fst_531_, 0);
lean_inc(v_val_537_);
lean_dec_ref_known(v_fst_531_, 1);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_val_537_);
v___x_539_ = v___x_529_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v_val_537_);
v___x_539_ = v_reuseFailAlloc_540_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
return v___x_539_;
}
}
}
}
else
{
lean_object* v_a_542_; lean_object* v___x_544_; uint8_t v_isShared_545_; uint8_t v_isSharedCheck_549_; 
v_a_542_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_549_ == 0)
{
v___x_544_ = v___x_526_;
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
else
{
lean_inc(v_a_542_);
lean_dec(v___x_526_);
v___x_544_ = lean_box(0);
v_isShared_545_ = v_isSharedCheck_549_;
goto v_resetjp_543_;
}
v_resetjp_543_:
{
lean_object* v___x_547_; 
if (v_isShared_545_ == 0)
{
v___x_547_ = v___x_544_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
v___x_547_ = v_reuseFailAlloc_548_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
return v___x_547_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_485_ = stack[0].m_obj;
lean_object* v_tk_486_ = stack[1].m_obj;
lean_object* v_n_487_ = stack[2].m_obj;
lean_object* v_b_488_ = stack[3].m_obj;
lean_object* v___y_489_ = stack[4].m_obj;
lean_object* v___y_490_ = stack[5].m_obj;
lean_object* v_res_550_;
v_res_550_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_485_, v_tk_486_, v_n_487_, v_b_488_, v___y_489_, v___y_490_);
stack->m_obj
 = v_res_550_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(lean_object* v_init_551_, lean_object* v_tk_552_, lean_object* v_as_553_, size_t v_sz_554_, size_t v_i_555_, lean_object* v_b_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
uint8_t v___x_560_; 
v___x_560_ = lean_usize_dec_lt(v_i_555_, v_sz_554_);
if (v___x_560_ == 0)
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_561_, 0, v_b_556_);
return v___x_561_;
}
else
{
lean_object* v_snd_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_596_; 
v_snd_562_ = lean_ctor_get(v_b_556_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_b_556_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_b_556_, 0);
lean_dec(v_unused_597_);
v___x_564_ = v_b_556_;
v_isShared_565_ = v_isSharedCheck_596_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_snd_562_);
lean_dec(v_b_556_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_596_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v_a_567_; lean_object* v___x_568_; 
v___x_566_ = lean_box(0);
v_a_567_ = lean_array_uget_borrowed(v_as_553_, v_i_555_);
lean_inc(v_snd_562_);
v___x_568_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_551_, v_tk_552_, v_a_567_, v_snd_562_, v___y_557_, v___y_558_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_587_; 
v_a_569_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_587_ == 0)
{
v___x_571_ = v___x_568_;
v_isShared_572_ = v_isSharedCheck_587_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_568_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_587_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
if (lean_obj_tag(v_a_569_) == 0)
{
lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v_a_569_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_573_);
v___x_575_ = v___x_564_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_573_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_snd_562_);
v___x_575_ = v_reuseFailAlloc_579_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_577_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_575_);
v___x_577_ = v___x_571_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; 
lean_del_object(v___x_571_);
lean_dec(v_snd_562_);
v_a_580_ = lean_ctor_get(v_a_569_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v_a_569_, 1);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v_a_580_);
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_582_ = v___x_564_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_a_580_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
size_t v___x_583_; size_t v___x_584_; 
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_555_, v___x_583_);
v_i_555_ = v___x_584_;
v_b_556_ = v___x_582_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_595_; 
lean_del_object(v___x_564_);
lean_dec(v_snd_562_);
v_a_588_ = lean_ctor_get(v___x_568_, 0);
v_isSharedCheck_595_ = !lean_is_exclusive(v___x_568_);
if (v_isSharedCheck_595_ == 0)
{
v___x_590_ = v___x_568_;
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_a_588_);
lean_dec(v___x_568_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_595_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_593_; 
if (v_isShared_591_ == 0)
{
v___x_593_ = v___x_590_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_a_588_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_551_ = stack[0].m_obj;
lean_object* v_tk_552_ = stack[1].m_obj;
lean_object* v_as_553_ = stack[2].m_obj;
size_t v_sz_554_ = stack[3].m_num;
size_t v_i_555_ = stack[4].m_num;
lean_object* v_b_556_ = stack[5].m_obj;
lean_object* v___y_557_ = stack[6].m_obj;
lean_object* v___y_558_ = stack[7].m_obj;
lean_object* v_res_598_;
v_res_598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(v_init_551_, v_tk_552_, v_as_553_, v_sz_554_, v_i_555_, v_b_556_, v___y_557_, v___y_558_);
stack->m_obj
 = v_res_598_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6___boxed(lean_object* v_init_599_, lean_object* v_tk_600_, lean_object* v_as_601_, lean_object* v_sz_602_, lean_object* v_i_603_, lean_object* v_b_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
size_t v_sz_boxed_608_; size_t v_i_boxed_609_; lean_object* v_res_610_; 
v_sz_boxed_608_ = lean_unbox_usize(v_sz_602_);
lean_dec(v_sz_602_);
v_i_boxed_609_ = lean_unbox_usize(v_i_603_);
lean_dec(v_i_603_);
v_res_610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(v_init_599_, v_tk_600_, v_as_601_, v_sz_boxed_608_, v_i_boxed_609_, v_b_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
lean_dec_ref(v_as_601_);
lean_dec(v_tk_600_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___boxed(lean_object* v_init_611_, lean_object* v_tk_612_, lean_object* v_n_613_, lean_object* v_b_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_611_, v_tk_612_, v_n_613_, v_b_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec_ref(v_n_613_);
lean_dec(v_tk_612_);
return v_res_618_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(lean_object* v_tk_619_, lean_object* v_t_620_, lean_object* v_init_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_root_625_; lean_object* v_tail_626_; lean_object* v___x_627_; 
v_root_625_ = lean_ctor_get(v_t_620_, 0);
v_tail_626_ = lean_ctor_get(v_t_620_, 1);
v___x_627_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_621_, v_tk_619_, v_root_625_, v_init_621_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_a_628_; lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_664_; 
v_a_628_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_664_ == 0)
{
v___x_630_ = v___x_627_;
v_isShared_631_ = v_isSharedCheck_664_;
goto v_resetjp_629_;
}
else
{
lean_inc(v_a_628_);
lean_dec(v___x_627_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_664_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
if (lean_obj_tag(v_a_628_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; 
v_a_632_ = lean_ctor_get(v_a_628_, 0);
lean_inc(v_a_632_);
lean_dec_ref_known(v_a_628_, 1);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v_a_632_);
v___x_634_ = v___x_630_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v_a_632_);
v___x_634_ = v_reuseFailAlloc_635_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
return v___x_634_;
}
}
else
{
lean_object* v_a_636_; lean_object* v___x_637_; lean_object* v___x_638_; size_t v_sz_639_; size_t v___x_640_; lean_object* v___x_641_; 
lean_del_object(v___x_630_);
v_a_636_ = lean_ctor_get(v_a_628_, 0);
lean_inc(v_a_636_);
lean_dec_ref_known(v_a_628_, 1);
v___x_637_ = lean_box(0);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v_a_636_);
v_sz_639_ = lean_array_size(v_tail_626_);
v___x_640_ = ((size_t)0ULL);
v___x_641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(v_tk_619_, v_tail_626_, v_sz_639_, v___x_640_, v___x_638_, v___y_622_, v___y_623_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_655_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_655_ == 0)
{
v___x_644_ = v___x_641_;
v_isShared_645_ = v_isSharedCheck_655_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_641_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_655_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v_fst_646_; 
v_fst_646_ = lean_ctor_get(v_a_642_, 0);
if (lean_obj_tag(v_fst_646_) == 0)
{
lean_object* v_snd_647_; lean_object* v___x_649_; 
v_snd_647_ = lean_ctor_get(v_a_642_, 1);
lean_inc(v_snd_647_);
lean_dec(v_a_642_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_snd_647_);
v___x_649_ = v___x_644_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_snd_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
else
{
lean_object* v_val_651_; lean_object* v___x_653_; 
lean_inc_ref(v_fst_646_);
lean_dec(v_a_642_);
v_val_651_ = lean_ctor_get(v_fst_646_, 0);
lean_inc(v_val_651_);
lean_dec_ref_known(v_fst_646_, 1);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v_val_651_);
v___x_653_ = v___x_644_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_val_651_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_641_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_641_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_641_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_641_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
}
else
{
lean_object* v_a_665_; lean_object* v___x_667_; uint8_t v_isShared_668_; uint8_t v_isSharedCheck_672_; 
v_a_665_ = lean_ctor_get(v___x_627_, 0);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_627_);
if (v_isSharedCheck_672_ == 0)
{
v___x_667_ = v___x_627_;
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
else
{
lean_inc(v_a_665_);
lean_dec(v___x_627_);
v___x_667_ = lean_box(0);
v_isShared_668_ = v_isSharedCheck_672_;
goto v_resetjp_666_;
}
v_resetjp_666_:
{
lean_object* v___x_670_; 
if (v_isShared_668_ == 0)
{
v___x_670_ = v___x_667_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_a_665_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_tk_619_ = stack[0].m_obj;
lean_object* v_t_620_ = stack[1].m_obj;
lean_object* v_init_621_ = stack[2].m_obj;
lean_object* v___y_622_ = stack[3].m_obj;
lean_object* v___y_623_ = stack[4].m_obj;
lean_object* v_res_673_;
v_res_673_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_619_, v_t_620_, v_init_621_, v___y_622_, v___y_623_);
stack->m_obj
 = v_res_673_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2___boxed(lean_object* v_tk_674_, lean_object* v_t_675_, lean_object* v_init_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_674_, v_t_675_, v_init_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec_ref(v_t_675_);
lean_dec(v_tk_674_);
return v_res_680_;
}
}
lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(lean_object* v_msgData_681_, uint8_t v_severity_682_, uint8_t v_isSilent_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_Elab_Command_getRef___redArg(v___y_684_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v___x_689_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v___x_689_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_a_688_, v_msgData_681_, v_severity_682_, v_isSilent_683_, v___y_684_, v___y_685_);
lean_dec(v_a_688_);
return v___x_689_;
}
else
{
lean_object* v_a_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_697_; 
lean_dec_ref(v_msgData_681_);
v_a_690_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_697_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_697_ == 0)
{
v___x_692_ = v___x_687_;
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_a_690_);
lean_dec(v___x_687_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_697_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_695_; 
if (v_isShared_693_ == 0)
{
v___x_695_ = v___x_692_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_a_690_);
v___x_695_ = v_reuseFailAlloc_696_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
return v___x_695_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_681_ = stack[0].m_obj;
uint8_t v_severity_682_ = stack[1].m_num;
uint8_t v_isSilent_683_ = stack[2].m_num;
lean_object* v___y_684_ = stack[3].m_obj;
lean_object* v___y_685_ = stack[4].m_obj;
lean_object* v_res_698_;
v_res_698_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_msgData_681_, v_severity_682_, v_isSilent_683_, v___y_684_, v___y_685_);
stack->m_obj
 = v_res_698_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6___boxed(lean_object* v_msgData_699_, lean_object* v_severity_700_, lean_object* v_isSilent_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_){
_start:
{
uint8_t v_severity_boxed_705_; uint8_t v_isSilent_boxed_706_; lean_object* v_res_707_; 
v_severity_boxed_705_ = lean_unbox(v_severity_700_);
v_isSilent_boxed_706_ = lean_unbox(v_isSilent_701_);
v_res_707_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_msgData_699_, v_severity_boxed_705_, v_isSilent_boxed_706_, v___y_702_, v___y_703_);
lean_dec(v___y_703_);
lean_dec_ref(v___y_702_);
return v_res_707_;
}
}
lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object* v_msgData_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
uint8_t v___x_712_; uint8_t v___x_713_; lean_object* v___x_714_; 
v___x_712_ = 2;
v___x_713_ = 0;
v___x_714_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_msgData_708_, v___x_712_, v___x_713_, v___y_709_, v___y_710_);
return v___x_714_;
}
}
LEAN_EXPORT void l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_708_ = stack[0].m_obj;
lean_object* v___y_709_ = stack[1].m_obj;
lean_object* v___y_710_ = stack[2].m_obj;
lean_object* v_res_715_;
v_res_715_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v_msgData_708_, v___y_709_, v___y_710_);
stack->m_obj
 = v_res_715_;
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3___boxed(lean_object* v_msgData_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v_msgData_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
return v_res_720_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5(void){
_start:
{
lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_729_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4));
v___x_730_ = l_Lean_MessageData_ofFormat(v___x_729_);
return v___x_730_;
}
}
lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(lean_object* v_x_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_735_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
lean_inc(v_x_731_);
v___x_736_ = l_Lean_Syntax_isOfKind(v_x_731_, v___x_735_);
if (v___x_736_ == 0)
{
lean_object* v___x_737_; 
lean_dec(v_x_731_);
v___x_737_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
return v___x_737_;
}
else
{
lean_object* v___x_738_; lean_object* v_tk_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v_infoState_760_; uint8_t v_enabled_761_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v_tk_739_ = l_Lean_Syntax_getArg(v_x_731_, v___x_738_);
v___x_740_ = lean_unsigned_to_nat(2u);
v___x_741_ = l_Lean_Syntax_getArg(v_x_731_, v___x_740_);
lean_dec(v_x_731_);
v___x_742_ = lean_st_ref_get(v_a_733_);
v_infoState_760_ = lean_ctor_get(v___x_742_, 8);
lean_inc_ref(v_infoState_760_);
lean_dec(v___x_742_);
v_enabled_761_ = lean_ctor_get_uint8(v_infoState_760_, sizeof(void*)*3);
lean_dec_ref(v_infoState_760_);
if (v_enabled_761_ == 0)
{
if (v___x_736_ == 0)
{
goto v___jp_743_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; 
lean_dec(v___x_741_);
lean_dec(v_tk_739_);
v___x_762_ = lean_obj_once(&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5, &l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5_once, _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5);
v___x_763_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_762_, v_a_732_, v_a_733_);
return v___x_763_;
}
}
else
{
goto v___jp_743_;
}
v___jp_743_:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Elab_Command_elabCommand(v___x_741_, v_a_732_, v_a_733_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_745_; lean_object* v_infoState_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v_trees_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec_ref_known(v___x_744_, 1);
v___x_745_ = lean_st_ref_get(v_a_733_);
v_infoState_746_ = lean_ctor_get(v___x_745_, 8);
lean_inc_ref(v_infoState_746_);
lean_dec(v___x_745_);
v___x_747_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_746_);
v___x_748_ = lean_task_get_own(v___x_747_);
v_trees_749_ = lean_ctor_get(v___x_748_, 2);
lean_inc_ref(v_trees_749_);
lean_dec(v___x_748_);
v___x_750_ = lean_box(0);
v___x_751_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_739_, v_trees_749_, v___x_750_, v_a_732_, v_a_733_);
lean_dec_ref(v_trees_749_);
lean_dec(v_tk_739_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_751_);
if (v_isSharedCheck_758_ == 0)
{
lean_object* v_unused_759_; 
v_unused_759_ = lean_ctor_get(v___x_751_, 0);
lean_dec(v_unused_759_);
v___x_753_ = v___x_751_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_dec(v___x_751_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 0, v___x_750_);
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_750_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
else
{
return v___x_751_;
}
}
else
{
lean_dec(v_tk_739_);
return v___x_744_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_731_ = stack[0].m_obj;
lean_object* v_a_732_ = stack[1].m_obj;
lean_object* v_a_733_ = stack[2].m_obj;
lean_object* v_res_764_;
v_res_764_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(v_x_731_, v_a_732_, v_a_733_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed(lean_object* v_x_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(v_x_765_, v_a_766_, v_a_767_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
return v_res_769_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(lean_object* v_msgData_770_, lean_object* v___y_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v_msgData_770_, v___y_772_);
return v___x_774_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_770_ = stack[0].m_obj;
lean_object* v___y_771_ = stack[1].m_obj;
lean_object* v___y_772_ = stack[2].m_obj;
lean_object* v_res_775_;
v_res_775_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(v_msgData_770_, v___y_771_, v___y_772_);
stack->m_obj
 = v_res_775_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(v_msgData_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
return v_res_780_;
}
}
lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1(){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_792_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_793_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
v___x_794_ = ((lean_object*)(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4));
v___x_795_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed), 4, 0);
v___x_796_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_792_, v___x_793_, v___x_794_, v___x_795_);
return v___x_796_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_797_;
v_res_797_ = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
stack->m_obj
 = v_res_797_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___boxed(lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
return v_res_799_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_InfoTrees(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_InfoTrees(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_InfoTrees(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Command(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_InfoTrees(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_InfoTrees(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_InfoTrees(builtin);
}
#ifdef __cplusplus
}
#endif
