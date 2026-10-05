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
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___boxed(lean_object* v_00_u03b1_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0(v_00_u03b1_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(lean_object* v_opts_19_, lean_object* v_opt_20_){
_start:
{
lean_object* v_name_21_; lean_object* v_defValue_22_; lean_object* v_map_23_; lean_object* v___x_24_; 
v_name_21_ = lean_ctor_get(v_opt_20_, 0);
v_defValue_22_ = lean_ctor_get(v_opt_20_, 1);
v_map_23_ = lean_ctor_get(v_opts_19_, 0);
v___x_24_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_23_, v_name_21_);
if (lean_obj_tag(v___x_24_) == 0)
{
uint8_t v___x_25_; 
v___x_25_ = lean_unbox(v_defValue_22_);
return v___x_25_;
}
else
{
lean_object* v_val_26_; 
v_val_26_ = lean_ctor_get(v___x_24_, 0);
lean_inc(v_val_26_);
lean_dec_ref_known(v___x_24_, 1);
if (lean_obj_tag(v_val_26_) == 1)
{
uint8_t v_v_27_; 
v_v_27_ = lean_ctor_get_uint8(v_val_26_, 0);
lean_dec_ref_known(v_val_26_, 0);
return v_v_27_;
}
else
{
uint8_t v___x_28_; 
lean_dec(v_val_26_);
v___x_28_ = lean_unbox(v_defValue_22_);
return v___x_28_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3___boxed(lean_object* v_opts_29_, lean_object* v_opt_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(v_opts_29_, v_opt_30_);
lean_dec_ref(v_opt_30_);
lean_dec_ref(v_opts_29_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(uint8_t v_suppressElabErrors_34_, uint8_t v___y_35_, lean_object* v_x_36_){
_start:
{
if (lean_obj_tag(v_x_36_) == 1)
{
lean_object* v_pre_37_; 
v_pre_37_ = lean_ctor_get(v_x_36_, 0);
if (lean_obj_tag(v_pre_37_) == 0)
{
lean_object* v_str_38_; lean_object* v___x_39_; uint8_t v___x_40_; 
v_str_38_ = lean_ctor_get(v_x_36_, 1);
v___x_39_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___closed__0));
v___x_40_ = lean_string_dec_eq(v_str_38_, v___x_39_);
if (v___x_40_ == 0)
{
return v___x_40_;
}
else
{
return v_suppressElabErrors_34_;
}
}
else
{
return v___y_35_;
}
}
else
{
return v___y_35_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___boxed(lean_object* v_suppressElabErrors_41_, lean_object* v___y_42_, lean_object* v_x_43_){
_start:
{
uint8_t v_suppressElabErrors_boxed_44_; uint8_t v___y_6320__boxed_45_; uint8_t v_res_46_; lean_object* v_r_47_; 
v_suppressElabErrors_boxed_44_ = lean_unbox(v_suppressElabErrors_41_);
v___y_6320__boxed_45_ = lean_unbox(v___y_42_);
v_res_46_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(v_suppressElabErrors_boxed_44_, v___y_6320__boxed_45_, v_x_43_);
lean_dec(v_x_43_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_48_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_51_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_52_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_53_ = lean_unsigned_to_nat(0u);
v___x_54_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v___x_53_);
lean_ctor_set(v___x_54_, 2, v___x_53_);
lean_ctor_set(v___x_54_, 3, v___x_53_);
lean_ctor_set(v___x_54_, 4, v___x_52_);
lean_ctor_set(v___x_54_, 5, v___x_52_);
lean_ctor_set(v___x_54_, 6, v___x_52_);
lean_ctor_set(v___x_54_, 7, v___x_52_);
lean_ctor_set(v___x_54_, 8, v___x_52_);
lean_ctor_set(v___x_54_, 9, v___x_52_);
lean_ctor_set(v___x_54_, 10, v___x_52_);
lean_ctor_set(v___x_54_, 11, v___x_51_);
return v___x_54_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_55_ = lean_unsigned_to_nat(32u);
v___x_56_ = lean_mk_empty_array_with_capacity(v___x_55_);
v___x_57_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_57_, 0, v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_58_ = ((size_t)5ULL);
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_unsigned_to_nat(32u);
v___x_61_ = lean_mk_empty_array_with_capacity(v___x_60_);
v___x_62_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_63_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_63_, 0, v___x_62_);
lean_ctor_set(v___x_63_, 1, v___x_61_);
lean_ctor_set(v___x_63_, 2, v___x_59_);
lean_ctor_set(v___x_63_, 3, v___x_59_);
lean_ctor_set_usize(v___x_63_, 4, v___x_58_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_64_ = lean_box(1);
v___x_65_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_66_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_67_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v_env_72_; uint8_t v___x_73_; lean_object* v_env_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v_scopes_77_; lean_object* v___x_78_; lean_object* v_opts_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_71_ = lean_st_ref_get(v___y_69_);
v_env_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_env_72_);
lean_dec(v___x_71_);
v___x_73_ = 0;
v_env_74_ = l_Lean_Environment_setRecordingDeps(v_env_72_, v___x_73_);
v___x_75_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_76_ = lean_st_ref_get(v___y_69_);
v_scopes_77_ = lean_ctor_get(v___x_76_, 2);
lean_inc(v_scopes_77_);
lean_dec(v___x_76_);
v___x_78_ = l_List_head_x21___redArg(v___x_75_, v_scopes_77_);
lean_dec(v_scopes_77_);
v_opts_79_ = lean_ctor_get(v___x_78_, 1);
lean_inc_ref(v_opts_79_);
lean_dec(v___x_78_);
v___x_80_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_81_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5);
v___x_82_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_82_, 0, v_env_74_);
lean_ctor_set(v___x_82_, 1, v___x_80_);
lean_ctor_set(v___x_82_, 2, v___x_81_);
lean_ctor_set(v___x_82_, 3, v_opts_79_);
v___x_83_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v_msgData_68_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_85_, lean_object* v___y_86_, lean_object* v___y_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v_msgData_85_, v___y_86_);
lean_dec(v___y_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(lean_object* v_ref_90_, lean_object* v_msgData_91_, uint8_t v_severity_92_, uint8_t v_isSilent_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v___y_100_; uint8_t v___y_101_; lean_object* v___y_102_; uint8_t v___y_103_; lean_object* v___y_104_; lean_object* v___y_105_; uint8_t v___y_163_; lean_object* v___y_164_; uint8_t v___y_165_; uint8_t v___y_166_; lean_object* v___y_167_; uint8_t v___y_191_; lean_object* v___y_192_; uint8_t v___y_193_; uint8_t v___y_194_; lean_object* v___y_195_; uint8_t v___y_199_; uint8_t v___y_200_; uint8_t v___y_201_; uint8_t v___x_216_; uint8_t v___y_218_; uint8_t v___y_219_; uint8_t v___y_220_; uint8_t v___y_222_; uint8_t v___x_234_; 
v___x_216_ = 2;
v___x_234_ = l_Lean_instBEqMessageSeverity_beq(v_severity_92_, v___x_216_);
if (v___x_234_ == 0)
{
v___y_222_ = v___x_234_;
goto v___jp_221_;
}
else
{
uint8_t v___x_235_; 
lean_inc_ref(v_msgData_91_);
v___x_235_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_91_);
v___y_222_ = v___x_235_;
goto v___jp_221_;
}
v___jp_97_:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_Elab_Command_getScope___redArg(v___y_105_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v_currNamespace_108_; lean_object* v___x_109_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_106_, 1);
v_currNamespace_108_ = lean_ctor_get(v_a_107_, 2);
lean_inc(v_currNamespace_108_);
lean_dec(v_a_107_);
v___x_109_ = l_Lean_Elab_Command_getScope___redArg(v___y_105_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_145_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_145_ == 0)
{
v___x_112_ = v___x_109_;
v_isShared_113_ = v_isSharedCheck_145_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_a_110_);
lean_dec(v___x_109_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_145_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v_openDecls_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v_env_119_; lean_object* v_messages_120_; lean_object* v_scopes_121_; lean_object* v_usedQuotCtxts_122_; lean_object* v_nextMacroScope_123_; lean_object* v_maxRecDepth_124_; lean_object* v_ngen_125_; lean_object* v_auxDeclNGen_126_; lean_object* v_infoState_127_; lean_object* v_traceState_128_; lean_object* v_snapshotTasks_129_; lean_object* v_prevLinterStates_130_; lean_object* v_codeQualityEntryTasks_131_; lean_object* v___x_133_; uint8_t v_isShared_134_; uint8_t v_isSharedCheck_144_; 
v_openDecls_114_ = lean_ctor_get(v_a_110_, 3);
lean_inc(v_openDecls_114_);
lean_dec(v_a_110_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v_currNamespace_108_);
lean_ctor_set(v___x_115_, 1, v_openDecls_114_);
v___x_116_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v___y_100_);
lean_inc_ref(v___y_98_);
lean_inc_ref(v___y_104_);
v___x_117_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_117_, 0, v___y_104_);
lean_ctor_set(v___x_117_, 1, v___y_99_);
lean_ctor_set(v___x_117_, 2, v___y_102_);
lean_ctor_set(v___x_117_, 3, v___y_98_);
lean_ctor_set(v___x_117_, 4, v___x_116_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*5, v___y_101_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*5 + 1, v___y_103_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*5 + 2, v_isSilent_93_);
v___x_118_ = lean_st_ref_take(v___y_105_);
v_env_119_ = lean_ctor_get(v___x_118_, 0);
v_messages_120_ = lean_ctor_get(v___x_118_, 1);
v_scopes_121_ = lean_ctor_get(v___x_118_, 2);
v_usedQuotCtxts_122_ = lean_ctor_get(v___x_118_, 3);
v_nextMacroScope_123_ = lean_ctor_get(v___x_118_, 4);
v_maxRecDepth_124_ = lean_ctor_get(v___x_118_, 5);
v_ngen_125_ = lean_ctor_get(v___x_118_, 6);
v_auxDeclNGen_126_ = lean_ctor_get(v___x_118_, 7);
v_infoState_127_ = lean_ctor_get(v___x_118_, 8);
v_traceState_128_ = lean_ctor_get(v___x_118_, 9);
v_snapshotTasks_129_ = lean_ctor_get(v___x_118_, 10);
v_prevLinterStates_130_ = lean_ctor_get(v___x_118_, 11);
v_codeQualityEntryTasks_131_ = lean_ctor_get(v___x_118_, 12);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_144_ == 0)
{
v___x_133_ = v___x_118_;
v_isShared_134_ = v_isSharedCheck_144_;
goto v_resetjp_132_;
}
else
{
lean_inc(v_codeQualityEntryTasks_131_);
lean_inc(v_prevLinterStates_130_);
lean_inc(v_snapshotTasks_129_);
lean_inc(v_traceState_128_);
lean_inc(v_infoState_127_);
lean_inc(v_auxDeclNGen_126_);
lean_inc(v_ngen_125_);
lean_inc(v_maxRecDepth_124_);
lean_inc(v_nextMacroScope_123_);
lean_inc(v_usedQuotCtxts_122_);
lean_inc(v_scopes_121_);
lean_inc(v_messages_120_);
lean_inc(v_env_119_);
lean_dec(v___x_118_);
v___x_133_ = lean_box(0);
v_isShared_134_ = v_isSharedCheck_144_;
goto v_resetjp_132_;
}
v_resetjp_132_:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_138_; 
v___x_135_ = lean_box(0);
v___x_136_ = l_Lean_MessageLog_add(v___x_117_, v_messages_120_);
if (v_isShared_134_ == 0)
{
lean_ctor_set(v___x_133_, 1, v___x_136_);
v___x_138_ = v___x_133_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_env_119_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v___x_136_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_scopes_121_);
lean_ctor_set(v_reuseFailAlloc_143_, 3, v_usedQuotCtxts_122_);
lean_ctor_set(v_reuseFailAlloc_143_, 4, v_nextMacroScope_123_);
lean_ctor_set(v_reuseFailAlloc_143_, 5, v_maxRecDepth_124_);
lean_ctor_set(v_reuseFailAlloc_143_, 6, v_ngen_125_);
lean_ctor_set(v_reuseFailAlloc_143_, 7, v_auxDeclNGen_126_);
lean_ctor_set(v_reuseFailAlloc_143_, 8, v_infoState_127_);
lean_ctor_set(v_reuseFailAlloc_143_, 9, v_traceState_128_);
lean_ctor_set(v_reuseFailAlloc_143_, 10, v_snapshotTasks_129_);
lean_ctor_set(v_reuseFailAlloc_143_, 11, v_prevLinterStates_130_);
lean_ctor_set(v_reuseFailAlloc_143_, 12, v_codeQualityEntryTasks_131_);
v___x_138_ = v_reuseFailAlloc_143_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_st_ref_put(v___y_105_, v___x_138_);
if (v_isShared_113_ == 0)
{
lean_ctor_set(v___x_112_, 0, v___x_135_);
v___x_141_ = v___x_112_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_135_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_currNamespace_108_);
lean_dec(v___y_102_);
lean_dec_ref(v___y_100_);
lean_dec_ref(v___y_99_);
v_a_146_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_109_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_109_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v___y_102_);
lean_dec_ref(v___y_100_);
lean_dec_ref(v___y_99_);
v_a_154_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_106_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_106_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
v___jp_162_:
{
lean_object* v_fileName_168_; lean_object* v_fileMap_169_; uint8_t v_suppressElabErrors_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___f_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_189_; 
v_fileName_168_ = lean_ctor_get(v___y_94_, 0);
v_fileMap_169_ = lean_ctor_get(v___y_94_, 1);
v_suppressElabErrors_170_ = lean_ctor_get_uint8(v___y_94_, sizeof(void*)*10);
v___x_171_ = lean_box(v_suppressElabErrors_170_);
v___x_172_ = lean_box(v___y_163_);
v___f_173_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_173_, 0, v___x_171_);
lean_closure_set(v___f_173_, 1, v___x_172_);
v___x_174_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_91_);
v___x_175_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v___x_174_, v___y_95_);
v_a_176_ = lean_ctor_get(v___x_175_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_175_);
if (v_isSharedCheck_189_ == 0)
{
v___x_178_ = v___x_175_;
v_isShared_179_ = v_isSharedCheck_189_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_175_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_189_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
lean_inc_ref_n(v_fileMap_169_, 2);
v___x_180_ = l_Lean_FileMap_toPosition(v_fileMap_169_, v___y_164_);
lean_dec(v___y_164_);
v___x_181_ = l_Lean_FileMap_toPosition(v_fileMap_169_, v___y_167_);
lean_dec(v___y_167_);
v___x_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
v___x_183_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0));
if (v_suppressElabErrors_170_ == 0)
{
lean_del_object(v___x_178_);
lean_dec_ref(v___f_173_);
v___y_98_ = v___x_183_;
v___y_99_ = v___x_180_;
v___y_100_ = v_a_176_;
v___y_101_ = v___y_165_;
v___y_102_ = v___x_182_;
v___y_103_ = v___y_166_;
v___y_104_ = v_fileName_168_;
v___y_105_ = v___y_95_;
goto v___jp_97_;
}
else
{
uint8_t v___x_184_; 
lean_inc(v_a_176_);
v___x_184_ = l_Lean_MessageData_hasTag(v___f_173_, v_a_176_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec_ref_known(v___x_182_, 1);
lean_dec_ref(v___x_180_);
lean_dec(v_a_176_);
v___x_185_ = lean_box(0);
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_185_);
v___x_187_ = v___x_178_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
else
{
lean_del_object(v___x_178_);
v___y_98_ = v___x_183_;
v___y_99_ = v___x_180_;
v___y_100_ = v_a_176_;
v___y_101_ = v___y_165_;
v___y_102_ = v___x_182_;
v___y_103_ = v___y_166_;
v___y_104_ = v_fileName_168_;
v___y_105_ = v___y_95_;
goto v___jp_97_;
}
}
}
}
v___jp_190_:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Syntax_getTailPos_x3f(v___y_192_, v___y_193_);
lean_dec(v___y_192_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_inc(v___y_195_);
v___y_163_ = v___y_191_;
v___y_164_ = v___y_195_;
v___y_165_ = v___y_193_;
v___y_166_ = v___y_194_;
v___y_167_ = v___y_195_;
goto v___jp_162_;
}
else
{
lean_object* v_val_197_; 
v_val_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_val_197_);
lean_dec_ref_known(v___x_196_, 1);
v___y_163_ = v___y_191_;
v___y_164_ = v___y_195_;
v___y_165_ = v___y_193_;
v___y_166_ = v___y_194_;
v___y_167_ = v_val_197_;
goto v___jp_162_;
}
}
v___jp_198_:
{
lean_object* v___x_202_; 
v___x_202_ = l_Lean_Elab_Command_getRef___redArg(v___y_94_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v_ref_204_; lean_object* v___x_205_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v_ref_204_ = l_Lean_replaceRef(v_ref_90_, v_a_203_);
lean_dec(v_a_203_);
v___x_205_ = l_Lean_Syntax_getPos_x3f(v_ref_204_, v___y_200_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___y_191_ = v___y_199_;
v___y_192_ = v_ref_204_;
v___y_193_ = v___y_200_;
v___y_194_ = v___y_201_;
v___y_195_ = v___x_206_;
goto v___jp_190_;
}
else
{
lean_object* v_val_207_; 
v_val_207_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_val_207_);
lean_dec_ref_known(v___x_205_, 1);
v___y_191_ = v___y_199_;
v___y_192_ = v_ref_204_;
v___y_193_ = v___y_200_;
v___y_194_ = v___y_201_;
v___y_195_ = v_val_207_;
goto v___jp_190_;
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec_ref(v_msgData_91_);
v_a_208_ = lean_ctor_get(v___x_202_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_202_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_202_);
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
v___jp_217_:
{
if (v___y_220_ == 0)
{
v___y_199_ = v___y_218_;
v___y_200_ = v___y_219_;
v___y_201_ = v_severity_92_;
goto v___jp_198_;
}
else
{
v___y_199_ = v___y_218_;
v___y_200_ = v___y_219_;
v___y_201_ = v___x_216_;
goto v___jp_198_;
}
}
v___jp_221_:
{
if (v___y_222_ == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_scopes_225_; lean_object* v___x_226_; lean_object* v_opts_227_; uint8_t v___x_228_; uint8_t v___x_229_; 
v___x_223_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_224_ = lean_st_ref_get(v___y_95_);
v_scopes_225_ = lean_ctor_get(v___x_224_, 2);
lean_inc(v_scopes_225_);
lean_dec(v___x_224_);
v___x_226_ = l_List_head_x21___redArg(v___x_223_, v_scopes_225_);
lean_dec(v_scopes_225_);
v_opts_227_ = lean_ctor_get(v___x_226_, 1);
lean_inc_ref(v_opts_227_);
lean_dec(v___x_226_);
v___x_228_ = 1;
v___x_229_ = l_Lean_instBEqMessageSeverity_beq(v_severity_92_, v___x_228_);
if (v___x_229_ == 0)
{
lean_dec_ref(v_opts_227_);
v___y_218_ = v___y_222_;
v___y_219_ = v___y_222_;
v___y_220_ = v___x_229_;
goto v___jp_217_;
}
else
{
lean_object* v___x_230_; uint8_t v___x_231_; 
v___x_230_ = l_Lean_warningAsError;
v___x_231_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(v_opts_227_, v___x_230_);
lean_dec_ref(v_opts_227_);
v___y_218_ = v___y_222_;
v___y_219_ = v___y_222_;
v___y_220_ = v___x_231_;
goto v___jp_217_;
}
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec_ref(v_msgData_91_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
return v___x_233_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___boxed(lean_object* v_ref_236_, lean_object* v_msgData_237_, lean_object* v_severity_238_, lean_object* v_isSilent_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_){
_start:
{
uint8_t v_severity_boxed_243_; uint8_t v_isSilent_boxed_244_; lean_object* v_res_245_; 
v_severity_boxed_243_ = lean_unbox(v_severity_238_);
v_isSilent_boxed_244_ = lean_unbox(v_isSilent_239_);
v_res_245_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_ref_236_, v_msgData_237_, v_severity_boxed_243_, v_isSilent_boxed_244_, v___y_240_, v___y_241_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
lean_dec(v_ref_236_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(lean_object* v_ref_246_, lean_object* v_msgData_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
uint8_t v___x_251_; uint8_t v___x_252_; lean_object* v___x_253_; 
v___x_251_ = 0;
v___x_252_ = 0;
v___x_253_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_ref_246_, v_msgData_247_, v___x_251_, v___x_252_, v___y_248_, v___y_249_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1___boxed(lean_object* v_ref_254_, lean_object* v_msgData_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_ref_254_, v_msgData_255_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v_ref_254_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(lean_object* v_tk_263_, lean_object* v_as_264_, size_t v_sz_265_, size_t v_i_266_, lean_object* v_b_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
uint8_t v___x_271_; 
v___x_271_ = lean_usize_dec_lt(v_i_266_, v_sz_265_);
if (v___x_271_ == 0)
{
lean_object* v___x_272_; 
v___x_272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_272_, 0, v_b_267_);
return v___x_272_;
}
else
{
lean_object* v___x_273_; lean_object* v_a_274_; lean_object* v___x_275_; 
lean_dec_ref(v_b_267_);
v___x_273_ = lean_box(0);
v_a_274_ = lean_array_uget_borrowed(v_as_264_, v_i_266_);
lean_inc(v_a_274_);
v___x_275_ = l_Lean_Elab_InfoTree_format(v_a_274_, v___x_273_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v_a_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_a_276_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_275_, 1);
v___x_277_ = l_Lean_MessageData_ofFormat(v_a_276_);
v___x_278_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_263_, v___x_277_, v___y_268_, v___y_269_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_279_; size_t v___x_280_; size_t v___x_281_; 
lean_dec_ref_known(v___x_278_, 1);
v___x_279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0));
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_add(v_i_266_, v___x_280_);
v_i_266_ = v___x_281_;
v_b_267_ = v___x_279_;
goto _start;
}
else
{
lean_object* v_a_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_290_; 
v_a_283_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_290_ == 0)
{
v___x_285_ = v___x_278_;
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_a_283_);
lean_dec(v___x_278_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_290_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_288_; 
if (v_isShared_286_ == 0)
{
v___x_288_ = v___x_285_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v_a_283_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
}
}
}
}
else
{
lean_object* v_a_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_303_; 
v_a_291_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_303_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_303_ == 0)
{
v___x_293_ = v___x_275_;
v_isShared_294_ = v_isSharedCheck_303_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_a_291_);
lean_dec(v___x_275_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_303_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v_ref_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v_ref_295_ = lean_ctor_get(v___y_268_, 7);
v___x_296_ = lean_io_error_to_string(v_a_291_);
v___x_297_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
v___x_298_ = l_Lean_MessageData_ofFormat(v___x_297_);
lean_inc(v_ref_295_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_ref_295_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 0, v___x_299_);
v___x_301_ = v___x_293_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___boxed(lean_object* v_tk_304_, lean_object* v_as_305_, lean_object* v_sz_306_, lean_object* v_i_307_, lean_object* v_b_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_){
_start:
{
size_t v_sz_boxed_312_; size_t v_i_boxed_313_; lean_object* v_res_314_; 
v_sz_boxed_312_ = lean_unbox_usize(v_sz_306_);
lean_dec(v_sz_306_);
v_i_boxed_313_ = lean_unbox_usize(v_i_307_);
lean_dec(v_i_307_);
v_res_314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(v_tk_304_, v_as_305_, v_sz_boxed_312_, v_i_boxed_313_, v_b_308_, v___y_309_, v___y_310_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec_ref(v_as_305_);
lean_dec(v_tk_304_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(lean_object* v_tk_315_, lean_object* v_as_316_, size_t v_sz_317_, size_t v_i_318_, lean_object* v_b_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
uint8_t v___x_323_; 
v___x_323_ = lean_usize_dec_lt(v_i_318_, v_sz_317_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
v___x_324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_324_, 0, v_b_319_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; lean_object* v_a_326_; lean_object* v___x_327_; 
lean_dec_ref(v_b_319_);
v___x_325_ = lean_box(0);
v_a_326_ = lean_array_uget_borrowed(v_as_316_, v_i_318_);
lean_inc(v_a_326_);
v___x_327_ = l_Lean_Elab_InfoTree_format(v_a_326_, v___x_325_);
if (lean_obj_tag(v___x_327_) == 0)
{
lean_object* v_a_328_; lean_object* v___x_329_; lean_object* v___x_330_; 
v_a_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_a_328_);
lean_dec_ref_known(v___x_327_, 1);
v___x_329_ = l_Lean_MessageData_ofFormat(v_a_328_);
v___x_330_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_315_, v___x_329_, v___y_320_, v___y_321_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v___x_331_; size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
lean_dec_ref_known(v___x_330_, 1);
v___x_331_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0));
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_318_, v___x_332_);
v___x_334_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(v_tk_315_, v_as_316_, v_sz_317_, v___x_333_, v___x_331_, v___y_320_, v___y_321_);
return v___x_334_;
}
else
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_342_; 
v_a_335_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_342_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_342_ == 0)
{
v___x_337_ = v___x_330_;
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_330_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_342_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_a_335_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
else
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_355_; 
v_a_343_ = lean_ctor_get(v___x_327_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_327_);
if (v_isSharedCheck_355_ == 0)
{
v___x_345_ = v___x_327_;
v_isShared_346_ = v_isSharedCheck_355_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_327_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_355_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_ref_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v_ref_347_ = lean_ctor_get(v___y_320_, 7);
v___x_348_ = lean_io_error_to_string(v_a_343_);
v___x_349_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
v___x_350_ = l_Lean_MessageData_ofFormat(v___x_349_);
lean_inc(v_ref_347_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_ref_347_);
lean_ctor_set(v___x_351_, 1, v___x_350_);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v___x_351_);
v___x_353_ = v___x_345_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4___boxed(lean_object* v_tk_356_, lean_object* v_as_357_, lean_object* v_sz_358_, lean_object* v_i_359_, lean_object* v_b_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
size_t v_sz_boxed_364_; size_t v_i_boxed_365_; lean_object* v_res_366_; 
v_sz_boxed_364_ = lean_unbox_usize(v_sz_358_);
lean_dec(v_sz_358_);
v_i_boxed_365_ = lean_unbox_usize(v_i_359_);
lean_dec(v_i_359_);
v_res_366_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(v_tk_356_, v_as_357_, v_sz_boxed_364_, v_i_boxed_365_, v_b_360_, v___y_361_, v___y_362_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec_ref(v_as_357_);
lean_dec(v_tk_356_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(lean_object* v_tk_370_, lean_object* v_as_371_, size_t v_sz_372_, size_t v_i_373_, lean_object* v_b_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = lean_usize_dec_lt(v_i_373_, v_sz_372_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
v___x_379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_379_, 0, v_b_374_);
return v___x_379_;
}
else
{
lean_object* v___x_380_; lean_object* v_a_381_; lean_object* v___x_382_; 
lean_dec_ref(v_b_374_);
v___x_380_ = lean_box(0);
v_a_381_ = lean_array_uget_borrowed(v_as_371_, v_i_373_);
lean_inc(v_a_381_);
v___x_382_ = l_Lean_Elab_InfoTree_format(v_a_381_, v___x_380_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_a_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_a_383_);
lean_dec_ref_known(v___x_382_, 1);
v___x_384_ = l_Lean_MessageData_ofFormat(v_a_383_);
v___x_385_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_370_, v___x_384_, v___y_375_, v___y_376_);
if (lean_obj_tag(v___x_385_) == 0)
{
lean_object* v___x_386_; size_t v___x_387_; size_t v___x_388_; 
lean_dec_ref_known(v___x_385_, 1);
v___x_386_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0));
v___x_387_ = ((size_t)1ULL);
v___x_388_ = lean_usize_add(v_i_373_, v___x_387_);
v_i_373_ = v___x_388_;
v_b_374_ = v___x_386_;
goto _start;
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v_a_390_ = lean_ctor_get(v___x_385_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_385_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_385_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_385_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_410_; 
v_a_398_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_410_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_410_ == 0)
{
v___x_400_ = v___x_382_;
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_382_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_410_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_ref_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_408_; 
v_ref_402_ = lean_ctor_get(v___y_375_, 7);
v___x_403_ = lean_io_error_to_string(v_a_398_);
v___x_404_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
v___x_405_ = l_Lean_MessageData_ofFormat(v___x_404_);
lean_inc(v_ref_402_);
v___x_406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_406_, 0, v_ref_402_);
lean_ctor_set(v___x_406_, 1, v___x_405_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_406_);
v___x_408_ = v___x_400_;
goto v_reusejp_407_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
v___x_408_ = v_reuseFailAlloc_409_;
goto v_reusejp_407_;
}
v_reusejp_407_:
{
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___boxed(lean_object* v_tk_411_, lean_object* v_as_412_, lean_object* v_sz_413_, lean_object* v_i_414_, lean_object* v_b_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_){
_start:
{
size_t v_sz_boxed_419_; size_t v_i_boxed_420_; lean_object* v_res_421_; 
v_sz_boxed_419_ = lean_unbox_usize(v_sz_413_);
lean_dec(v_sz_413_);
v_i_boxed_420_ = lean_unbox_usize(v_i_414_);
lean_dec(v_i_414_);
v_res_421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(v_tk_411_, v_as_412_, v_sz_boxed_419_, v_i_boxed_420_, v_b_415_, v___y_416_, v___y_417_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec_ref(v_as_412_);
lean_dec(v_tk_411_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(lean_object* v_tk_422_, lean_object* v_as_423_, size_t v_sz_424_, size_t v_i_425_, lean_object* v_b_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
uint8_t v___x_430_; 
v___x_430_ = lean_usize_dec_lt(v_i_425_, v_sz_424_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
v___x_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_431_, 0, v_b_426_);
return v___x_431_;
}
else
{
lean_object* v___x_432_; lean_object* v_a_433_; lean_object* v___x_434_; 
lean_dec_ref(v_b_426_);
v___x_432_ = lean_box(0);
v_a_433_ = lean_array_uget_borrowed(v_as_423_, v_i_425_);
lean_inc(v_a_433_);
v___x_434_ = l_Lean_Elab_InfoTree_format(v_a_433_, v___x_432_);
if (lean_obj_tag(v___x_434_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v_a_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v___x_434_, 1);
v___x_436_ = l_Lean_MessageData_ofFormat(v_a_435_);
v___x_437_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_422_, v___x_436_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v___x_438_; size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
lean_dec_ref_known(v___x_437_, 1);
v___x_438_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0));
v___x_439_ = ((size_t)1ULL);
v___x_440_ = lean_usize_add(v_i_425_, v___x_439_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(v_tk_422_, v_as_423_, v_sz_424_, v___x_440_, v___x_438_, v___y_427_, v___y_428_);
return v___x_441_;
}
else
{
lean_object* v_a_442_; lean_object* v___x_444_; uint8_t v_isShared_445_; uint8_t v_isSharedCheck_449_; 
v_a_442_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_449_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_449_ == 0)
{
v___x_444_ = v___x_437_;
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
else
{
lean_inc(v_a_442_);
lean_dec(v___x_437_);
v___x_444_ = lean_box(0);
v_isShared_445_ = v_isSharedCheck_449_;
goto v_resetjp_443_;
}
v_resetjp_443_:
{
lean_object* v___x_447_; 
if (v_isShared_445_ == 0)
{
v___x_447_ = v___x_444_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_448_; 
v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
v___x_447_ = v_reuseFailAlloc_448_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
return v___x_447_;
}
}
}
}
else
{
lean_object* v_a_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_462_; 
v_a_450_ = lean_ctor_get(v___x_434_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_434_);
if (v_isSharedCheck_462_ == 0)
{
v___x_452_ = v___x_434_;
v_isShared_453_ = v_isSharedCheck_462_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_a_450_);
lean_dec(v___x_434_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_462_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v_ref_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
v_ref_454_ = lean_ctor_get(v___y_427_, 7);
v___x_455_ = lean_io_error_to_string(v_a_450_);
v___x_456_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_456_, 0, v___x_455_);
v___x_457_ = l_Lean_MessageData_ofFormat(v___x_456_);
lean_inc(v_ref_454_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_ref_454_);
lean_ctor_set(v___x_458_, 1, v___x_457_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 0, v___x_458_);
v___x_460_ = v___x_452_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7___boxed(lean_object* v_tk_463_, lean_object* v_as_464_, lean_object* v_sz_465_, lean_object* v_i_466_, lean_object* v_b_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
size_t v_sz_boxed_471_; size_t v_i_boxed_472_; lean_object* v_res_473_; 
v_sz_boxed_471_ = lean_unbox_usize(v_sz_465_);
lean_dec(v_sz_465_);
v_i_boxed_472_ = lean_unbox_usize(v_i_466_);
lean_dec(v_i_466_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(v_tk_463_, v_as_464_, v_sz_boxed_471_, v_i_boxed_472_, v_b_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec_ref(v_as_464_);
lean_dec(v_tk_463_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(lean_object* v_init_474_, lean_object* v_tk_475_, lean_object* v_n_476_, lean_object* v_b_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
if (lean_obj_tag(v_n_476_) == 0)
{
lean_object* v_cs_481_; lean_object* v___x_482_; lean_object* v___x_483_; size_t v_sz_484_; size_t v___x_485_; lean_object* v___x_486_; 
v_cs_481_ = lean_ctor_get(v_n_476_, 0);
v___x_482_ = lean_box(0);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v_b_477_);
v_sz_484_ = lean_array_size(v_cs_481_);
v___x_485_ = ((size_t)0ULL);
v___x_486_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(v_init_474_, v_tk_475_, v_cs_481_, v_sz_484_, v___x_485_, v___x_483_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_486_) == 0)
{
lean_object* v_a_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_501_; 
v_a_487_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_501_ == 0)
{
v___x_489_ = v___x_486_;
v_isShared_490_ = v_isSharedCheck_501_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_a_487_);
lean_dec(v___x_486_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_501_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v_fst_491_; 
v_fst_491_ = lean_ctor_get(v_a_487_, 0);
if (lean_obj_tag(v_fst_491_) == 0)
{
lean_object* v_snd_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v_snd_492_ = lean_ctor_get(v_a_487_, 1);
lean_inc(v_snd_492_);
lean_dec(v_a_487_);
v___x_493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_493_, 0, v_snd_492_);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v___x_493_);
v___x_495_ = v___x_489_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
lean_object* v_val_497_; lean_object* v___x_499_; 
lean_inc_ref(v_fst_491_);
lean_dec(v_a_487_);
v_val_497_ = lean_ctor_get(v_fst_491_, 0);
lean_inc(v_val_497_);
lean_dec_ref_known(v_fst_491_, 1);
if (v_isShared_490_ == 0)
{
lean_ctor_set(v___x_489_, 0, v_val_497_);
v___x_499_ = v___x_489_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_val_497_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
}
}
else
{
lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_a_502_ = lean_ctor_get(v___x_486_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_486_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_486_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_486_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
else
{
lean_object* v_vs_510_; lean_object* v___x_511_; lean_object* v___x_512_; size_t v_sz_513_; size_t v___x_514_; lean_object* v___x_515_; 
v_vs_510_ = lean_ctor_get(v_n_476_, 0);
v___x_511_ = lean_box(0);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_b_477_);
v_sz_513_ = lean_array_size(v_vs_510_);
v___x_514_ = ((size_t)0ULL);
v___x_515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(v_tk_475_, v_vs_510_, v_sz_513_, v___x_514_, v___x_512_, v___y_478_, v___y_479_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_530_; 
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_530_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_530_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_530_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v_fst_520_; 
v_fst_520_ = lean_ctor_get(v_a_516_, 0);
if (lean_obj_tag(v_fst_520_) == 0)
{
lean_object* v_snd_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
v_snd_521_ = lean_ctor_get(v_a_516_, 1);
lean_inc(v_snd_521_);
lean_dec(v_a_516_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v_snd_521_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_522_);
v___x_524_ = v___x_518_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
else
{
lean_object* v_val_526_; lean_object* v___x_528_; 
lean_inc_ref(v_fst_520_);
lean_dec(v_a_516_);
v_val_526_ = lean_ctor_get(v_fst_520_, 0);
lean_inc(v_val_526_);
lean_dec_ref_known(v_fst_520_, 1);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v_val_526_);
v___x_528_ = v___x_518_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_val_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_object* v_a_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
v_a_531_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_538_ == 0)
{
v___x_533_ = v___x_515_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_a_531_);
lean_dec(v___x_515_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_531_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(lean_object* v_init_539_, lean_object* v_tk_540_, lean_object* v_as_541_, size_t v_sz_542_, size_t v_i_543_, lean_object* v_b_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
uint8_t v___x_548_; 
v___x_548_ = lean_usize_dec_lt(v_i_543_, v_sz_542_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; 
v___x_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_549_, 0, v_b_544_);
return v___x_549_;
}
else
{
lean_object* v_snd_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_584_; 
v_snd_550_ = lean_ctor_get(v_b_544_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_b_544_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v_b_544_, 0);
lean_dec(v_unused_585_);
v___x_552_ = v_b_544_;
v_isShared_553_ = v_isSharedCheck_584_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_550_);
lean_dec(v_b_544_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_584_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v_a_555_; lean_object* v___x_556_; 
v___x_554_ = lean_box(0);
v_a_555_ = lean_array_uget_borrowed(v_as_541_, v_i_543_);
lean_inc(v_snd_550_);
v___x_556_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_539_, v_tk_540_, v_a_555_, v_snd_550_, v___y_545_, v___y_546_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v_a_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_575_; 
v_a_557_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_575_ == 0)
{
v___x_559_ = v___x_556_;
v_isShared_560_ = v_isSharedCheck_575_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_a_557_);
lean_dec(v___x_556_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_575_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
if (lean_obj_tag(v_a_557_) == 0)
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_561_, 0, v_a_557_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_561_);
v___x_563_ = v___x_552_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_561_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v_snd_550_);
v___x_563_ = v_reuseFailAlloc_567_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_563_);
v___x_565_ = v___x_559_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; 
lean_del_object(v___x_559_);
lean_dec(v_snd_550_);
v_a_568_ = lean_ctor_get(v_a_557_, 0);
lean_inc(v_a_568_);
lean_dec_ref_known(v_a_557_, 1);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 1, v_a_568_);
lean_ctor_set(v___x_552_, 0, v___x_554_);
v___x_570_ = v___x_552_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_554_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_a_568_);
v___x_570_ = v_reuseFailAlloc_574_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
size_t v___x_571_; size_t v___x_572_; 
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_543_, v___x_571_);
v_i_543_ = v___x_572_;
v_b_544_ = v___x_570_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_583_; 
lean_del_object(v___x_552_);
lean_dec(v_snd_550_);
v_a_576_ = lean_ctor_get(v___x_556_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_556_);
if (v_isSharedCheck_583_ == 0)
{
v___x_578_ = v___x_556_;
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_a_576_);
lean_dec(v___x_556_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_583_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_581_; 
if (v_isShared_579_ == 0)
{
v___x_581_ = v___x_578_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_a_576_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6___boxed(lean_object* v_init_586_, lean_object* v_tk_587_, lean_object* v_as_588_, lean_object* v_sz_589_, lean_object* v_i_590_, lean_object* v_b_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
size_t v_sz_boxed_595_; size_t v_i_boxed_596_; lean_object* v_res_597_; 
v_sz_boxed_595_ = lean_unbox_usize(v_sz_589_);
lean_dec(v_sz_589_);
v_i_boxed_596_ = lean_unbox_usize(v_i_590_);
lean_dec(v_i_590_);
v_res_597_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(v_init_586_, v_tk_587_, v_as_588_, v_sz_boxed_595_, v_i_boxed_596_, v_b_591_, v___y_592_, v___y_593_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec_ref(v_as_588_);
lean_dec(v_tk_587_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___boxed(lean_object* v_init_598_, lean_object* v_tk_599_, lean_object* v_n_600_, lean_object* v_b_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_598_, v_tk_599_, v_n_600_, v_b_601_, v___y_602_, v___y_603_);
lean_dec(v___y_603_);
lean_dec_ref(v___y_602_);
lean_dec_ref(v_n_600_);
lean_dec(v_tk_599_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(lean_object* v_tk_606_, lean_object* v_t_607_, lean_object* v_init_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_root_612_; lean_object* v_tail_613_; lean_object* v___x_614_; 
v_root_612_ = lean_ctor_get(v_t_607_, 0);
v_tail_613_ = lean_ctor_get(v_t_607_, 1);
v___x_614_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_608_, v_tk_606_, v_root_612_, v_init_608_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v_a_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_651_; 
v_a_615_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_651_ == 0)
{
v___x_617_ = v___x_614_;
v_isShared_618_ = v_isSharedCheck_651_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_a_615_);
lean_dec(v___x_614_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_651_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
if (lean_obj_tag(v_a_615_) == 0)
{
lean_object* v_a_619_; lean_object* v___x_621_; 
v_a_619_ = lean_ctor_get(v_a_615_, 0);
lean_inc(v_a_619_);
lean_dec_ref_known(v_a_615_, 1);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v_a_619_);
v___x_621_ = v___x_617_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_a_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
else
{
lean_object* v_a_623_; lean_object* v___x_624_; lean_object* v___x_625_; size_t v_sz_626_; size_t v___x_627_; lean_object* v___x_628_; 
lean_del_object(v___x_617_);
v_a_623_ = lean_ctor_get(v_a_615_, 0);
lean_inc(v_a_623_);
lean_dec_ref_known(v_a_615_, 1);
v___x_624_ = lean_box(0);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v_a_623_);
v_sz_626_ = lean_array_size(v_tail_613_);
v___x_627_ = ((size_t)0ULL);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(v_tk_606_, v_tail_613_, v_sz_626_, v___x_627_, v___x_625_, v___y_609_, v___y_610_);
if (lean_obj_tag(v___x_628_) == 0)
{
lean_object* v_a_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_642_; 
v_a_629_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_642_ == 0)
{
v___x_631_ = v___x_628_;
v_isShared_632_ = v_isSharedCheck_642_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_a_629_);
lean_dec(v___x_628_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_642_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v_fst_633_; 
v_fst_633_ = lean_ctor_get(v_a_629_, 0);
if (lean_obj_tag(v_fst_633_) == 0)
{
lean_object* v_snd_634_; lean_object* v___x_636_; 
v_snd_634_ = lean_ctor_get(v_a_629_, 1);
lean_inc(v_snd_634_);
lean_dec(v_a_629_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v_snd_634_);
v___x_636_ = v___x_631_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v_snd_634_);
v___x_636_ = v_reuseFailAlloc_637_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
return v___x_636_;
}
}
else
{
lean_object* v_val_638_; lean_object* v___x_640_; 
lean_inc_ref(v_fst_633_);
lean_dec(v_a_629_);
v_val_638_ = lean_ctor_get(v_fst_633_, 0);
lean_inc(v_val_638_);
lean_dec_ref_known(v_fst_633_, 1);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 0, v_val_638_);
v___x_640_ = v___x_631_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_val_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
else
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_650_; 
v_a_643_ = lean_ctor_get(v___x_628_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v___x_628_);
if (v_isSharedCheck_650_ == 0)
{
v___x_645_ = v___x_628_;
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_628_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_650_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v___x_648_; 
if (v_isShared_646_ == 0)
{
v___x_648_ = v___x_645_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v_a_643_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_654_; uint8_t v_isShared_655_; uint8_t v_isSharedCheck_659_; 
v_a_652_ = lean_ctor_get(v___x_614_, 0);
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_659_ == 0)
{
v___x_654_ = v___x_614_;
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
else
{
lean_inc(v_a_652_);
lean_dec(v___x_614_);
v___x_654_ = lean_box(0);
v_isShared_655_ = v_isSharedCheck_659_;
goto v_resetjp_653_;
}
v_resetjp_653_:
{
lean_object* v___x_657_; 
if (v_isShared_655_ == 0)
{
v___x_657_ = v___x_654_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_a_652_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2___boxed(lean_object* v_tk_660_, lean_object* v_t_661_, lean_object* v_init_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_660_, v_t_661_, v_init_662_, v___y_663_, v___y_664_);
lean_dec(v___y_664_);
lean_dec_ref(v___y_663_);
lean_dec_ref(v_t_661_);
lean_dec(v_tk_660_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(lean_object* v_msgData_667_, uint8_t v_severity_668_, uint8_t v_isSilent_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
lean_object* v___x_673_; 
v___x_673_ = l_Lean_Elab_Command_getRef___redArg(v___y_670_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_a_674_, v_msgData_667_, v_severity_668_, v_isSilent_669_, v___y_670_, v___y_671_);
lean_dec(v_a_674_);
return v___x_675_;
}
else
{
lean_object* v_a_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_683_; 
lean_dec_ref(v_msgData_667_);
v_a_676_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_683_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_683_ == 0)
{
v___x_678_ = v___x_673_;
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_a_676_);
lean_dec(v___x_673_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_683_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v___x_681_; 
if (v_isShared_679_ == 0)
{
v___x_681_ = v___x_678_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_a_676_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6___boxed(lean_object* v_msgData_684_, lean_object* v_severity_685_, lean_object* v_isSilent_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
uint8_t v_severity_boxed_690_; uint8_t v_isSilent_boxed_691_; lean_object* v_res_692_; 
v_severity_boxed_690_ = lean_unbox(v_severity_685_);
v_isSilent_boxed_691_ = lean_unbox(v_isSilent_686_);
v_res_692_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_msgData_684_, v_severity_boxed_690_, v_isSilent_boxed_691_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object* v_msgData_693_, lean_object* v___y_694_, lean_object* v___y_695_){
_start:
{
uint8_t v___x_697_; uint8_t v___x_698_; lean_object* v___x_699_; 
v___x_697_ = 2;
v___x_698_ = 0;
v___x_699_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_msgData_693_, v___x_697_, v___x_698_, v___y_694_, v___y_695_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3___boxed(lean_object* v_msgData_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v_msgData_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
return v_res_704_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4));
v___x_714_ = l_Lean_MessageData_ofFormat(v___x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(lean_object* v_x_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_719_; uint8_t v___x_720_; 
v___x_719_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
lean_inc(v_x_715_);
v___x_720_ = l_Lean_Syntax_isOfKind(v_x_715_, v___x_719_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; 
lean_dec(v_x_715_);
v___x_721_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v_tk_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_infoState_744_; uint8_t v_enabled_745_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v_tk_723_ = l_Lean_Syntax_getArg(v_x_715_, v___x_722_);
v___x_724_ = lean_unsigned_to_nat(2u);
v___x_725_ = l_Lean_Syntax_getArg(v_x_715_, v___x_724_);
lean_dec(v_x_715_);
v___x_726_ = lean_st_ref_get(v_a_717_);
v_infoState_744_ = lean_ctor_get(v___x_726_, 8);
lean_inc_ref(v_infoState_744_);
lean_dec(v___x_726_);
v_enabled_745_ = lean_ctor_get_uint8(v_infoState_744_, sizeof(void*)*3);
lean_dec_ref(v_infoState_744_);
if (v_enabled_745_ == 0)
{
if (v___x_720_ == 0)
{
goto v___jp_727_;
}
else
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v___x_725_);
lean_dec(v_tk_723_);
v___x_746_ = lean_obj_once(&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5, &l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5_once, _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5);
v___x_747_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_746_, v_a_716_, v_a_717_);
return v___x_747_;
}
}
else
{
goto v___jp_727_;
}
v___jp_727_:
{
lean_object* v___x_728_; 
v___x_728_ = l_Lean_Elab_Command_elabCommand(v___x_725_, v_a_716_, v_a_717_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_729_; lean_object* v_infoState_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v_trees_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
lean_dec_ref_known(v___x_728_, 1);
v___x_729_ = lean_st_ref_get(v_a_717_);
v_infoState_730_ = lean_ctor_get(v___x_729_, 8);
lean_inc_ref(v_infoState_730_);
lean_dec(v___x_729_);
v___x_731_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_730_);
v___x_732_ = lean_task_get_own(v___x_731_);
v_trees_733_ = lean_ctor_get(v___x_732_, 2);
lean_inc_ref(v_trees_733_);
lean_dec(v___x_732_);
v___x_734_ = lean_box(0);
v___x_735_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_723_, v_trees_733_, v___x_734_, v_a_716_, v_a_717_);
lean_dec_ref(v_trees_733_);
lean_dec(v_tk_723_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v___x_735_, 0);
lean_dec(v_unused_743_);
v___x_737_ = v___x_735_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_dec(v___x_735_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 0, v___x_734_);
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_734_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
else
{
return v___x_735_;
}
}
else
{
lean_dec(v_tk_723_);
return v___x_728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed(lean_object* v_x_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(v_x_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(lean_object* v_msgData_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v_msgData_753_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(v_msgData_758_, v___y_759_, v___y_760_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1(){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_774_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_775_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
v___x_776_ = ((lean_object*)(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4));
v___x_777_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed), 4, 0);
v___x_778_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_774_, v___x_775_, v___x_776_, v___x_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___boxed(lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
return v_res_780_;
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
