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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
extern lean_object* l_Lean_Elab_Command_instInhabitedScope_default;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_dec_ref(v___x_24_);
if (lean_obj_tag(v_val_26_) == 1)
{
uint8_t v_v_27_; 
v_v_27_ = lean_ctor_get_uint8(v_val_26_, 0);
lean_dec_ref(v_val_26_);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(uint8_t v___y_34_, uint8_t v_suppressElabErrors_35_, lean_object* v_x_36_){
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
return v___y_34_;
}
else
{
return v_suppressElabErrors_35_;
}
}
else
{
return v___y_34_;
}
}
else
{
return v___y_34_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___boxed(lean_object* v___y_41_, lean_object* v_suppressElabErrors_42_, lean_object* v_x_43_){
_start:
{
uint8_t v___y_6638__boxed_44_; uint8_t v_suppressElabErrors_boxed_45_; uint8_t v_res_46_; lean_object* v_r_47_; 
v___y_6638__boxed_44_ = lean_unbox(v___y_41_);
v_suppressElabErrors_boxed_45_ = lean_unbox(v_suppressElabErrors_42_);
v_res_46_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0(v___y_6638__boxed_44_, v_suppressElabErrors_boxed_45_, v_x_43_);
lean_dec(v_x_43_);
v_r_47_ = lean_box(v_res_46_);
return v_r_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_52_ = lean_unsigned_to_nat(0u);
v___x_53_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_53_, 0, v___x_52_);
lean_ctor_set(v___x_53_, 1, v___x_52_);
lean_ctor_set(v___x_53_, 2, v___x_52_);
lean_ctor_set(v___x_53_, 3, v___x_52_);
lean_ctor_set(v___x_53_, 4, v___x_51_);
lean_ctor_set(v___x_53_, 5, v___x_51_);
lean_ctor_set(v___x_53_, 6, v___x_51_);
lean_ctor_set(v___x_53_, 7, v___x_51_);
lean_ctor_set(v___x_53_, 8, v___x_51_);
lean_ctor_set(v___x_53_, 9, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_54_ = lean_unsigned_to_nat(32u);
v___x_55_ = lean_mk_empty_array_with_capacity(v___x_54_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4(void){
_start:
{
size_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_57_ = ((size_t)5ULL);
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_unsigned_to_nat(32u);
v___x_60_ = lean_mk_empty_array_with_capacity(v___x_59_);
v___x_61_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__3);
v___x_62_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
lean_ctor_set(v___x_62_, 2, v___x_58_);
lean_ctor_set(v___x_62_, 3, v___x_58_);
lean_ctor_set_usize(v___x_62_, 4, v___x_57_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_63_ = lean_box(1);
v___x_64_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__4);
v___x_65_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__1);
v___x_66_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_63_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(lean_object* v_msgData_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; lean_object* v_env_71_; lean_object* v___x_72_; lean_object* v_scopes_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v_opts_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_env_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref(v_env_71_);
lean_dec(v___x_70_);
v___x_72_ = lean_st_ref_get(v___y_68_);
v_scopes_73_ = lean_ctor_get(v___x_72_, 2);
lean_inc(v_scopes_73_);
lean_dec(v___x_72_);
v___x_74_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_75_ = l_List_head_x21___redArg(v___x_74_, v_scopes_73_);
lean_dec(v_scopes_73_);
v_opts_76_ = lean_ctor_get(v___x_75_, 1);
lean_inc_ref(v_opts_76_);
lean_dec(v___x_75_);
v___x_77_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__2);
v___x_78_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___closed__5);
v___x_79_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_79_, 0, v_env_71_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
lean_ctor_set(v___x_79_, 2, v___x_78_);
lean_ctor_set(v___x_79_, 3, v_opts_76_);
v___x_80_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v_msgData_67_);
v___x_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msgData_82_, lean_object* v___y_83_, lean_object* v___y_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v_msgData_82_, v___y_83_);
lean_dec(v___y_83_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(lean_object* v_ref_87_, lean_object* v_msgData_88_, uint8_t v_severity_89_, uint8_t v_isSilent_90_, lean_object* v___y_91_, lean_object* v___y_92_){
_start:
{
uint8_t v___y_95_; uint8_t v___y_96_; lean_object* v___y_97_; lean_object* v___y_98_; lean_object* v___y_99_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; uint8_t v___y_158_; uint8_t v___y_159_; uint8_t v___y_160_; lean_object* v___y_161_; lean_object* v___y_162_; uint8_t v___y_186_; uint8_t v___y_187_; uint8_t v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; uint8_t v___y_194_; uint8_t v___y_195_; uint8_t v___y_196_; uint8_t v___x_211_; uint8_t v___y_213_; uint8_t v___y_214_; uint8_t v___y_215_; uint8_t v___y_217_; uint8_t v___x_229_; 
v___x_211_ = 2;
v___x_229_ = l_Lean_instBEqMessageSeverity_beq(v_severity_89_, v___x_211_);
if (v___x_229_ == 0)
{
v___y_217_ = v___x_229_;
goto v___jp_216_;
}
else
{
uint8_t v___x_230_; 
lean_inc_ref(v_msgData_88_);
v___x_230_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_88_);
v___y_217_ = v___x_230_;
goto v___jp_216_;
}
v___jp_94_:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_Elab_Command_getScope___redArg(v___y_102_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref(v___x_103_);
v___x_105_ = l_Lean_Elab_Command_getScope___redArg(v___y_102_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_140_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_140_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_140_ == 0)
{
v___x_108_ = v___x_105_;
v_isShared_109_ = v_isSharedCheck_140_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_a_106_);
lean_dec(v___x_105_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_140_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; lean_object* v_currNamespace_111_; lean_object* v_openDecls_112_; lean_object* v_env_113_; lean_object* v_messages_114_; lean_object* v_scopes_115_; lean_object* v_usedQuotCtxts_116_; lean_object* v_nextMacroScope_117_; lean_object* v_maxRecDepth_118_; lean_object* v_ngen_119_; lean_object* v_auxDeclNGen_120_; lean_object* v_infoState_121_; lean_object* v_traceState_122_; lean_object* v_snapshotTasks_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_139_; 
v___x_110_ = lean_st_ref_take(v___y_102_);
v_currNamespace_111_ = lean_ctor_get(v_a_104_, 2);
lean_inc(v_currNamespace_111_);
lean_dec(v_a_104_);
v_openDecls_112_ = lean_ctor_get(v_a_106_, 3);
lean_inc(v_openDecls_112_);
lean_dec(v_a_106_);
v_env_113_ = lean_ctor_get(v___x_110_, 0);
v_messages_114_ = lean_ctor_get(v___x_110_, 1);
v_scopes_115_ = lean_ctor_get(v___x_110_, 2);
v_usedQuotCtxts_116_ = lean_ctor_get(v___x_110_, 3);
v_nextMacroScope_117_ = lean_ctor_get(v___x_110_, 4);
v_maxRecDepth_118_ = lean_ctor_get(v___x_110_, 5);
v_ngen_119_ = lean_ctor_get(v___x_110_, 6);
v_auxDeclNGen_120_ = lean_ctor_get(v___x_110_, 7);
v_infoState_121_ = lean_ctor_get(v___x_110_, 8);
v_traceState_122_ = lean_ctor_get(v___x_110_, 9);
v_snapshotTasks_123_ = lean_ctor_get(v___x_110_, 10);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_139_ == 0)
{
v___x_125_ = v___x_110_;
v_isShared_126_ = v_isSharedCheck_139_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_snapshotTasks_123_);
lean_inc(v_traceState_122_);
lean_inc(v_infoState_121_);
lean_inc(v_auxDeclNGen_120_);
lean_inc(v_ngen_119_);
lean_inc(v_maxRecDepth_118_);
lean_inc(v_nextMacroScope_117_);
lean_inc(v_usedQuotCtxts_116_);
lean_inc(v_scopes_115_);
lean_inc(v_messages_114_);
lean_inc(v_env_113_);
lean_dec(v___x_110_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_139_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_132_; 
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_currNamespace_111_);
lean_ctor_set(v___x_127_, 1, v_openDecls_112_);
v___x_128_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___y_99_);
lean_inc_ref(v___y_100_);
lean_inc_ref(v___y_98_);
v___x_129_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_129_, 0, v___y_98_);
lean_ctor_set(v___x_129_, 1, v___y_97_);
lean_ctor_set(v___x_129_, 2, v___y_101_);
lean_ctor_set(v___x_129_, 3, v___y_100_);
lean_ctor_set(v___x_129_, 4, v___x_128_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*5, v___y_96_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*5 + 1, v___y_95_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*5 + 2, v_isSilent_90_);
v___x_130_ = l_Lean_MessageLog_add(v___x_129_, v_messages_114_);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 1, v___x_130_);
v___x_132_ = v___x_125_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_env_113_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_130_);
lean_ctor_set(v_reuseFailAlloc_138_, 2, v_scopes_115_);
lean_ctor_set(v_reuseFailAlloc_138_, 3, v_usedQuotCtxts_116_);
lean_ctor_set(v_reuseFailAlloc_138_, 4, v_nextMacroScope_117_);
lean_ctor_set(v_reuseFailAlloc_138_, 5, v_maxRecDepth_118_);
lean_ctor_set(v_reuseFailAlloc_138_, 6, v_ngen_119_);
lean_ctor_set(v_reuseFailAlloc_138_, 7, v_auxDeclNGen_120_);
lean_ctor_set(v_reuseFailAlloc_138_, 8, v_infoState_121_);
lean_ctor_set(v_reuseFailAlloc_138_, 9, v_traceState_122_);
lean_ctor_set(v_reuseFailAlloc_138_, 10, v_snapshotTasks_123_);
v___x_132_ = v_reuseFailAlloc_138_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = lean_st_ref_set(v___y_102_, v___x_132_);
v___x_134_ = lean_box(0);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 0, v___x_134_);
v___x_136_ = v___x_108_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
else
{
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_148_; 
lean_dec(v_a_104_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_99_);
lean_dec_ref(v___y_97_);
v_a_141_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_148_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_148_ == 0)
{
v___x_143_ = v___x_105_;
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_105_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_148_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_146_; 
if (v_isShared_144_ == 0)
{
v___x_146_ = v___x_143_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_a_141_);
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
else
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec(v___y_101_);
lean_dec_ref(v___y_99_);
lean_dec_ref(v___y_97_);
v_a_149_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_103_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_103_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
v___jp_157_:
{
lean_object* v_fileName_163_; lean_object* v_fileMap_164_; uint8_t v_suppressElabErrors_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_184_; 
v_fileName_163_ = lean_ctor_get(v___y_91_, 0);
v_fileMap_164_ = lean_ctor_get(v___y_91_, 1);
v_suppressElabErrors_165_ = lean_ctor_get_uint8(v___y_91_, sizeof(void*)*10);
v___x_166_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_88_);
v___x_167_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v___x_166_, v___y_92_);
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_184_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_184_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_184_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
lean_inc_ref_n(v_fileMap_164_, 2);
v___x_172_ = l_Lean_FileMap_toPosition(v_fileMap_164_, v___y_161_);
lean_dec(v___y_161_);
v___x_173_ = l_Lean_FileMap_toPosition(v_fileMap_164_, v___y_162_);
lean_dec(v___y_162_);
v___x_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
v___x_175_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___closed__0));
if (v_suppressElabErrors_165_ == 0)
{
lean_del_object(v___x_170_);
v___y_95_ = v___y_160_;
v___y_96_ = v___y_159_;
v___y_97_ = v___x_172_;
v___y_98_ = v_fileName_163_;
v___y_99_ = v_a_168_;
v___y_100_ = v___x_175_;
v___y_101_ = v___x_174_;
v___y_102_ = v___y_92_;
goto v___jp_94_;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___f_178_; uint8_t v___x_179_; 
v___x_176_ = lean_box(v___y_158_);
v___x_177_ = lean_box(v_suppressElabErrors_165_);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___lam__0___boxed), 3, 2);
lean_closure_set(v___f_178_, 0, v___x_176_);
lean_closure_set(v___f_178_, 1, v___x_177_);
lean_inc(v_a_168_);
v___x_179_ = l_Lean_MessageData_hasTag(v___f_178_, v_a_168_);
if (v___x_179_ == 0)
{
lean_object* v___x_180_; lean_object* v___x_182_; 
lean_dec_ref(v___x_174_);
lean_dec_ref(v___x_172_);
lean_dec(v_a_168_);
v___x_180_ = lean_box(0);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_180_);
v___x_182_ = v___x_170_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
else
{
lean_del_object(v___x_170_);
v___y_95_ = v___y_160_;
v___y_96_ = v___y_159_;
v___y_97_ = v___x_172_;
v___y_98_ = v_fileName_163_;
v___y_99_ = v_a_168_;
v___y_100_ = v___x_175_;
v___y_101_ = v___x_174_;
v___y_102_ = v___y_92_;
goto v___jp_94_;
}
}
}
}
v___jp_185_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Syntax_getTailPos_x3f(v___y_189_, v___y_188_);
lean_dec(v___y_189_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_inc(v___y_190_);
v___y_158_ = v___y_186_;
v___y_159_ = v___y_188_;
v___y_160_ = v___y_187_;
v___y_161_ = v___y_190_;
v___y_162_ = v___y_190_;
goto v___jp_157_;
}
else
{
lean_object* v_val_192_; 
v_val_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_val_192_);
lean_dec_ref(v___x_191_);
v___y_158_ = v___y_186_;
v___y_159_ = v___y_188_;
v___y_160_ = v___y_187_;
v___y_161_ = v___y_190_;
v___y_162_ = v_val_192_;
goto v___jp_157_;
}
}
v___jp_193_:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Elab_Command_getRef___redArg(v___y_91_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v_ref_199_; lean_object* v___x_200_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v___x_197_);
v_ref_199_ = l_Lean_replaceRef(v_ref_87_, v_a_198_);
lean_dec(v_a_198_);
v___x_200_ = l_Lean_Syntax_getPos_x3f(v_ref_199_, v___y_195_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___y_186_ = v___y_194_;
v___y_187_ = v___y_196_;
v___y_188_ = v___y_195_;
v___y_189_ = v_ref_199_;
v___y_190_ = v___x_201_;
goto v___jp_185_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_202_);
lean_dec_ref(v___x_200_);
v___y_186_ = v___y_194_;
v___y_187_ = v___y_196_;
v___y_188_ = v___y_195_;
v___y_189_ = v_ref_199_;
v___y_190_ = v_val_202_;
goto v___jp_185_;
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v_msgData_88_);
v_a_203_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_210_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_210_ == 0)
{
v___x_205_ = v___x_197_;
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_a_203_);
lean_dec(v___x_197_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_210_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_208_; 
if (v_isShared_206_ == 0)
{
v___x_208_ = v___x_205_;
goto v_reusejp_207_;
}
else
{
lean_object* v_reuseFailAlloc_209_; 
v_reuseFailAlloc_209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_209_, 0, v_a_203_);
v___x_208_ = v_reuseFailAlloc_209_;
goto v_reusejp_207_;
}
v_reusejp_207_:
{
return v___x_208_;
}
}
}
}
v___jp_212_:
{
if (v___y_215_ == 0)
{
v___y_194_ = v___y_213_;
v___y_195_ = v___y_214_;
v___y_196_ = v_severity_89_;
goto v___jp_193_;
}
else
{
v___y_194_ = v___y_213_;
v___y_195_ = v___y_214_;
v___y_196_ = v___x_211_;
goto v___jp_193_;
}
}
v___jp_216_:
{
if (v___y_217_ == 0)
{
lean_object* v___x_218_; lean_object* v_scopes_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_opts_222_; uint8_t v___x_223_; uint8_t v___x_224_; 
v___x_218_ = lean_st_ref_get(v___y_92_);
v_scopes_219_ = lean_ctor_get(v___x_218_, 2);
lean_inc(v_scopes_219_);
lean_dec(v___x_218_);
v___x_220_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_221_ = l_List_head_x21___redArg(v___x_220_, v_scopes_219_);
lean_dec(v_scopes_219_);
v_opts_222_ = lean_ctor_get(v___x_221_, 1);
lean_inc_ref(v_opts_222_);
lean_dec(v___x_221_);
v___x_223_ = 1;
v___x_224_ = l_Lean_instBEqMessageSeverity_beq(v_severity_89_, v___x_223_);
if (v___x_224_ == 0)
{
lean_dec_ref(v_opts_222_);
v___y_213_ = v___y_217_;
v___y_214_ = v___y_217_;
v___y_215_ = v___x_224_;
goto v___jp_212_;
}
else
{
lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_225_ = l_Lean_warningAsError;
v___x_226_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__3(v_opts_222_, v___x_225_);
lean_dec_ref(v_opts_222_);
v___y_213_ = v___y_217_;
v___y_214_ = v___y_217_;
v___y_215_ = v___x_226_;
goto v___jp_212_;
}
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec_ref(v_msgData_88_);
v___x_227_ = lean_box(0);
v___x_228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_228_, 0, v___x_227_);
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___boxed(lean_object* v_ref_231_, lean_object* v_msgData_232_, lean_object* v_severity_233_, lean_object* v_isSilent_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_){
_start:
{
uint8_t v_severity_boxed_238_; uint8_t v_isSilent_boxed_239_; lean_object* v_res_240_; 
v_severity_boxed_238_ = lean_unbox(v_severity_233_);
v_isSilent_boxed_239_ = lean_unbox(v_isSilent_234_);
v_res_240_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_ref_231_, v_msgData_232_, v_severity_boxed_238_, v_isSilent_boxed_239_, v___y_235_, v___y_236_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
lean_dec(v_ref_231_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(lean_object* v_ref_241_, lean_object* v_msgData_242_, lean_object* v___y_243_, lean_object* v___y_244_){
_start:
{
uint8_t v___x_246_; uint8_t v___x_247_; lean_object* v___x_248_; 
v___x_246_ = 0;
v___x_247_ = 0;
v___x_248_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_ref_241_, v_msgData_242_, v___x_246_, v___x_247_, v___y_243_, v___y_244_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1___boxed(lean_object* v_ref_249_, lean_object* v_msgData_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_ref_249_, v_msgData_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v_ref_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(lean_object* v_tk_258_, lean_object* v_as_259_, size_t v_sz_260_, size_t v_i_261_, lean_object* v_b_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v___x_266_; 
v___x_266_ = lean_usize_dec_lt(v_i_261_, v_sz_260_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
v___x_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_267_, 0, v_b_262_);
return v___x_267_;
}
else
{
lean_object* v_a_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec_ref(v_b_262_);
v_a_268_ = lean_array_uget_borrowed(v_as_259_, v_i_261_);
v___x_269_ = lean_box(0);
lean_inc(v_a_268_);
v___x_270_ = l_Lean_Elab_InfoTree_format(v_a_268_, v___x_269_);
if (lean_obj_tag(v___x_270_) == 0)
{
lean_object* v_a_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_a_271_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v___x_270_);
v___x_272_ = l_Lean_MessageData_ofFormat(v_a_271_);
v___x_273_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_258_, v___x_272_, v___y_263_, v___y_264_);
if (lean_obj_tag(v___x_273_) == 0)
{
lean_object* v___x_274_; size_t v___x_275_; size_t v___x_276_; 
lean_dec_ref(v___x_273_);
v___x_274_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0));
v___x_275_ = ((size_t)1ULL);
v___x_276_ = lean_usize_add(v_i_261_, v___x_275_);
v_i_261_ = v___x_276_;
v_b_262_ = v___x_274_;
goto _start;
}
else
{
lean_object* v_a_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_285_; 
v_a_278_ = lean_ctor_get(v___x_273_, 0);
v_isSharedCheck_285_ = !lean_is_exclusive(v___x_273_);
if (v_isSharedCheck_285_ == 0)
{
v___x_280_ = v___x_273_;
v_isShared_281_ = v_isSharedCheck_285_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_a_278_);
lean_dec(v___x_273_);
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
else
{
lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_298_; 
v_a_286_ = lean_ctor_get(v___x_270_, 0);
v_isSharedCheck_298_ = !lean_is_exclusive(v___x_270_);
if (v_isSharedCheck_298_ == 0)
{
v___x_288_ = v___x_270_;
v_isShared_289_ = v_isSharedCheck_298_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_dec(v___x_270_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_298_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v_ref_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
v_ref_290_ = lean_ctor_get(v___y_263_, 7);
v___x_291_ = lean_io_error_to_string(v_a_286_);
v___x_292_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = l_Lean_MessageData_ofFormat(v___x_292_);
lean_inc(v_ref_290_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_ref_290_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 0, v___x_294_);
v___x_296_ = v___x_288_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_294_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___boxed(lean_object* v_tk_299_, lean_object* v_as_300_, lean_object* v_sz_301_, lean_object* v_i_302_, lean_object* v_b_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
size_t v_sz_boxed_307_; size_t v_i_boxed_308_; lean_object* v_res_309_; 
v_sz_boxed_307_ = lean_unbox_usize(v_sz_301_);
lean_dec(v_sz_301_);
v_i_boxed_308_ = lean_unbox_usize(v_i_302_);
lean_dec(v_i_302_);
v_res_309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(v_tk_299_, v_as_300_, v_sz_boxed_307_, v_i_boxed_308_, v_b_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec_ref(v_as_300_);
lean_dec(v_tk_299_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(lean_object* v_tk_310_, lean_object* v_as_311_, size_t v_sz_312_, size_t v_i_313_, lean_object* v_b_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
uint8_t v___x_318_; 
v___x_318_ = lean_usize_dec_lt(v_i_313_, v_sz_312_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; 
v___x_319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_319_, 0, v_b_314_);
return v___x_319_;
}
else
{
lean_object* v_a_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec_ref(v_b_314_);
v_a_320_ = lean_array_uget_borrowed(v_as_311_, v_i_313_);
v___x_321_ = lean_box(0);
lean_inc(v_a_320_);
v___x_322_ = l_Lean_Elab_InfoTree_format(v_a_320_, v___x_321_);
if (lean_obj_tag(v___x_322_) == 0)
{
lean_object* v_a_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v_a_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_a_323_);
lean_dec_ref(v___x_322_);
v___x_324_ = l_Lean_MessageData_ofFormat(v_a_323_);
v___x_325_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_310_, v___x_324_, v___y_315_, v___y_316_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v___x_326_; size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
lean_dec_ref(v___x_325_);
v___x_326_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9___closed__0));
v___x_327_ = ((size_t)1ULL);
v___x_328_ = lean_usize_add(v_i_313_, v___x_327_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4_spec__9(v_tk_310_, v_as_311_, v_sz_312_, v___x_328_, v___x_326_, v___y_315_, v___y_316_);
return v___x_329_;
}
else
{
lean_object* v_a_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_337_; 
v_a_330_ = lean_ctor_get(v___x_325_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v___x_325_);
if (v_isSharedCheck_337_ == 0)
{
v___x_332_ = v___x_325_;
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_a_330_);
lean_dec(v___x_325_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_337_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_335_; 
if (v_isShared_333_ == 0)
{
v___x_335_ = v___x_332_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_a_330_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
return v___x_335_;
}
}
}
}
else
{
lean_object* v_a_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_350_; 
v_a_338_ = lean_ctor_get(v___x_322_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_322_);
if (v_isSharedCheck_350_ == 0)
{
v___x_340_ = v___x_322_;
v_isShared_341_ = v_isSharedCheck_350_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_a_338_);
lean_dec(v___x_322_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_350_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v_ref_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v_ref_342_ = lean_ctor_get(v___y_315_, 7);
v___x_343_ = lean_io_error_to_string(v_a_338_);
v___x_344_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
v___x_345_ = l_Lean_MessageData_ofFormat(v___x_344_);
lean_inc(v_ref_342_);
v___x_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_346_, 0, v_ref_342_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_346_);
v___x_348_ = v___x_340_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4___boxed(lean_object* v_tk_351_, lean_object* v_as_352_, lean_object* v_sz_353_, lean_object* v_i_354_, lean_object* v_b_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
size_t v_sz_boxed_359_; size_t v_i_boxed_360_; lean_object* v_res_361_; 
v_sz_boxed_359_ = lean_unbox_usize(v_sz_353_);
lean_dec(v_sz_353_);
v_i_boxed_360_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_res_361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(v_tk_351_, v_as_352_, v_sz_boxed_359_, v_i_boxed_360_, v_b_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec_ref(v_as_352_);
lean_dec(v_tk_351_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(lean_object* v_tk_365_, lean_object* v_as_366_, size_t v_sz_367_, size_t v_i_368_, lean_object* v_b_369_, lean_object* v___y_370_, lean_object* v___y_371_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = lean_usize_dec_lt(v_i_368_, v_sz_367_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
v___x_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_374_, 0, v_b_369_);
return v___x_374_;
}
else
{
lean_object* v_a_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec_ref(v_b_369_);
v_a_375_ = lean_array_uget_borrowed(v_as_366_, v_i_368_);
v___x_376_ = lean_box(0);
lean_inc(v_a_375_);
v___x_377_ = l_Lean_Elab_InfoTree_format(v_a_375_, v___x_376_);
if (lean_obj_tag(v___x_377_) == 0)
{
lean_object* v_a_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_a_378_ = lean_ctor_get(v___x_377_, 0);
lean_inc(v_a_378_);
lean_dec_ref(v___x_377_);
v___x_379_ = l_Lean_MessageData_ofFormat(v_a_378_);
v___x_380_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_365_, v___x_379_, v___y_370_, v___y_371_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v___x_381_; size_t v___x_382_; size_t v___x_383_; 
lean_dec_ref(v___x_380_);
v___x_381_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0));
v___x_382_ = ((size_t)1ULL);
v___x_383_ = lean_usize_add(v_i_368_, v___x_382_);
v_i_368_ = v___x_383_;
v_b_369_ = v___x_381_;
goto _start;
}
else
{
lean_object* v_a_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_392_; 
v_a_385_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_392_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_392_ == 0)
{
v___x_387_ = v___x_380_;
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_a_385_);
lean_dec(v___x_380_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_392_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_390_; 
if (v_isShared_388_ == 0)
{
v___x_390_ = v___x_387_;
goto v_reusejp_389_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
v___x_390_ = v_reuseFailAlloc_391_;
goto v_reusejp_389_;
}
v_reusejp_389_:
{
return v___x_390_;
}
}
}
}
else
{
lean_object* v_a_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_405_; 
v_a_393_ = lean_ctor_get(v___x_377_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_377_);
if (v_isSharedCheck_405_ == 0)
{
v___x_395_ = v___x_377_;
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_a_393_);
lean_dec(v___x_377_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v_ref_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v_ref_397_ = lean_ctor_get(v___y_370_, 7);
v___x_398_ = lean_io_error_to_string(v_a_393_);
v___x_399_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_399_, 0, v___x_398_);
v___x_400_ = l_Lean_MessageData_ofFormat(v___x_399_);
lean_inc(v_ref_397_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v_ref_397_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 0, v___x_401_);
v___x_403_ = v___x_395_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___boxed(lean_object* v_tk_406_, lean_object* v_as_407_, lean_object* v_sz_408_, lean_object* v_i_409_, lean_object* v_b_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_){
_start:
{
size_t v_sz_boxed_414_; size_t v_i_boxed_415_; lean_object* v_res_416_; 
v_sz_boxed_414_ = lean_unbox_usize(v_sz_408_);
lean_dec(v_sz_408_);
v_i_boxed_415_ = lean_unbox_usize(v_i_409_);
lean_dec(v_i_409_);
v_res_416_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(v_tk_406_, v_as_407_, v_sz_boxed_414_, v_i_boxed_415_, v_b_410_, v___y_411_, v___y_412_);
lean_dec(v___y_412_);
lean_dec_ref(v___y_411_);
lean_dec_ref(v_as_407_);
lean_dec(v_tk_406_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(lean_object* v_tk_417_, lean_object* v_as_418_, size_t v_sz_419_, size_t v_i_420_, lean_object* v_b_421_, lean_object* v___y_422_, lean_object* v___y_423_){
_start:
{
uint8_t v___x_425_; 
v___x_425_ = lean_usize_dec_lt(v_i_420_, v_sz_419_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v_b_421_);
return v___x_426_;
}
else
{
lean_object* v_a_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
lean_dec_ref(v_b_421_);
v_a_427_ = lean_array_uget_borrowed(v_as_418_, v_i_420_);
v___x_428_ = lean_box(0);
lean_inc(v_a_427_);
v___x_429_ = l_Lean_Elab_InfoTree_format(v_a_427_, v___x_428_);
if (lean_obj_tag(v___x_429_) == 0)
{
lean_object* v_a_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v_a_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_a_430_);
lean_dec_ref(v___x_429_);
v___x_431_ = l_Lean_MessageData_ofFormat(v_a_430_);
v___x_432_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_tk_417_, v___x_431_, v___y_422_, v___y_423_);
if (lean_obj_tag(v___x_432_) == 0)
{
lean_object* v___x_433_; size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
lean_dec_ref(v___x_432_);
v___x_433_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9___closed__0));
v___x_434_ = ((size_t)1ULL);
v___x_435_ = lean_usize_add(v_i_420_, v___x_434_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7_spec__9(v_tk_417_, v_as_418_, v_sz_419_, v___x_435_, v___x_433_, v___y_422_, v___y_423_);
return v___x_436_;
}
else
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_444_; 
v_a_437_ = lean_ctor_get(v___x_432_, 0);
v_isSharedCheck_444_ = !lean_is_exclusive(v___x_432_);
if (v_isSharedCheck_444_ == 0)
{
v___x_439_ = v___x_432_;
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_432_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_444_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_442_; 
if (v_isShared_440_ == 0)
{
v___x_442_ = v___x_439_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_a_437_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
return v___x_442_;
}
}
}
}
else
{
lean_object* v_a_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_457_; 
v_a_445_ = lean_ctor_get(v___x_429_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v___x_429_);
if (v_isSharedCheck_457_ == 0)
{
v___x_447_ = v___x_429_;
v_isShared_448_ = v_isSharedCheck_457_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_a_445_);
lean_dec(v___x_429_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_457_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_ref_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v_ref_449_ = lean_ctor_get(v___y_422_, 7);
v___x_450_ = lean_io_error_to_string(v_a_445_);
v___x_451_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
v___x_452_ = l_Lean_MessageData_ofFormat(v___x_451_);
lean_inc(v_ref_449_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_ref_449_);
lean_ctor_set(v___x_453_, 1, v___x_452_);
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_453_);
v___x_455_ = v___x_447_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v___x_453_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7___boxed(lean_object* v_tk_458_, lean_object* v_as_459_, lean_object* v_sz_460_, lean_object* v_i_461_, lean_object* v_b_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
size_t v_sz_boxed_466_; size_t v_i_boxed_467_; lean_object* v_res_468_; 
v_sz_boxed_466_ = lean_unbox_usize(v_sz_460_);
lean_dec(v_sz_460_);
v_i_boxed_467_ = lean_unbox_usize(v_i_461_);
lean_dec(v_i_461_);
v_res_468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(v_tk_458_, v_as_459_, v_sz_boxed_466_, v_i_boxed_467_, v_b_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec_ref(v_as_459_);
lean_dec(v_tk_458_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(lean_object* v_init_469_, lean_object* v_tk_470_, lean_object* v_n_471_, lean_object* v_b_472_, lean_object* v___y_473_, lean_object* v___y_474_){
_start:
{
if (lean_obj_tag(v_n_471_) == 0)
{
lean_object* v_cs_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_510_; 
v_cs_476_ = lean_ctor_get(v_n_471_, 0);
v_isSharedCheck_510_ = !lean_is_exclusive(v_n_471_);
if (v_isSharedCheck_510_ == 0)
{
v___x_478_ = v_n_471_;
v_isShared_479_ = v_isSharedCheck_510_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_cs_476_);
lean_dec(v_n_471_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_510_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_481_; size_t v_sz_482_; size_t v___x_483_; lean_object* v___x_484_; 
v___x_480_ = lean_box(0);
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v_b_472_);
v_sz_482_ = lean_array_size(v_cs_476_);
v___x_483_ = ((size_t)0ULL);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(v_init_469_, v_tk_470_, v_cs_476_, v_sz_482_, v___x_483_, v___x_481_, v___y_473_, v___y_474_);
lean_dec_ref(v_cs_476_);
if (lean_obj_tag(v___x_484_) == 0)
{
lean_object* v_a_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_501_; 
v_a_485_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_501_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_501_ == 0)
{
v___x_487_ = v___x_484_;
v_isShared_488_ = v_isSharedCheck_501_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_a_485_);
lean_dec(v___x_484_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_501_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v_fst_489_; 
v_fst_489_ = lean_ctor_get(v_a_485_, 0);
if (lean_obj_tag(v_fst_489_) == 0)
{
lean_object* v_snd_490_; lean_object* v___x_492_; 
v_snd_490_ = lean_ctor_get(v_a_485_, 1);
lean_inc(v_snd_490_);
lean_dec(v_a_485_);
if (v_isShared_479_ == 0)
{
lean_ctor_set_tag(v___x_478_, 1);
lean_ctor_set(v___x_478_, 0, v_snd_490_);
v___x_492_ = v___x_478_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_snd_490_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_494_; 
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v___x_492_);
v___x_494_ = v___x_487_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
}
else
{
lean_object* v_val_497_; lean_object* v___x_499_; 
lean_inc_ref(v_fst_489_);
lean_dec(v_a_485_);
lean_del_object(v___x_478_);
v_val_497_ = lean_ctor_get(v_fst_489_, 0);
lean_inc(v_val_497_);
lean_dec_ref(v_fst_489_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 0, v_val_497_);
v___x_499_ = v___x_487_;
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
lean_del_object(v___x_478_);
v_a_502_ = lean_ctor_get(v___x_484_, 0);
v_isSharedCheck_509_ = !lean_is_exclusive(v___x_484_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___x_484_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_dec(v___x_484_);
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
}
else
{
lean_object* v_vs_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_545_; 
v_vs_511_ = lean_ctor_get(v_n_471_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v_n_471_);
if (v_isSharedCheck_545_ == 0)
{
v___x_513_ = v_n_471_;
v_isShared_514_ = v_isSharedCheck_545_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_vs_511_);
lean_dec(v_n_471_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_545_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v___x_515_; lean_object* v___x_516_; size_t v_sz_517_; size_t v___x_518_; lean_object* v___x_519_; 
v___x_515_ = lean_box(0);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v_b_472_);
v_sz_517_ = lean_array_size(v_vs_511_);
v___x_518_ = ((size_t)0ULL);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__7(v_tk_470_, v_vs_511_, v_sz_517_, v___x_518_, v___x_516_, v___y_473_, v___y_474_);
lean_dec_ref(v_vs_511_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_536_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_536_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_536_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_536_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v_fst_524_; 
v_fst_524_ = lean_ctor_get(v_a_520_, 0);
if (lean_obj_tag(v_fst_524_) == 0)
{
lean_object* v_snd_525_; lean_object* v___x_527_; 
v_snd_525_ = lean_ctor_get(v_a_520_, 1);
lean_inc(v_snd_525_);
lean_dec(v_a_520_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v_snd_525_);
v___x_527_ = v___x_513_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v_snd_525_);
v___x_527_ = v_reuseFailAlloc_531_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_529_; 
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v___x_527_);
v___x_529_ = v___x_522_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
return v___x_529_;
}
}
}
else
{
lean_object* v_val_532_; lean_object* v___x_534_; 
lean_inc_ref(v_fst_524_);
lean_dec(v_a_520_);
lean_del_object(v___x_513_);
v_val_532_ = lean_ctor_get(v_fst_524_, 0);
lean_inc(v_val_532_);
lean_dec_ref(v_fst_524_);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 0, v_val_532_);
v___x_534_ = v___x_522_;
goto v_reusejp_533_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v_val_532_);
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
else
{
lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_544_; 
lean_del_object(v___x_513_);
v_a_537_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_544_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_544_ == 0)
{
v___x_539_ = v___x_519_;
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_519_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_544_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v_a_537_);
v___x_542_ = v_reuseFailAlloc_543_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
return v___x_542_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(lean_object* v_init_546_, lean_object* v_tk_547_, lean_object* v_as_548_, size_t v_sz_549_, size_t v_i_550_, lean_object* v_b_551_, lean_object* v___y_552_, lean_object* v___y_553_){
_start:
{
uint8_t v___x_555_; 
v___x_555_ = lean_usize_dec_lt(v_i_550_, v_sz_549_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; 
v___x_556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_556_, 0, v_b_551_);
return v___x_556_;
}
else
{
lean_object* v_snd_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_591_; 
v_snd_557_ = lean_ctor_get(v_b_551_, 1);
v_isSharedCheck_591_ = !lean_is_exclusive(v_b_551_);
if (v_isSharedCheck_591_ == 0)
{
lean_object* v_unused_592_; 
v_unused_592_ = lean_ctor_get(v_b_551_, 0);
lean_dec(v_unused_592_);
v___x_559_ = v_b_551_;
v_isShared_560_ = v_isSharedCheck_591_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_snd_557_);
lean_dec(v_b_551_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_591_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_a_561_; lean_object* v___x_562_; 
v_a_561_ = lean_array_uget_borrowed(v_as_548_, v_i_550_);
lean_inc(v_snd_557_);
lean_inc(v_a_561_);
v___x_562_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_546_, v_tk_547_, v_a_561_, v_snd_557_, v___y_552_, v___y_553_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_582_; 
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_582_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_582_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_582_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_582_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
if (lean_obj_tag(v_a_563_) == 0)
{
lean_object* v___x_567_; lean_object* v___x_569_; 
v___x_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_567_, 0, v_a_563_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_567_);
v___x_569_ = v___x_559_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_snd_557_);
v___x_569_ = v_reuseFailAlloc_573_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
lean_object* v___x_571_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_569_);
v___x_571_ = v___x_565_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___x_569_);
v___x_571_ = v_reuseFailAlloc_572_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
return v___x_571_;
}
}
}
else
{
lean_object* v_a_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
lean_del_object(v___x_565_);
lean_dec(v_snd_557_);
v_a_574_ = lean_ctor_get(v_a_563_, 0);
lean_inc(v_a_574_);
lean_dec_ref(v_a_563_);
v___x_575_ = lean_box(0);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v_a_574_);
lean_ctor_set(v___x_559_, 0, v___x_575_);
v___x_577_ = v___x_559_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___x_575_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_a_574_);
v___x_577_ = v_reuseFailAlloc_581_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
size_t v___x_578_; size_t v___x_579_; 
v___x_578_ = ((size_t)1ULL);
v___x_579_ = lean_usize_add(v_i_550_, v___x_578_);
v_i_550_ = v___x_579_;
v_b_551_ = v___x_577_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_590_; 
lean_del_object(v___x_559_);
lean_dec(v_snd_557_);
v_a_583_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_590_ == 0)
{
v___x_585_ = v___x_562_;
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_a_583_);
lean_dec(v___x_562_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_590_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_588_; 
if (v_isShared_586_ == 0)
{
v___x_588_ = v___x_585_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6___boxed(lean_object* v_init_593_, lean_object* v_tk_594_, lean_object* v_as_595_, lean_object* v_sz_596_, lean_object* v_i_597_, lean_object* v_b_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
size_t v_sz_boxed_602_; size_t v_i_boxed_603_; lean_object* v_res_604_; 
v_sz_boxed_602_ = lean_unbox_usize(v_sz_596_);
lean_dec(v_sz_596_);
v_i_boxed_603_ = lean_unbox_usize(v_i_597_);
lean_dec(v_i_597_);
v_res_604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__6(v_init_593_, v_tk_594_, v_as_595_, v_sz_boxed_602_, v_i_boxed_603_, v_b_598_, v___y_599_, v___y_600_);
lean_dec(v___y_600_);
lean_dec_ref(v___y_599_);
lean_dec_ref(v_as_595_);
lean_dec(v_tk_594_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___boxed(lean_object* v_init_605_, lean_object* v_tk_606_, lean_object* v_n_607_, lean_object* v_b_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_605_, v_tk_606_, v_n_607_, v_b_608_, v___y_609_, v___y_610_);
lean_dec(v___y_610_);
lean_dec_ref(v___y_609_);
lean_dec(v_tk_606_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(lean_object* v_tk_613_, lean_object* v_t_614_, lean_object* v_init_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_root_619_; lean_object* v_tail_620_; lean_object* v___x_621_; 
v_root_619_ = lean_ctor_get(v_t_614_, 0);
lean_inc_ref(v_root_619_);
v_tail_620_ = lean_ctor_get(v_t_614_, 1);
lean_inc_ref(v_tail_620_);
lean_dec_ref(v_t_614_);
v___x_621_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_init_615_, v_tk_613_, v_root_619_, v_init_615_, v___y_616_, v___y_617_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v_a_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_658_; 
v_a_622_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_658_ == 0)
{
v___x_624_ = v___x_621_;
v_isShared_625_ = v_isSharedCheck_658_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_a_622_);
lean_dec(v___x_621_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_658_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
if (lean_obj_tag(v_a_622_) == 0)
{
lean_object* v_a_626_; lean_object* v___x_628_; 
lean_dec_ref(v_tail_620_);
v_a_626_ = lean_ctor_get(v_a_622_, 0);
lean_inc(v_a_626_);
lean_dec_ref(v_a_622_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v_a_626_);
v___x_628_ = v___x_624_;
goto v_reusejp_627_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_626_);
v___x_628_ = v_reuseFailAlloc_629_;
goto v_reusejp_627_;
}
v_reusejp_627_:
{
return v___x_628_;
}
}
else
{
lean_object* v_a_630_; lean_object* v___x_631_; lean_object* v___x_632_; size_t v_sz_633_; size_t v___x_634_; lean_object* v___x_635_; 
lean_del_object(v___x_624_);
v_a_630_ = lean_ctor_get(v_a_622_, 0);
lean_inc(v_a_630_);
lean_dec_ref(v_a_622_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v_a_630_);
v_sz_633_ = lean_array_size(v_tail_620_);
v___x_634_ = ((size_t)0ULL);
v___x_635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__4(v_tk_613_, v_tail_620_, v_sz_633_, v___x_634_, v___x_632_, v___y_616_, v___y_617_);
lean_dec_ref(v_tail_620_);
if (lean_obj_tag(v___x_635_) == 0)
{
lean_object* v_a_636_; lean_object* v___x_638_; uint8_t v_isShared_639_; uint8_t v_isSharedCheck_649_; 
v_a_636_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_649_ == 0)
{
v___x_638_ = v___x_635_;
v_isShared_639_ = v_isSharedCheck_649_;
goto v_resetjp_637_;
}
else
{
lean_inc(v_a_636_);
lean_dec(v___x_635_);
v___x_638_ = lean_box(0);
v_isShared_639_ = v_isSharedCheck_649_;
goto v_resetjp_637_;
}
v_resetjp_637_:
{
lean_object* v_fst_640_; 
v_fst_640_ = lean_ctor_get(v_a_636_, 0);
if (lean_obj_tag(v_fst_640_) == 0)
{
lean_object* v_snd_641_; lean_object* v___x_643_; 
v_snd_641_ = lean_ctor_get(v_a_636_, 1);
lean_inc(v_snd_641_);
lean_dec(v_a_636_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v_snd_641_);
v___x_643_ = v___x_638_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_snd_641_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
else
{
lean_object* v_val_645_; lean_object* v___x_647_; 
lean_inc_ref(v_fst_640_);
lean_dec(v_a_636_);
v_val_645_ = lean_ctor_get(v_fst_640_, 0);
lean_inc(v_val_645_);
lean_dec_ref(v_fst_640_);
if (v_isShared_639_ == 0)
{
lean_ctor_set(v___x_638_, 0, v_val_645_);
v___x_647_ = v___x_638_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_val_645_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
v_a_650_ = lean_ctor_get(v___x_635_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_635_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_635_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
lean_dec_ref(v_tail_620_);
v_a_659_ = lean_ctor_get(v___x_621_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_621_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_621_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2___boxed(lean_object* v_tk_667_, lean_object* v_t_668_, lean_object* v_init_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_667_, v_t_668_, v_init_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v_tk_667_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(lean_object* v_msgData_674_, uint8_t v_severity_675_, uint8_t v_isSilent_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Lean_Elab_Command_getRef___redArg(v___y_677_);
if (lean_obj_tag(v___x_680_) == 0)
{
lean_object* v_a_681_; lean_object* v___x_682_; 
v_a_681_ = lean_ctor_get(v___x_680_, 0);
lean_inc(v_a_681_);
lean_dec_ref(v___x_680_);
v___x_682_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_a_681_, v_msgData_674_, v_severity_675_, v_isSilent_676_, v___y_677_, v___y_678_);
lean_dec(v_a_681_);
return v___x_682_;
}
else
{
lean_object* v_a_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_690_; 
lean_dec_ref(v_msgData_674_);
v_a_683_ = lean_ctor_get(v___x_680_, 0);
v_isSharedCheck_690_ = !lean_is_exclusive(v___x_680_);
if (v_isSharedCheck_690_ == 0)
{
v___x_685_ = v___x_680_;
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_a_683_);
lean_dec(v___x_680_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_690_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_688_; 
if (v_isShared_686_ == 0)
{
v___x_688_ = v___x_685_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v_a_683_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6___boxed(lean_object* v_msgData_691_, lean_object* v_severity_692_, lean_object* v_isSilent_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
uint8_t v_severity_boxed_697_; uint8_t v_isSilent_boxed_698_; lean_object* v_res_699_; 
v_severity_boxed_697_ = lean_unbox(v_severity_692_);
v_isSilent_boxed_698_ = lean_unbox(v_isSilent_693_);
v_res_699_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_msgData_691_, v_severity_boxed_697_, v_isSilent_boxed_698_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object* v_msgData_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v___x_704_; uint8_t v___x_705_; lean_object* v___x_706_; 
v___x_704_ = 2;
v___x_705_ = 0;
v___x_706_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_msgData_700_, v___x_704_, v___x_705_, v___y_701_, v___y_702_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3___boxed(lean_object* v_msgData_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v_msgData_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
return v_res_711_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4));
v___x_721_ = l_Lean_MessageData_ofFormat(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(lean_object* v_x_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_726_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
lean_inc(v_x_722_);
v___x_727_ = l_Lean_Syntax_isOfKind(v_x_722_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___x_728_; 
lean_dec(v_x_722_);
v___x_728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
return v___x_728_;
}
else
{
lean_object* v___x_729_; lean_object* v_infoState_730_; uint8_t v_enabled_731_; lean_object* v___x_732_; lean_object* v_tk_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_729_ = lean_st_ref_get(v_a_724_);
v_infoState_730_ = lean_ctor_get(v___x_729_, 8);
lean_inc_ref(v_infoState_730_);
lean_dec(v___x_729_);
v_enabled_731_ = lean_ctor_get_uint8(v_infoState_730_, sizeof(void*)*3);
lean_dec_ref(v_infoState_730_);
v___x_732_ = lean_unsigned_to_nat(0u);
v_tk_733_ = l_Lean_Syntax_getArg(v_x_722_, v___x_732_);
v___x_734_ = lean_unsigned_to_nat(2u);
v___x_735_ = l_Lean_Syntax_getArg(v_x_722_, v___x_734_);
lean_dec(v_x_722_);
if (v_enabled_731_ == 0)
{
if (v___x_727_ == 0)
{
goto v___jp_736_;
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec(v___x_735_);
lean_dec(v_tk_733_);
v___x_753_ = lean_obj_once(&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5, &l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5_once, _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5);
v___x_754_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v___x_753_, v_a_723_, v_a_724_);
return v___x_754_;
}
}
else
{
goto v___jp_736_;
}
v___jp_736_:
{
lean_object* v___x_737_; 
v___x_737_ = l_Lean_Elab_Command_elabCommand(v___x_735_, v_a_723_, v_a_724_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_object* v___x_738_; lean_object* v_infoState_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v_trees_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec_ref(v___x_737_);
v___x_738_ = lean_st_ref_get(v_a_724_);
v_infoState_739_ = lean_ctor_get(v___x_738_, 8);
lean_inc_ref(v_infoState_739_);
lean_dec(v___x_738_);
v___x_740_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_739_);
v___x_741_ = lean_task_get_own(v___x_740_);
v_trees_742_ = lean_ctor_get(v___x_741_, 2);
lean_inc_ref(v_trees_742_);
lean_dec(v___x_741_);
v___x_743_ = lean_box(0);
v___x_744_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_733_, v_trees_742_, v___x_743_, v_a_723_, v_a_724_);
lean_dec(v_tk_733_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_751_ == 0)
{
lean_object* v_unused_752_; 
v_unused_752_ = lean_ctor_get(v___x_744_, 0);
lean_dec(v_unused_752_);
v___x_746_ = v___x_744_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_dec(v___x_744_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_743_);
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_743_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
else
{
return v___x_744_;
}
}
else
{
lean_dec(v_tk_733_);
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed(lean_object* v_x_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(v_x_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(lean_object* v_msgData_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___redArg(v_msgData_760_, v___y_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2___boxed(lean_object* v_msgData_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1_spec__2(v_msgData_765_, v___y_766_, v___y_767_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1(){
_start:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_781_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_782_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
v___x_783_ = ((lean_object*)(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4));
v___x_784_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed), 4, 0);
v___x_785_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_781_, v___x_782_, v___x_783_, v___x_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___boxed(lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
return v_res_787_;
}
}
lean_object* runtime_initialize_Lean_Elab_Command(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_InfoTrees(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
