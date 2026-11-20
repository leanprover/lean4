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
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Elab_InfoTree_format(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_error_to_string(lean_object*);
size_t lean_array_size(lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_elabCommand(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_InfoState_substituteLazy(lean_object*);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4;
static lean_once_cell_t l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__5(lean_object* v_opts_19_, lean_object* v_opt_20_){
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
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__5___boxed(lean_object* v_opts_29_, lean_object* v_opt_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__5(v_opts_29_, v_opt_30_);
lean_dec_ref(v_opt_30_);
lean_dec_ref(v_opts_29_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_33_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_34_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__0);
v___x_35_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
return v___x_35_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_37_);
lean_ctor_set(v___x_38_, 2, v___x_37_);
lean_ctor_set(v___x_38_, 3, v___x_37_);
lean_ctor_set(v___x_38_, 4, v___x_36_);
lean_ctor_set(v___x_38_, 5, v___x_36_);
lean_ctor_set(v___x_38_, 6, v___x_36_);
lean_ctor_set(v___x_38_, 7, v___x_36_);
lean_ctor_set(v___x_38_, 8, v___x_36_);
lean_ctor_set(v___x_38_, 9, v___x_36_);
lean_ctor_set(v___x_38_, 10, v___x_36_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_39_ = lean_unsigned_to_nat(32u);
v___x_40_ = lean_mk_empty_array_with_capacity(v___x_39_);
v___x_41_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_41_, 0, v___x_40_);
return v___x_41_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_42_ = ((size_t)5ULL);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_unsigned_to_nat(32u);
v___x_45_ = lean_mk_empty_array_with_capacity(v___x_44_);
v___x_46_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_47_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_47_, 0, v___x_46_);
lean_ctor_set(v___x_47_, 1, v___x_45_);
lean_ctor_set(v___x_47_, 2, v___x_43_);
lean_ctor_set(v___x_47_, 3, v___x_43_);
lean_ctor_set_usize(v___x_47_, 4, v___x_42_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_48_ = lean_box(1);
v___x_49_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_51_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v___x_49_);
lean_ctor_set(v___x_51_, 2, v___x_48_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg(lean_object* v_msgData_52_, lean_object* v___y_53_){
_start:
{
lean_object* v___x_55_; lean_object* v_env_56_; uint8_t v___x_57_; lean_object* v_env_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v_scopes_61_; lean_object* v___x_62_; lean_object* v_opts_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_55_ = lean_st_ref_get(v___y_53_);
v_env_56_ = lean_ctor_get(v___x_55_, 0);
lean_inc_ref(v_env_56_);
lean_dec(v___x_55_);
v___x_57_ = 0;
v_env_58_ = l_Lean_Environment_setRecordingDeps(v_env_56_, v___x_57_);
v___x_59_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_60_ = lean_st_ref_get(v___y_53_);
v_scopes_61_ = lean_ctor_get(v___x_60_, 2);
lean_inc(v_scopes_61_);
lean_dec(v___x_60_);
v___x_62_ = l_List_head_x21___redArg(v___x_59_, v_scopes_61_);
lean_dec(v_scopes_61_);
v_opts_63_ = lean_ctor_get(v___x_62_, 1);
lean_inc_ref(v_opts_63_);
lean_dec(v___x_62_);
v___x_64_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_65_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_66_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_66_, 0, v_env_58_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
lean_ctor_set(v___x_66_, 2, v___x_65_);
lean_ctor_set(v___x_66_, 3, v_opts_63_);
v___x_67_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v_msgData_52_);
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg(v_msgData_69_, v___y_70_);
lean_dec(v___y_70_);
return v_res_72_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_74_, lean_object* v_x_75_){
_start:
{
if (lean_obj_tag(v_x_75_) == 1)
{
lean_object* v_pre_76_; 
v_pre_76_ = lean_ctor_get(v_x_75_, 0);
if (lean_obj_tag(v_pre_76_) == 0)
{
lean_object* v_str_77_; lean_object* v___x_78_; uint8_t v___x_79_; 
v_str_77_ = lean_ctor_get(v_x_75_, 1);
v___x_78_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___closed__0));
v___x_79_ = lean_string_dec_eq(v_str_77_, v___x_78_);
if (v___x_79_ == 0)
{
return v___x_79_;
}
else
{
return v_suppressElabErrors_74_;
}
}
else
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
}
else
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_82_, lean_object* v_x_83_){
_start:
{
uint8_t v_suppressElabErrors_boxed_84_; uint8_t v_res_85_; lean_object* v_r_86_; 
v_suppressElabErrors_boxed_84_ = lean_unbox(v_suppressElabErrors_82_);
v_res_85_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_84_, v_x_83_);
lean_dec(v_x_83_);
v_r_86_ = lean_box(v_res_85_);
return v_r_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(lean_object* v_ref_88_, lean_object* v_msgData_89_, uint8_t v_severity_90_, uint8_t v_isSilent_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v___y_96_; uint8_t v___y_97_; uint8_t v___y_98_; lean_object* v___y_99_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_161_; uint8_t v___y_162_; uint8_t v___y_163_; lean_object* v___y_164_; uint8_t v___y_187_; uint8_t v___y_188_; lean_object* v___y_189_; lean_object* v___y_190_; uint8_t v___y_194_; uint8_t v___y_195_; uint8_t v___x_210_; uint8_t v___y_212_; uint8_t v___x_222_; 
v___x_210_ = 2;
v___x_222_ = l_Lean_instBEqMessageSeverity_beq(v_severity_90_, v___x_210_);
if (v___x_222_ == 0)
{
v___y_212_ = v___x_222_;
goto v___jp_211_;
}
else
{
uint8_t v___x_223_; 
lean_inc_ref(v_msgData_89_);
v___x_223_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_89_);
if (v___x_223_ == 0)
{
v___y_212_ = v___x_223_;
goto v___jp_211_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; 
lean_dec_ref(v_msgData_89_);
v___x_224_ = lean_box(0);
v___x_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
return v___x_225_;
}
}
v___jp_95_:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_Elab_Command_getScope___redArg(v___y_103_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v_currNamespace_106_; lean_object* v___x_107_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v_currNamespace_106_ = lean_ctor_get(v_a_105_, 2);
lean_inc(v_currNamespace_106_);
lean_dec(v_a_105_);
v___x_107_ = l_Lean_Elab_Command_getScope___redArg(v___y_103_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_143_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_143_ == 0)
{
v___x_110_ = v___x_107_;
v_isShared_111_ = v_isSharedCheck_143_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v___x_107_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_143_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v_openDecls_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v_env_117_; lean_object* v_messages_118_; lean_object* v_scopes_119_; lean_object* v_usedQuotCtxts_120_; lean_object* v_nextMacroScope_121_; lean_object* v_maxRecDepth_122_; lean_object* v_ngen_123_; lean_object* v_auxDeclNGen_124_; lean_object* v_infoState_125_; lean_object* v_traceState_126_; lean_object* v_snapshotTasks_127_; lean_object* v_prevLinterStates_128_; lean_object* v_codeQualityEntryTasks_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_142_; 
v_openDecls_112_ = lean_ctor_get(v_a_108_, 3);
lean_inc(v_openDecls_112_);
lean_dec(v_a_108_);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_currNamespace_106_);
lean_ctor_set(v___x_113_, 1, v_openDecls_112_);
v___x_114_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___y_100_);
lean_inc_ref(v___y_102_);
lean_inc_ref(v___y_96_);
v___x_115_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_115_, 0, v___y_96_);
lean_ctor_set(v___x_115_, 1, v___y_99_);
lean_ctor_set(v___x_115_, 2, v___y_101_);
lean_ctor_set(v___x_115_, 3, v___y_102_);
lean_ctor_set(v___x_115_, 4, v___x_114_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*5, v___y_97_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*5 + 1, v___y_98_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*5 + 2, v_isSilent_91_);
v___x_116_ = lean_st_ref_take(v___y_103_);
v_env_117_ = lean_ctor_get(v___x_116_, 0);
v_messages_118_ = lean_ctor_get(v___x_116_, 1);
v_scopes_119_ = lean_ctor_get(v___x_116_, 2);
v_usedQuotCtxts_120_ = lean_ctor_get(v___x_116_, 3);
v_nextMacroScope_121_ = lean_ctor_get(v___x_116_, 4);
v_maxRecDepth_122_ = lean_ctor_get(v___x_116_, 5);
v_ngen_123_ = lean_ctor_get(v___x_116_, 6);
v_auxDeclNGen_124_ = lean_ctor_get(v___x_116_, 7);
v_infoState_125_ = lean_ctor_get(v___x_116_, 8);
v_traceState_126_ = lean_ctor_get(v___x_116_, 9);
v_snapshotTasks_127_ = lean_ctor_get(v___x_116_, 10);
v_prevLinterStates_128_ = lean_ctor_get(v___x_116_, 11);
v_codeQualityEntryTasks_129_ = lean_ctor_get(v___x_116_, 12);
v_isSharedCheck_142_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_142_ == 0)
{
v___x_131_ = v___x_116_;
v_isShared_132_ = v_isSharedCheck_142_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_codeQualityEntryTasks_129_);
lean_inc(v_prevLinterStates_128_);
lean_inc(v_snapshotTasks_127_);
lean_inc(v_traceState_126_);
lean_inc(v_infoState_125_);
lean_inc(v_auxDeclNGen_124_);
lean_inc(v_ngen_123_);
lean_inc(v_maxRecDepth_122_);
lean_inc(v_nextMacroScope_121_);
lean_inc(v_usedQuotCtxts_120_);
lean_inc(v_scopes_119_);
lean_inc(v_messages_118_);
lean_inc(v_env_117_);
lean_dec(v___x_116_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_142_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_133_ = lean_box(0);
v___x_134_ = l_Lean_MessageLog_add(v___x_115_, v_messages_118_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_134_);
v___x_136_ = v___x_131_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_env_117_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_scopes_119_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v_usedQuotCtxts_120_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v_nextMacroScope_121_);
lean_ctor_set(v_reuseFailAlloc_141_, 5, v_maxRecDepth_122_);
lean_ctor_set(v_reuseFailAlloc_141_, 6, v_ngen_123_);
lean_ctor_set(v_reuseFailAlloc_141_, 7, v_auxDeclNGen_124_);
lean_ctor_set(v_reuseFailAlloc_141_, 8, v_infoState_125_);
lean_ctor_set(v_reuseFailAlloc_141_, 9, v_traceState_126_);
lean_ctor_set(v_reuseFailAlloc_141_, 10, v_snapshotTasks_127_);
lean_ctor_set(v_reuseFailAlloc_141_, 11, v_prevLinterStates_128_);
lean_ctor_set(v_reuseFailAlloc_141_, 12, v_codeQualityEntryTasks_129_);
v___x_136_ = v_reuseFailAlloc_141_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_st_ref_put(v___y_103_, v___x_136_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_133_);
v___x_139_ = v___x_110_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_133_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
else
{
lean_object* v_a_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_currNamespace_106_);
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec_ref(v___y_99_);
v_a_144_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_151_ == 0)
{
v___x_146_ = v___x_107_;
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_a_144_);
lean_dec(v___x_107_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_151_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_149_; 
if (v_isShared_147_ == 0)
{
v___x_149_ = v___x_146_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_a_144_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
else
{
lean_object* v_a_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_159_; 
lean_dec(v___y_101_);
lean_dec_ref(v___y_100_);
lean_dec_ref(v___y_99_);
v_a_152_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_159_ == 0)
{
v___x_154_ = v___x_104_;
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_a_152_);
lean_dec(v___x_104_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_159_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_157_; 
if (v_isShared_155_ == 0)
{
v___x_157_ = v___x_154_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
}
v___jp_160_:
{
lean_object* v_fileName_165_; lean_object* v_fileMap_166_; uint8_t v_suppressElabErrors_167_; lean_object* v___x_168_; lean_object* v___f_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_185_; 
v_fileName_165_ = lean_ctor_get(v___y_92_, 0);
v_fileMap_166_ = lean_ctor_get(v___y_92_, 1);
v_suppressElabErrors_167_ = lean_ctor_get_uint8(v___y_92_, sizeof(void*)*10);
v___x_168_ = lean_box(v_suppressElabErrors_167_);
v___f_169_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_169_, 0, v___x_168_);
v___x_170_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_89_);
v___x_171_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg(v___x_170_, v___y_93_);
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_185_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_185_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_185_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
lean_inc_ref_n(v_fileMap_166_, 2);
v___x_176_ = l_Lean_FileMap_toPosition(v_fileMap_166_, v___y_161_);
lean_dec(v___y_161_);
v___x_177_ = l_Lean_FileMap_toPosition(v_fileMap_166_, v___y_164_);
lean_dec(v___y_164_);
v___x_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
v___x_179_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_167_ == 0)
{
lean_del_object(v___x_174_);
lean_dec_ref(v___f_169_);
v___y_96_ = v_fileName_165_;
v___y_97_ = v___y_162_;
v___y_98_ = v___y_163_;
v___y_99_ = v___x_176_;
v___y_100_ = v_a_172_;
v___y_101_ = v___x_178_;
v___y_102_ = v___x_179_;
v___y_103_ = v___y_93_;
goto v___jp_95_;
}
else
{
uint8_t v___x_180_; 
lean_inc(v_a_172_);
v___x_180_ = l_Lean_MessageData_hasTag(v___f_169_, v_a_172_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_183_; 
lean_dec_ref_known(v___x_178_, 1);
lean_dec_ref(v___x_176_);
lean_dec(v_a_172_);
v___x_181_ = lean_box(0);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_181_);
v___x_183_ = v___x_174_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_181_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
else
{
lean_del_object(v___x_174_);
v___y_96_ = v_fileName_165_;
v___y_97_ = v___y_162_;
v___y_98_ = v___y_163_;
v___y_99_ = v___x_176_;
v___y_100_ = v_a_172_;
v___y_101_ = v___x_178_;
v___y_102_ = v___x_179_;
v___y_103_ = v___y_93_;
goto v___jp_95_;
}
}
}
}
v___jp_186_:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_Syntax_getTailPos_x3f(v___y_189_, v___y_187_);
lean_dec(v___y_189_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_inc(v___y_190_);
v___y_161_ = v___y_190_;
v___y_162_ = v___y_187_;
v___y_163_ = v___y_188_;
v___y_164_ = v___y_190_;
goto v___jp_160_;
}
else
{
lean_object* v_val_192_; 
v_val_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v___x_191_, 1);
v___y_161_ = v___y_190_;
v___y_162_ = v___y_187_;
v___y_163_ = v___y_188_;
v___y_164_ = v_val_192_;
goto v___jp_160_;
}
}
v___jp_193_:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean_Elab_Command_getRef___redArg(v___y_92_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v_ref_198_; lean_object* v___x_199_; 
v_a_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_197_);
lean_dec_ref_known(v___x_196_, 1);
v_ref_198_ = l_Lean_replaceRef(v_ref_88_, v_a_197_);
lean_dec(v_a_197_);
v___x_199_ = l_Lean_Syntax_getPos_x3f(v_ref_198_, v___y_194_);
if (lean_obj_tag(v___x_199_) == 0)
{
lean_object* v___x_200_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___y_187_ = v___y_194_;
v___y_188_ = v___y_195_;
v___y_189_ = v_ref_198_;
v___y_190_ = v___x_200_;
goto v___jp_186_;
}
else
{
lean_object* v_val_201_; 
v_val_201_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_val_201_);
lean_dec_ref_known(v___x_199_, 1);
v___y_187_ = v___y_194_;
v___y_188_ = v___y_195_;
v___y_189_ = v_ref_198_;
v___y_190_ = v_val_201_;
goto v___jp_186_;
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec_ref(v_msgData_89_);
v_a_202_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_196_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_196_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
v___jp_211_:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_scopes_215_; lean_object* v___x_216_; lean_object* v_opts_217_; uint8_t v___x_218_; uint8_t v___x_219_; 
v___x_213_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_214_ = lean_st_ref_get(v___y_93_);
v_scopes_215_ = lean_ctor_get(v___x_214_, 2);
lean_inc(v_scopes_215_);
lean_dec(v___x_214_);
v___x_216_ = l_List_head_x21___redArg(v___x_213_, v_scopes_215_);
lean_dec(v_scopes_215_);
v_opts_217_ = lean_ctor_get(v___x_216_, 1);
lean_inc_ref(v_opts_217_);
lean_dec(v___x_216_);
v___x_218_ = 1;
v___x_219_ = l_Lean_instBEqMessageSeverity_beq(v_severity_90_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v_opts_217_);
v___y_194_ = v___y_212_;
v___y_195_ = v_severity_90_;
goto v___jp_193_;
}
else
{
lean_object* v___x_220_; uint8_t v___x_221_; 
v___x_220_ = l_Lean_warningAsError;
v___x_221_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__5(v_opts_217_, v___x_220_);
lean_dec_ref(v_opts_217_);
if (v___x_221_ == 0)
{
v___y_194_ = v___y_212_;
v___y_195_ = v_severity_90_;
goto v___jp_193_;
}
else
{
v___y_194_ = v___y_212_;
v___y_195_ = v___x_210_;
goto v___jp_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___boxed(lean_object* v_ref_226_, lean_object* v_msgData_227_, lean_object* v_severity_228_, lean_object* v_isSilent_229_, lean_object* v___y_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
uint8_t v_severity_boxed_233_; uint8_t v_isSilent_boxed_234_; lean_object* v_res_235_; 
v_severity_boxed_233_ = lean_unbox(v_severity_228_);
v_isSilent_boxed_234_ = lean_unbox(v_isSilent_229_);
v_res_235_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_ref_226_, v_msgData_227_, v_severity_boxed_233_, v_isSilent_boxed_234_, v___y_230_, v___y_231_);
lean_dec(v___y_231_);
lean_dec_ref(v___y_230_);
lean_dec(v_ref_226_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(lean_object* v_msgData_236_, uint8_t v_severity_237_, uint8_t v_isSilent_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_Elab_Command_getRef___redArg(v___y_239_);
if (lean_obj_tag(v___x_242_) == 0)
{
lean_object* v_a_243_; lean_object* v___x_244_; 
v_a_243_ = lean_ctor_get(v___x_242_, 0);
lean_inc(v_a_243_);
lean_dec_ref_known(v___x_242_, 1);
v___x_244_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_a_243_, v_msgData_236_, v_severity_237_, v_isSilent_238_, v___y_239_, v___y_240_);
lean_dec(v_a_243_);
return v___x_244_;
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec_ref(v_msgData_236_);
v_a_245_ = lean_ctor_get(v___x_242_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_242_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_242_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_242_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___boxed(lean_object* v_msgData_253_, lean_object* v_severity_254_, lean_object* v_isSilent_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
uint8_t v_severity_boxed_259_; uint8_t v_isSilent_boxed_260_; lean_object* v_res_261_; 
v_severity_boxed_259_ = lean_unbox(v_severity_254_);
v_isSilent_boxed_260_ = lean_unbox(v_isSilent_255_);
v_res_261_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_msgData_253_, v_severity_boxed_259_, v_isSilent_boxed_260_, v___y_256_, v___y_257_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(lean_object* v_msgData_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v___x_266_; uint8_t v___x_267_; lean_object* v___x_268_; 
v___x_266_ = 2;
v___x_267_ = 0;
v___x_268_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_msgData_262_, v___x_266_, v___x_267_, v___y_263_, v___y_264_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1___boxed(lean_object* v_msgData_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_msgData_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(lean_object* v_ref_274_, lean_object* v_msgData_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
uint8_t v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; 
v___x_279_ = 0;
v___x_280_ = 0;
v___x_281_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_ref_274_, v_msgData_275_, v___x_279_, v___x_280_, v___y_276_, v___y_277_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2___boxed(lean_object* v_ref_282_, lean_object* v_msgData_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_ref_282_, v_msgData_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v_ref_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10(lean_object* v_tk_291_, lean_object* v_as_292_, size_t v_sz_293_, size_t v_i_294_, lean_object* v_b_295_, lean_object* v___y_296_, lean_object* v___y_297_){
_start:
{
uint8_t v___x_299_; 
v___x_299_ = lean_usize_dec_lt(v_i_294_, v_sz_293_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; 
v___x_300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_300_, 0, v_b_295_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; lean_object* v_a_302_; lean_object* v___x_303_; 
lean_dec_ref(v_b_295_);
v___x_301_ = lean_box(0);
v_a_302_ = lean_array_uget_borrowed(v_as_292_, v_i_294_);
lean_inc(v_a_302_);
v___x_303_ = l_Lean_Elab_InfoTree_format(v_a_302_, v___x_301_);
if (lean_obj_tag(v___x_303_) == 0)
{
lean_object* v_a_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_a_304_ = lean_ctor_get(v___x_303_, 0);
lean_inc(v_a_304_);
lean_dec_ref_known(v___x_303_, 1);
v___x_305_ = l_Lean_MessageData_ofFormat(v_a_304_);
v___x_306_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_291_, v___x_305_, v___y_296_, v___y_297_);
if (lean_obj_tag(v___x_306_) == 0)
{
lean_object* v___x_307_; size_t v___x_308_; size_t v___x_309_; 
lean_dec_ref_known(v___x_306_, 1);
v___x_307_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___closed__0));
v___x_308_ = ((size_t)1ULL);
v___x_309_ = lean_usize_add(v_i_294_, v___x_308_);
v_i_294_ = v___x_309_;
v_b_295_ = v___x_307_;
goto _start;
}
else
{
lean_object* v_a_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_a_311_ = lean_ctor_get(v___x_306_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_306_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_306_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_a_311_);
lean_dec(v___x_306_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_a_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_331_; 
v_a_319_ = lean_ctor_get(v___x_303_, 0);
v_isSharedCheck_331_ = !lean_is_exclusive(v___x_303_);
if (v_isSharedCheck_331_ == 0)
{
v___x_321_ = v___x_303_;
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_303_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_331_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_ref_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v_ref_323_ = lean_ctor_get(v___y_296_, 7);
v___x_324_ = lean_io_error_to_string(v_a_319_);
v___x_325_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
v___x_326_ = l_Lean_MessageData_ofFormat(v___x_325_);
lean_inc(v_ref_323_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v_ref_323_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_327_);
v___x_329_ = v___x_321_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___boxed(lean_object* v_tk_332_, lean_object* v_as_333_, lean_object* v_sz_334_, lean_object* v_i_335_, lean_object* v_b_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_){
_start:
{
size_t v_sz_boxed_340_; size_t v_i_boxed_341_; lean_object* v_res_342_; 
v_sz_boxed_340_ = lean_unbox_usize(v_sz_334_);
lean_dec(v_sz_334_);
v_i_boxed_341_ = lean_unbox_usize(v_i_335_);
lean_dec(v_i_335_);
v_res_342_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10(v_tk_332_, v_as_333_, v_sz_boxed_340_, v_i_boxed_341_, v_b_336_, v___y_337_, v___y_338_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec_ref(v_as_333_);
lean_dec(v_tk_332_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9(lean_object* v_tk_343_, lean_object* v_as_344_, size_t v_sz_345_, size_t v_i_346_, lean_object* v_b_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = lean_usize_dec_lt(v_i_346_, v_sz_345_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; 
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v_b_347_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v_a_354_; lean_object* v___x_355_; 
lean_dec_ref(v_b_347_);
v___x_353_ = lean_box(0);
v_a_354_ = lean_array_uget_borrowed(v_as_344_, v_i_346_);
lean_inc(v_a_354_);
v___x_355_ = l_Lean_Elab_InfoTree_format(v_a_354_, v___x_353_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v___x_355_, 1);
v___x_357_ = l_Lean_MessageData_ofFormat(v_a_356_);
v___x_358_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_343_, v___x_357_, v___y_348_, v___y_349_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v___x_359_; size_t v___x_360_; size_t v___x_361_; lean_object* v___x_362_; 
lean_dec_ref_known(v___x_358_, 1);
v___x_359_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___closed__0));
v___x_360_ = ((size_t)1ULL);
v___x_361_ = lean_usize_add(v_i_346_, v___x_360_);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10(v_tk_343_, v_as_344_, v_sz_345_, v___x_361_, v___x_359_, v___y_348_, v___y_349_);
return v___x_362_;
}
else
{
lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_370_; 
v_a_363_ = lean_ctor_get(v___x_358_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_358_);
if (v_isSharedCheck_370_ == 0)
{
v___x_365_ = v___x_358_;
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_dec(v___x_358_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_370_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_366_ == 0)
{
v___x_368_ = v___x_365_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
else
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_383_; 
v_a_371_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_383_ == 0)
{
v___x_373_ = v___x_355_;
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_355_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_383_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v_ref_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_381_; 
v_ref_375_ = lean_ctor_get(v___y_348_, 7);
v___x_376_ = lean_io_error_to_string(v_a_371_);
v___x_377_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
v___x_378_ = l_Lean_MessageData_ofFormat(v___x_377_);
lean_inc(v_ref_375_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v_ref_375_);
lean_ctor_set(v___x_379_, 1, v___x_378_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_379_);
v___x_381_ = v___x_373_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9___boxed(lean_object* v_tk_384_, lean_object* v_as_385_, lean_object* v_sz_386_, lean_object* v_i_387_, lean_object* v_b_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
size_t v_sz_boxed_392_; size_t v_i_boxed_393_; lean_object* v_res_394_; 
v_sz_boxed_392_ = lean_unbox_usize(v_sz_386_);
lean_dec(v_sz_386_);
v_i_boxed_393_ = lean_unbox_usize(v_i_387_);
lean_dec(v_i_387_);
v_res_394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9(v_tk_384_, v_as_385_, v_sz_boxed_392_, v_i_boxed_393_, v_b_388_, v___y_389_, v___y_390_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec_ref(v_as_385_);
lean_dec(v_tk_384_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5(lean_object* v_init_395_, lean_object* v_tk_396_, lean_object* v_n_397_, lean_object* v_b_398_, lean_object* v___y_399_, lean_object* v___y_400_){
_start:
{
if (lean_obj_tag(v_n_397_) == 0)
{
lean_object* v_cs_402_; lean_object* v___x_403_; lean_object* v___x_404_; size_t v_sz_405_; size_t v___x_406_; lean_object* v___x_407_; 
v_cs_402_ = lean_ctor_get(v_n_397_, 0);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_b_398_);
v_sz_405_ = lean_array_size(v_cs_402_);
v___x_406_ = ((size_t)0ULL);
v___x_407_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8(v_init_395_, v_tk_396_, v_cs_402_, v_sz_405_, v___x_406_, v___x_404_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_407_) == 0)
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_422_; 
v_a_408_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_422_ == 0)
{
v___x_410_ = v___x_407_;
v_isShared_411_ = v_isSharedCheck_422_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_407_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_422_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v_fst_412_; 
v_fst_412_ = lean_ctor_get(v_a_408_, 0);
if (lean_obj_tag(v_fst_412_) == 0)
{
lean_object* v_snd_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v_snd_413_ = lean_ctor_get(v_a_408_, 1);
lean_inc(v_snd_413_);
lean_dec(v_a_408_);
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v_snd_413_);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v___x_414_);
v___x_416_ = v___x_410_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
else
{
lean_object* v_val_418_; lean_object* v___x_420_; 
lean_inc_ref(v_fst_412_);
lean_dec(v_a_408_);
v_val_418_ = lean_ctor_get(v_fst_412_, 0);
lean_inc(v_val_418_);
lean_dec_ref_known(v_fst_412_, 1);
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 0, v_val_418_);
v___x_420_ = v___x_410_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_val_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
}
else
{
lean_object* v_a_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_430_; 
v_a_423_ = lean_ctor_get(v___x_407_, 0);
v_isSharedCheck_430_ = !lean_is_exclusive(v___x_407_);
if (v_isSharedCheck_430_ == 0)
{
v___x_425_ = v___x_407_;
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_a_423_);
lean_dec(v___x_407_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_430_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_428_; 
if (v_isShared_426_ == 0)
{
v___x_428_ = v___x_425_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v_a_423_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
else
{
lean_object* v_vs_431_; lean_object* v___x_432_; lean_object* v___x_433_; size_t v_sz_434_; size_t v___x_435_; lean_object* v___x_436_; 
v_vs_431_ = lean_ctor_get(v_n_397_, 0);
v___x_432_ = lean_box(0);
v___x_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
lean_ctor_set(v___x_433_, 1, v_b_398_);
v_sz_434_ = lean_array_size(v_vs_431_);
v___x_435_ = ((size_t)0ULL);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9(v_tk_396_, v_vs_431_, v_sz_434_, v___x_435_, v___x_433_, v___y_399_, v___y_400_);
if (lean_obj_tag(v___x_436_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_451_; 
v_a_437_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_451_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_451_ == 0)
{
v___x_439_ = v___x_436_;
v_isShared_440_ = v_isSharedCheck_451_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_a_437_);
lean_dec(v___x_436_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_451_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_fst_441_; 
v_fst_441_ = lean_ctor_get(v_a_437_, 0);
if (lean_obj_tag(v_fst_441_) == 0)
{
lean_object* v_snd_442_; lean_object* v___x_443_; lean_object* v___x_445_; 
v_snd_442_ = lean_ctor_get(v_a_437_, 1);
lean_inc(v_snd_442_);
lean_dec(v_a_437_);
v___x_443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_443_, 0, v_snd_442_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v___x_443_);
v___x_445_ = v___x_439_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_443_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
lean_object* v_val_447_; lean_object* v___x_449_; 
lean_inc_ref(v_fst_441_);
lean_dec(v_a_437_);
v_val_447_ = lean_ctor_get(v_fst_441_, 0);
lean_inc(v_val_447_);
lean_dec_ref_known(v_fst_441_, 1);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v_val_447_);
v___x_449_ = v___x_439_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_val_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
else
{
lean_object* v_a_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_459_; 
v_a_452_ = lean_ctor_get(v___x_436_, 0);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_436_);
if (v_isSharedCheck_459_ == 0)
{
v___x_454_ = v___x_436_;
v_isShared_455_ = v_isSharedCheck_459_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_a_452_);
lean_dec(v___x_436_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8(lean_object* v_init_460_, lean_object* v_tk_461_, lean_object* v_as_462_, size_t v_sz_463_, size_t v_i_464_, lean_object* v_b_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
uint8_t v___x_469_; 
v___x_469_ = lean_usize_dec_lt(v_i_464_, v_sz_463_);
if (v___x_469_ == 0)
{
lean_object* v___x_470_; 
v___x_470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_470_, 0, v_b_465_);
return v___x_470_;
}
else
{
lean_object* v_snd_471_; lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_505_; 
v_snd_471_ = lean_ctor_get(v_b_465_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_b_465_);
if (v_isSharedCheck_505_ == 0)
{
lean_object* v_unused_506_; 
v_unused_506_ = lean_ctor_get(v_b_465_, 0);
lean_dec(v_unused_506_);
v___x_473_ = v_b_465_;
v_isShared_474_ = v_isSharedCheck_505_;
goto v_resetjp_472_;
}
else
{
lean_inc(v_snd_471_);
lean_dec(v_b_465_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_505_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v_a_476_; lean_object* v___x_477_; 
v___x_475_ = lean_box(0);
v_a_476_ = lean_array_uget_borrowed(v_as_462_, v_i_464_);
lean_inc(v_snd_471_);
v___x_477_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5(v_init_460_, v_tk_461_, v_a_476_, v_snd_471_, v___y_466_, v___y_467_);
if (lean_obj_tag(v___x_477_) == 0)
{
lean_object* v_a_478_; lean_object* v___x_480_; uint8_t v_isShared_481_; uint8_t v_isSharedCheck_496_; 
v_a_478_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_496_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_496_ == 0)
{
v___x_480_ = v___x_477_;
v_isShared_481_ = v_isSharedCheck_496_;
goto v_resetjp_479_;
}
else
{
lean_inc(v_a_478_);
lean_dec(v___x_477_);
v___x_480_ = lean_box(0);
v_isShared_481_ = v_isSharedCheck_496_;
goto v_resetjp_479_;
}
v_resetjp_479_:
{
if (lean_obj_tag(v_a_478_) == 0)
{
lean_object* v___x_482_; lean_object* v___x_484_; 
v___x_482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_482_, 0, v_a_478_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 0, v___x_482_);
v___x_484_ = v___x_473_;
goto v_reusejp_483_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_482_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_snd_471_);
v___x_484_ = v_reuseFailAlloc_488_;
goto v_reusejp_483_;
}
v_reusejp_483_:
{
lean_object* v___x_486_; 
if (v_isShared_481_ == 0)
{
lean_ctor_set(v___x_480_, 0, v___x_484_);
v___x_486_ = v___x_480_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v___x_484_);
v___x_486_ = v_reuseFailAlloc_487_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
return v___x_486_;
}
}
}
else
{
lean_object* v_a_489_; lean_object* v___x_491_; 
lean_del_object(v___x_480_);
lean_dec(v_snd_471_);
v_a_489_ = lean_ctor_get(v_a_478_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v_a_478_, 1);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v_a_489_);
lean_ctor_set(v___x_473_, 0, v___x_475_);
v___x_491_ = v___x_473_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_a_489_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
size_t v___x_492_; size_t v___x_493_; 
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_464_, v___x_492_);
v_i_464_ = v___x_493_;
v_b_465_ = v___x_491_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_504_; 
lean_del_object(v___x_473_);
lean_dec(v_snd_471_);
v_a_497_ = lean_ctor_get(v___x_477_, 0);
v_isSharedCheck_504_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_504_ == 0)
{
v___x_499_ = v___x_477_;
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_a_497_);
lean_dec(v___x_477_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_504_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v___x_502_; 
if (v_isShared_500_ == 0)
{
v___x_502_ = v___x_499_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_a_497_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8___boxed(lean_object* v_init_507_, lean_object* v_tk_508_, lean_object* v_as_509_, lean_object* v_sz_510_, lean_object* v_i_511_, lean_object* v_b_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_510_);
lean_dec(v_sz_510_);
v_i_boxed_517_ = lean_unbox_usize(v_i_511_);
lean_dec(v_i_511_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8(v_init_507_, v_tk_508_, v_as_509_, v_sz_boxed_516_, v_i_boxed_517_, v_b_512_, v___y_513_, v___y_514_);
lean_dec(v___y_514_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v_as_509_);
lean_dec(v_tk_508_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5___boxed(lean_object* v_init_519_, lean_object* v_tk_520_, lean_object* v_n_521_, lean_object* v_b_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5(v_init_519_, v_tk_520_, v_n_521_, v_b_522_, v___y_523_, v___y_524_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v_n_521_);
lean_dec(v_tk_520_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11(lean_object* v_tk_530_, lean_object* v_as_531_, size_t v_sz_532_, size_t v_i_533_, lean_object* v_b_534_, lean_object* v___y_535_, lean_object* v___y_536_){
_start:
{
uint8_t v___x_538_; 
v___x_538_ = lean_usize_dec_lt(v_i_533_, v_sz_532_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
v___x_539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_539_, 0, v_b_534_);
return v___x_539_;
}
else
{
lean_object* v___x_540_; lean_object* v_a_541_; lean_object* v___x_542_; 
lean_dec_ref(v_b_534_);
v___x_540_ = lean_box(0);
v_a_541_ = lean_array_uget_borrowed(v_as_531_, v_i_533_);
lean_inc(v_a_541_);
v___x_542_ = l_Lean_Elab_InfoTree_format(v_a_541_, v___x_540_);
if (lean_obj_tag(v___x_542_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; lean_object* v___x_545_; 
v_a_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v___x_542_, 1);
v___x_544_ = l_Lean_MessageData_ofFormat(v_a_543_);
v___x_545_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_530_, v___x_544_, v___y_535_, v___y_536_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_546_; size_t v___x_547_; size_t v___x_548_; 
lean_dec_ref_known(v___x_545_, 1);
v___x_546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___closed__0));
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_add(v_i_533_, v___x_547_);
v_i_533_ = v___x_548_;
v_b_534_ = v___x_546_;
goto _start;
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
v_a_550_ = lean_ctor_get(v___x_545_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_545_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_545_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_545_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
else
{
lean_object* v_a_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_570_; 
v_a_558_ = lean_ctor_get(v___x_542_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_542_);
if (v_isSharedCheck_570_ == 0)
{
v___x_560_ = v___x_542_;
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_a_558_);
lean_dec(v___x_542_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_570_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v_ref_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
v_ref_562_ = lean_ctor_get(v___y_535_, 7);
v___x_563_ = lean_io_error_to_string(v_a_558_);
v___x_564_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
v___x_565_ = l_Lean_MessageData_ofFormat(v___x_564_);
lean_inc(v_ref_562_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v_ref_562_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_566_);
v___x_568_ = v___x_560_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v___x_566_);
v___x_568_ = v_reuseFailAlloc_569_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
return v___x_568_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___boxed(lean_object* v_tk_571_, lean_object* v_as_572_, lean_object* v_sz_573_, lean_object* v_i_574_, lean_object* v_b_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_){
_start:
{
size_t v_sz_boxed_579_; size_t v_i_boxed_580_; lean_object* v_res_581_; 
v_sz_boxed_579_ = lean_unbox_usize(v_sz_573_);
lean_dec(v_sz_573_);
v_i_boxed_580_ = lean_unbox_usize(v_i_574_);
lean_dec(v_i_574_);
v_res_581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11(v_tk_571_, v_as_572_, v_sz_boxed_579_, v_i_boxed_580_, v_b_575_, v___y_576_, v___y_577_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec_ref(v_as_572_);
lean_dec(v_tk_571_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(lean_object* v_tk_582_, lean_object* v_as_583_, size_t v_sz_584_, size_t v_i_585_, lean_object* v_b_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
uint8_t v___x_590_; 
v___x_590_ = lean_usize_dec_lt(v_i_585_, v_sz_584_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
v___x_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_591_, 0, v_b_586_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; lean_object* v_a_593_; lean_object* v___x_594_; 
lean_dec_ref(v_b_586_);
v___x_592_ = lean_box(0);
v_a_593_ = lean_array_uget_borrowed(v_as_583_, v_i_585_);
lean_inc(v_a_593_);
v___x_594_ = l_Lean_Elab_InfoTree_format(v_a_593_, v___x_592_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
lean_dec_ref_known(v___x_594_, 1);
v___x_596_ = l_Lean_MessageData_ofFormat(v_a_595_);
v___x_597_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_582_, v___x_596_, v___y_587_, v___y_588_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v___x_598_; size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; 
lean_dec_ref_known(v___x_597_, 1);
v___x_598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___closed__0));
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_add(v_i_585_, v___x_599_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11(v_tk_582_, v_as_583_, v_sz_584_, v___x_600_, v___x_598_, v___y_587_, v___y_588_);
return v___x_601_;
}
else
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
v_a_602_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_597_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_597_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_622_; 
v_a_610_ = lean_ctor_get(v___x_594_, 0);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_594_);
if (v_isSharedCheck_622_ == 0)
{
v___x_612_ = v___x_594_;
v_isShared_613_ = v_isSharedCheck_622_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_594_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_622_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_ref_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v_ref_614_ = lean_ctor_get(v___y_587_, 7);
v___x_615_ = lean_io_error_to_string(v_a_610_);
v___x_616_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
v___x_617_ = l_Lean_MessageData_ofFormat(v___x_616_);
lean_inc(v_ref_614_);
v___x_618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_618_, 0, v_ref_614_);
lean_ctor_set(v___x_618_, 1, v___x_617_);
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v___x_618_);
v___x_620_ = v___x_612_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6___boxed(lean_object* v_tk_623_, lean_object* v_as_624_, lean_object* v_sz_625_, lean_object* v_i_626_, lean_object* v_b_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
size_t v_sz_boxed_631_; size_t v_i_boxed_632_; lean_object* v_res_633_; 
v_sz_boxed_631_ = lean_unbox_usize(v_sz_625_);
lean_dec(v_sz_625_);
v_i_boxed_632_ = lean_unbox_usize(v_i_626_);
lean_dec(v_i_626_);
v_res_633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_tk_623_, v_as_624_, v_sz_boxed_631_, v_i_boxed_632_, v_b_627_, v___y_628_, v___y_629_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec_ref(v_as_624_);
lean_dec(v_tk_623_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object* v_tk_634_, lean_object* v_t_635_, lean_object* v_init_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_root_640_; lean_object* v_tail_641_; lean_object* v___x_642_; 
v_root_640_ = lean_ctor_get(v_t_635_, 0);
v_tail_641_ = lean_ctor_get(v_t_635_, 1);
v___x_642_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5(v_init_636_, v_tk_634_, v_root_640_, v_init_636_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_679_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_679_ == 0)
{
v___x_645_ = v___x_642_;
v_isShared_646_ = v_isSharedCheck_679_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_a_643_);
lean_dec(v___x_642_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_679_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
if (lean_obj_tag(v_a_643_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_649_; 
v_a_647_ = lean_ctor_get(v_a_643_, 0);
lean_inc(v_a_647_);
lean_dec_ref_known(v_a_643_, 1);
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 0, v_a_647_);
v___x_649_ = v___x_645_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_647_);
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
lean_object* v_a_651_; lean_object* v___x_652_; lean_object* v___x_653_; size_t v_sz_654_; size_t v___x_655_; lean_object* v___x_656_; 
lean_del_object(v___x_645_);
v_a_651_ = lean_ctor_get(v_a_643_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v_a_643_, 1);
v___x_652_ = lean_box(0);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v_a_651_);
v_sz_654_ = lean_array_size(v_tail_641_);
v___x_655_ = ((size_t)0ULL);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_tk_634_, v_tail_641_, v_sz_654_, v___x_655_, v___x_653_, v___y_637_, v___y_638_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v___x_659_; uint8_t v_isShared_660_; uint8_t v_isSharedCheck_670_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_670_ == 0)
{
v___x_659_ = v___x_656_;
v_isShared_660_ = v_isSharedCheck_670_;
goto v_resetjp_658_;
}
else
{
lean_inc(v_a_657_);
lean_dec(v___x_656_);
v___x_659_ = lean_box(0);
v_isShared_660_ = v_isSharedCheck_670_;
goto v_resetjp_658_;
}
v_resetjp_658_:
{
lean_object* v_fst_661_; 
v_fst_661_ = lean_ctor_get(v_a_657_, 0);
if (lean_obj_tag(v_fst_661_) == 0)
{
lean_object* v_snd_662_; lean_object* v___x_664_; 
v_snd_662_ = lean_ctor_get(v_a_657_, 1);
lean_inc(v_snd_662_);
lean_dec(v_a_657_);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_snd_662_);
v___x_664_ = v___x_659_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_snd_662_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
else
{
lean_object* v_val_666_; lean_object* v___x_668_; 
lean_inc_ref(v_fst_661_);
lean_dec(v_a_657_);
v_val_666_ = lean_ctor_get(v_fst_661_, 0);
lean_inc(v_val_666_);
lean_dec_ref_known(v_fst_661_, 1);
if (v_isShared_660_ == 0)
{
lean_ctor_set(v___x_659_, 0, v_val_666_);
v___x_668_ = v___x_659_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_val_666_);
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
else
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_678_; 
v_a_671_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_678_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_678_ == 0)
{
v___x_673_ = v___x_656_;
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_656_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_678_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_676_; 
if (v_isShared_674_ == 0)
{
v___x_676_ = v___x_673_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_a_671_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
}
}
else
{
lean_object* v_a_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_687_; 
v_a_680_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_687_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_687_ == 0)
{
v___x_682_ = v___x_642_;
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_a_680_);
lean_dec(v___x_642_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_687_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_685_; 
if (v_isShared_683_ == 0)
{
v___x_685_ = v___x_682_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_a_680_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3___boxed(lean_object* v_tk_688_, lean_object* v_t_689_, lean_object* v_init_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v_tk_688_, v_t_689_, v_init_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec_ref(v_t_689_);
lean_dec(v_tk_688_);
return v_res_694_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5(void){
_start:
{
lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_703_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4));
v___x_704_ = l_Lean_MessageData_ofFormat(v___x_703_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(lean_object* v_x_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_709_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
lean_inc(v_x_705_);
v___x_710_ = l_Lean_Syntax_isOfKind(v_x_705_, v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
lean_dec(v_x_705_);
v___x_711_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
return v___x_711_;
}
else
{
lean_object* v___x_712_; lean_object* v_tk_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v_infoState_717_; uint8_t v_enabled_718_; 
v___x_712_ = lean_unsigned_to_nat(0u);
v_tk_713_ = l_Lean_Syntax_getArg(v_x_705_, v___x_712_);
v___x_714_ = lean_unsigned_to_nat(2u);
v___x_715_ = l_Lean_Syntax_getArg(v_x_705_, v___x_714_);
lean_dec(v_x_705_);
v___x_716_ = lean_st_ref_get(v_a_707_);
v_infoState_717_ = lean_ctor_get(v___x_716_, 8);
lean_inc_ref(v_infoState_717_);
lean_dec(v___x_716_);
v_enabled_718_ = lean_ctor_get_uint8(v_infoState_717_, sizeof(void*)*3);
lean_dec_ref(v_infoState_717_);
if (v_enabled_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_dec(v___x_715_);
lean_dec(v_tk_713_);
v___x_719_ = lean_obj_once(&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5, &l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5_once, _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5);
v___x_720_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v___x_719_, v_a_706_, v_a_707_);
return v___x_720_;
}
else
{
lean_object* v___x_721_; 
v___x_721_ = l_Lean_Elab_Command_elabCommand(v___x_715_, v_a_706_, v_a_707_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_722_; lean_object* v_infoState_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v_trees_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref_known(v___x_721_, 1);
v___x_722_ = lean_st_ref_get(v_a_707_);
v_infoState_723_ = lean_ctor_get(v___x_722_, 8);
lean_inc_ref(v_infoState_723_);
lean_dec(v___x_722_);
v___x_724_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_723_);
v___x_725_ = lean_task_get_own(v___x_724_);
v_trees_726_ = lean_ctor_get(v___x_725_, 2);
lean_inc_ref(v_trees_726_);
lean_dec(v___x_725_);
v___x_727_ = lean_box(0);
v___x_728_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v_tk_713_, v_trees_726_, v___x_727_, v_a_706_, v_a_707_);
lean_dec_ref(v_trees_726_);
lean_dec(v_tk_713_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v___x_728_, 0);
lean_dec(v_unused_736_);
v___x_730_ = v___x_728_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_dec(v___x_728_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_727_);
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_727_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
else
{
return v___x_728_;
}
}
else
{
lean_dec(v_tk_713_);
return v___x_721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed(lean_object* v_x_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(v_x_737_, v_a_738_, v_a_739_);
lean_dec(v_a_739_);
lean_dec_ref(v_a_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4(lean_object* v_msgData_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg(v_msgData_742_, v___y_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4(v_msgData_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1(){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_763_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_764_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
v___x_765_ = ((lean_object*)(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4));
v___x_766_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed), 4, 0);
v___x_767_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_763_, v___x_764_, v___x_765_, v___x_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___boxed(lean_object* v_a_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
return v_res_769_;
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
