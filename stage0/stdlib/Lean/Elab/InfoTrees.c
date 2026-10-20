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
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_36_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_37_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_38_ = lean_unsigned_to_nat(0u);
v___x_39_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_38_);
lean_ctor_set(v___x_39_, 2, v___x_38_);
lean_ctor_set(v___x_39_, 3, v___x_38_);
lean_ctor_set(v___x_39_, 4, v___x_37_);
lean_ctor_set(v___x_39_, 5, v___x_37_);
lean_ctor_set(v___x_39_, 6, v___x_37_);
lean_ctor_set(v___x_39_, 7, v___x_37_);
lean_ctor_set(v___x_39_, 8, v___x_37_);
lean_ctor_set(v___x_39_, 9, v___x_37_);
lean_ctor_set(v___x_39_, 10, v___x_37_);
lean_ctor_set(v___x_39_, 11, v___x_36_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_40_ = lean_unsigned_to_nat(32u);
v___x_41_ = lean_mk_empty_array_with_capacity(v___x_40_);
v___x_42_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4(void){
_start:
{
size_t v___x_43_; lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_43_ = ((size_t)5ULL);
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_unsigned_to_nat(32u);
v___x_46_ = lean_mk_empty_array_with_capacity(v___x_45_);
v___x_47_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__3);
v___x_48_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v___x_46_);
lean_ctor_set(v___x_48_, 2, v___x_44_);
lean_ctor_set(v___x_48_, 3, v___x_44_);
lean_ctor_set_usize(v___x_48_, 4, v___x_43_);
return v___x_48_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_49_ = lean_box(1);
v___x_50_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__4);
v___x_51_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__1);
v___x_52_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
lean_ctor_set(v___x_52_, 1, v___x_50_);
lean_ctor_set(v___x_52_, 2, v___x_49_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg(lean_object* v_msgData_53_, lean_object* v___y_54_){
_start:
{
lean_object* v___x_56_; lean_object* v_env_57_; uint8_t v___x_58_; lean_object* v_env_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v_scopes_62_; lean_object* v___x_63_; lean_object* v_opts_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; 
v___x_56_ = lean_st_ref_get(v___y_54_);
v_env_57_ = lean_ctor_get(v___x_56_, 0);
lean_inc_ref(v_env_57_);
lean_dec(v___x_56_);
v___x_58_ = 0;
v_env_59_ = l_Lean_Environment_setRecordingDeps(v_env_57_, v___x_58_);
v___x_60_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_61_ = lean_st_ref_get(v___y_54_);
v_scopes_62_ = lean_ctor_get(v___x_61_, 2);
lean_inc(v_scopes_62_);
lean_dec(v___x_61_);
v___x_63_ = l_List_head_x21___redArg(v___x_60_, v_scopes_62_);
lean_dec(v_scopes_62_);
v_opts_64_ = lean_ctor_get(v___x_63_, 1);
lean_inc_ref(v_opts_64_);
lean_dec(v___x_63_);
v___x_65_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__2);
v___x_66_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___closed__5);
v___x_67_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_67_, 0, v_env_59_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
lean_ctor_set(v___x_67_, 2, v___x_66_);
lean_ctor_set(v___x_67_, 3, v_opts_64_);
v___x_68_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_msgData_53_);
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_msgData_70_, lean_object* v___y_71_, lean_object* v___y_72_){
_start:
{
lean_object* v_res_73_; 
v_res_73_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg(v_msgData_70_, v___y_71_);
lean_dec(v___y_71_);
return v_res_73_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0(uint8_t v_suppressElabErrors_75_, lean_object* v_x_76_){
_start:
{
if (lean_obj_tag(v_x_76_) == 1)
{
lean_object* v_pre_77_; 
v_pre_77_ = lean_ctor_get(v_x_76_, 0);
if (lean_obj_tag(v_pre_77_) == 0)
{
lean_object* v_str_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_str_78_ = lean_ctor_get(v_x_76_, 1);
v___x_79_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___closed__0));
v___x_80_ = lean_string_dec_eq(v_str_78_, v___x_79_);
if (v___x_80_ == 0)
{
return v___x_80_;
}
else
{
return v_suppressElabErrors_75_;
}
}
else
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
else
{
uint8_t v___x_82_; 
v___x_82_ = 0;
return v___x_82_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___boxed(lean_object* v_suppressElabErrors_83_, lean_object* v_x_84_){
_start:
{
uint8_t v_suppressElabErrors_boxed_85_; uint8_t v_res_86_; lean_object* v_r_87_; 
v_suppressElabErrors_boxed_85_ = lean_unbox(v_suppressElabErrors_83_);
v_res_86_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0(v_suppressElabErrors_boxed_85_, v_x_84_);
lean_dec(v_x_84_);
v_r_87_ = lean_box(v_res_86_);
return v_r_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(lean_object* v_ref_89_, lean_object* v_msgData_90_, uint8_t v_severity_91_, uint8_t v_isSilent_92_, lean_object* v___y_93_, lean_object* v___y_94_){
_start:
{
lean_object* v___y_97_; uint8_t v___y_98_; uint8_t v___y_99_; lean_object* v___y_100_; lean_object* v___y_101_; lean_object* v___y_102_; lean_object* v___y_103_; lean_object* v___y_104_; lean_object* v___y_162_; uint8_t v___y_163_; uint8_t v___y_164_; lean_object* v___y_165_; lean_object* v___y_188_; uint8_t v___y_189_; uint8_t v___y_190_; lean_object* v___y_191_; uint8_t v___y_195_; uint8_t v___y_196_; uint8_t v___x_211_; uint8_t v___y_213_; uint8_t v___x_223_; 
v___x_211_ = 2;
v___x_223_ = l_Lean_instBEqMessageSeverity_beq(v_severity_91_, v___x_211_);
if (v___x_223_ == 0)
{
v___y_213_ = v___x_223_;
goto v___jp_212_;
}
else
{
uint8_t v___x_224_; 
lean_inc_ref(v_msgData_90_);
v___x_224_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_90_);
if (v___x_224_ == 0)
{
v___y_213_ = v___x_224_;
goto v___jp_212_;
}
else
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec_ref(v_msgData_90_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
return v___x_226_;
}
}
v___jp_96_:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_Elab_Command_getScope___redArg(v___y_104_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v_currNamespace_107_; lean_object* v___x_108_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v_currNamespace_107_ = lean_ctor_get(v_a_106_, 2);
lean_inc(v_currNamespace_107_);
lean_dec(v_a_106_);
v___x_108_ = l_Lean_Elab_Command_getScope___redArg(v___y_104_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_144_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_144_ == 0)
{
v___x_111_ = v___x_108_;
v_isShared_112_ = v_isSharedCheck_144_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_a_109_);
lean_dec(v___x_108_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_144_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v_openDecls_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v_env_118_; lean_object* v_messages_119_; lean_object* v_scopes_120_; lean_object* v_usedQuotCtxts_121_; lean_object* v_nextMacroScope_122_; lean_object* v_maxRecDepth_123_; lean_object* v_ngen_124_; lean_object* v_auxDeclNGen_125_; lean_object* v_infoState_126_; lean_object* v_traceState_127_; lean_object* v_snapshotTasks_128_; lean_object* v_prevLinterStates_129_; lean_object* v_codeQualityEntryTasks_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_143_; 
v_openDecls_113_ = lean_ctor_get(v_a_109_, 3);
lean_inc(v_openDecls_113_);
lean_dec(v_a_109_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_currNamespace_107_);
lean_ctor_set(v___x_114_, 1, v_openDecls_113_);
v___x_115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___y_97_);
lean_inc_ref(v___y_102_);
lean_inc_ref(v___y_103_);
v___x_116_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_116_, 0, v___y_103_);
lean_ctor_set(v___x_116_, 1, v___y_101_);
lean_ctor_set(v___x_116_, 2, v___y_100_);
lean_ctor_set(v___x_116_, 3, v___y_102_);
lean_ctor_set(v___x_116_, 4, v___x_115_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*5, v___y_98_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*5 + 1, v___y_99_);
lean_ctor_set_uint8(v___x_116_, sizeof(void*)*5 + 2, v_isSilent_92_);
v___x_117_ = lean_st_ref_take(v___y_104_);
v_env_118_ = lean_ctor_get(v___x_117_, 0);
v_messages_119_ = lean_ctor_get(v___x_117_, 1);
v_scopes_120_ = lean_ctor_get(v___x_117_, 2);
v_usedQuotCtxts_121_ = lean_ctor_get(v___x_117_, 3);
v_nextMacroScope_122_ = lean_ctor_get(v___x_117_, 4);
v_maxRecDepth_123_ = lean_ctor_get(v___x_117_, 5);
v_ngen_124_ = lean_ctor_get(v___x_117_, 6);
v_auxDeclNGen_125_ = lean_ctor_get(v___x_117_, 7);
v_infoState_126_ = lean_ctor_get(v___x_117_, 8);
v_traceState_127_ = lean_ctor_get(v___x_117_, 9);
v_snapshotTasks_128_ = lean_ctor_get(v___x_117_, 10);
v_prevLinterStates_129_ = lean_ctor_get(v___x_117_, 11);
v_codeQualityEntryTasks_130_ = lean_ctor_get(v___x_117_, 12);
v_isSharedCheck_143_ = !lean_is_exclusive(v___x_117_);
if (v_isSharedCheck_143_ == 0)
{
v___x_132_ = v___x_117_;
v_isShared_133_ = v_isSharedCheck_143_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_codeQualityEntryTasks_130_);
lean_inc(v_prevLinterStates_129_);
lean_inc(v_snapshotTasks_128_);
lean_inc(v_traceState_127_);
lean_inc(v_infoState_126_);
lean_inc(v_auxDeclNGen_125_);
lean_inc(v_ngen_124_);
lean_inc(v_maxRecDepth_123_);
lean_inc(v_nextMacroScope_122_);
lean_inc(v_usedQuotCtxts_121_);
lean_inc(v_scopes_120_);
lean_inc(v_messages_119_);
lean_inc(v_env_118_);
lean_dec(v___x_117_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_143_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_134_ = lean_box(0);
v___x_135_ = l_Lean_MessageLog_add(v___x_116_, v_messages_119_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_135_);
v___x_137_ = v___x_132_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 13, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_env_118_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v___x_135_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_scopes_120_);
lean_ctor_set(v_reuseFailAlloc_142_, 3, v_usedQuotCtxts_121_);
lean_ctor_set(v_reuseFailAlloc_142_, 4, v_nextMacroScope_122_);
lean_ctor_set(v_reuseFailAlloc_142_, 5, v_maxRecDepth_123_);
lean_ctor_set(v_reuseFailAlloc_142_, 6, v_ngen_124_);
lean_ctor_set(v_reuseFailAlloc_142_, 7, v_auxDeclNGen_125_);
lean_ctor_set(v_reuseFailAlloc_142_, 8, v_infoState_126_);
lean_ctor_set(v_reuseFailAlloc_142_, 9, v_traceState_127_);
lean_ctor_set(v_reuseFailAlloc_142_, 10, v_snapshotTasks_128_);
lean_ctor_set(v_reuseFailAlloc_142_, 11, v_prevLinterStates_129_);
lean_ctor_set(v_reuseFailAlloc_142_, 12, v_codeQualityEntryTasks_130_);
v___x_137_ = v_reuseFailAlloc_142_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_st_ref_put(v___y_104_, v___x_137_);
if (v_isShared_112_ == 0)
{
lean_ctor_set(v___x_111_, 0, v___x_134_);
v___x_140_ = v___x_111_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v___x_134_);
v___x_140_ = v_reuseFailAlloc_141_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
return v___x_140_;
}
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v_currNamespace_107_);
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_97_);
v_a_145_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_108_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_108_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_dec_ref(v___y_101_);
lean_dec(v___y_100_);
lean_dec_ref(v___y_97_);
v_a_153_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_105_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_105_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
v___jp_161_:
{
lean_object* v_fileName_166_; lean_object* v_fileMap_167_; uint8_t v_suppressElabErrors_168_; lean_object* v___x_169_; lean_object* v___f_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_186_; 
v_fileName_166_ = lean_ctor_get(v___y_93_, 0);
v_fileMap_167_ = lean_ctor_get(v___y_93_, 1);
v_suppressElabErrors_168_ = lean_ctor_get_uint8(v___y_93_, sizeof(void*)*10);
v___x_169_ = lean_box(v_suppressElabErrors_168_);
v___f_170_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___lam__0___boxed), 2, 1);
lean_closure_set(v___f_170_, 0, v___x_169_);
v___x_171_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_90_);
v___x_172_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg(v___x_171_, v___y_94_);
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_186_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_186_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_186_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_186_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
lean_inc_ref_n(v_fileMap_167_, 2);
v___x_177_ = l_Lean_FileMap_toPosition(v_fileMap_167_, v___y_162_);
lean_dec(v___y_162_);
v___x_178_ = l_Lean_FileMap_toPosition(v_fileMap_167_, v___y_165_);
lean_dec(v___y_165_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
v___x_180_ = ((lean_object*)(l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___closed__0));
if (v_suppressElabErrors_168_ == 0)
{
lean_del_object(v___x_175_);
lean_dec_ref(v___f_170_);
v___y_97_ = v_a_173_;
v___y_98_ = v___y_163_;
v___y_99_ = v___y_164_;
v___y_100_ = v___x_179_;
v___y_101_ = v___x_177_;
v___y_102_ = v___x_180_;
v___y_103_ = v_fileName_166_;
v___y_104_ = v___y_94_;
goto v___jp_96_;
}
else
{
uint8_t v___x_181_; 
lean_inc(v_a_173_);
v___x_181_ = l_Lean_MessageData_hasTag(v___f_170_, v_a_173_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; lean_object* v___x_184_; 
lean_dec_ref_known(v___x_179_, 1);
lean_dec_ref(v___x_177_);
lean_dec(v_a_173_);
v___x_182_ = lean_box(0);
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v___x_182_);
v___x_184_ = v___x_175_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v___x_182_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
else
{
lean_del_object(v___x_175_);
v___y_97_ = v_a_173_;
v___y_98_ = v___y_163_;
v___y_99_ = v___y_164_;
v___y_100_ = v___x_179_;
v___y_101_ = v___x_177_;
v___y_102_ = v___x_180_;
v___y_103_ = v_fileName_166_;
v___y_104_ = v___y_94_;
goto v___jp_96_;
}
}
}
}
v___jp_187_:
{
lean_object* v___x_192_; 
v___x_192_ = l_Lean_Syntax_getTailPos_x3f(v___y_188_, v___y_189_);
lean_dec(v___y_188_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_inc(v___y_191_);
v___y_162_ = v___y_191_;
v___y_163_ = v___y_189_;
v___y_164_ = v___y_190_;
v___y_165_ = v___y_191_;
goto v___jp_161_;
}
else
{
lean_object* v_val_193_; 
v_val_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v___x_192_, 1);
v___y_162_ = v___y_191_;
v___y_163_ = v___y_189_;
v___y_164_ = v___y_190_;
v___y_165_ = v_val_193_;
goto v___jp_161_;
}
}
v___jp_194_:
{
lean_object* v___x_197_; 
v___x_197_ = l_Lean_Elab_Command_getRef___redArg(v___y_93_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v_ref_199_; lean_object* v___x_200_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref_known(v___x_197_, 1);
v_ref_199_ = l_Lean_replaceRef(v_ref_89_, v_a_198_);
lean_dec(v_a_198_);
v___x_200_ = l_Lean_Syntax_getPos_x3f(v_ref_199_, v___y_195_);
if (lean_obj_tag(v___x_200_) == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___y_188_ = v_ref_199_;
v___y_189_ = v___y_195_;
v___y_190_ = v___y_196_;
v___y_191_ = v___x_201_;
goto v___jp_187_;
}
else
{
lean_object* v_val_202_; 
v_val_202_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_val_202_);
lean_dec_ref_known(v___x_200_, 1);
v___y_188_ = v_ref_199_;
v___y_189_ = v___y_195_;
v___y_190_ = v___y_196_;
v___y_191_ = v_val_202_;
goto v___jp_187_;
}
}
else
{
lean_object* v_a_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_210_; 
lean_dec_ref(v_msgData_90_);
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
lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v_scopes_216_; lean_object* v___x_217_; lean_object* v_opts_218_; uint8_t v___x_219_; uint8_t v___x_220_; 
v___x_214_ = l_Lean_Elab_Command_instInhabitedScope_default;
v___x_215_ = lean_st_ref_get(v___y_94_);
v_scopes_216_ = lean_ctor_get(v___x_215_, 2);
lean_inc(v_scopes_216_);
lean_dec(v___x_215_);
v___x_217_ = l_List_head_x21___redArg(v___x_214_, v_scopes_216_);
lean_dec(v_scopes_216_);
v_opts_218_ = lean_ctor_get(v___x_217_, 1);
lean_inc_ref(v_opts_218_);
lean_dec(v___x_217_);
v___x_219_ = 1;
v___x_220_ = l_Lean_instBEqMessageSeverity_beq(v_severity_91_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec_ref(v_opts_218_);
v___y_195_ = v___y_213_;
v___y_196_ = v_severity_91_;
goto v___jp_194_;
}
else
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = l_Lean_warningAsError;
v___x_222_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__5(v_opts_218_, v___x_221_);
lean_dec_ref(v_opts_218_);
if (v___x_222_ == 0)
{
v___y_195_ = v___y_213_;
v___y_196_ = v_severity_91_;
goto v___jp_194_;
}
else
{
v___y_195_ = v___y_213_;
v___y_196_ = v___x_211_;
goto v___jp_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3___boxed(lean_object* v_ref_227_, lean_object* v_msgData_228_, lean_object* v_severity_229_, lean_object* v_isSilent_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
uint8_t v_severity_boxed_234_; uint8_t v_isSilent_boxed_235_; lean_object* v_res_236_; 
v_severity_boxed_234_ = lean_unbox(v_severity_229_);
v_isSilent_boxed_235_ = lean_unbox(v_isSilent_230_);
v_res_236_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_ref_227_, v_msgData_228_, v_severity_boxed_234_, v_isSilent_boxed_235_, v___y_231_, v___y_232_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec(v_ref_227_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(lean_object* v_msgData_237_, uint8_t v_severity_238_, uint8_t v_isSilent_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_Elab_Command_getRef___redArg(v___y_240_);
if (lean_obj_tag(v___x_243_) == 0)
{
lean_object* v_a_244_; lean_object* v___x_245_; 
v_a_244_ = lean_ctor_get(v___x_243_, 0);
lean_inc(v_a_244_);
lean_dec_ref_known(v___x_243_, 1);
v___x_245_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_a_244_, v_msgData_237_, v_severity_238_, v_isSilent_239_, v___y_240_, v___y_241_);
lean_dec(v_a_244_);
return v___x_245_;
}
else
{
lean_object* v_a_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_253_; 
lean_dec_ref(v_msgData_237_);
v_a_246_ = lean_ctor_get(v___x_243_, 0);
v_isSharedCheck_253_ = !lean_is_exclusive(v___x_243_);
if (v_isSharedCheck_253_ == 0)
{
v___x_248_ = v___x_243_;
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_a_246_);
lean_dec(v___x_243_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_253_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_251_; 
if (v_isShared_249_ == 0)
{
v___x_251_ = v___x_248_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v_a_246_);
v___x_251_ = v_reuseFailAlloc_252_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
return v___x_251_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1___boxed(lean_object* v_msgData_254_, lean_object* v_severity_255_, lean_object* v_isSilent_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
uint8_t v_severity_boxed_260_; uint8_t v_isSilent_boxed_261_; lean_object* v_res_262_; 
v_severity_boxed_260_ = lean_unbox(v_severity_255_);
v_isSilent_boxed_261_ = lean_unbox(v_isSilent_256_);
v_res_262_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_msgData_254_, v_severity_boxed_260_, v_isSilent_boxed_261_, v___y_257_, v___y_258_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(lean_object* v_msgData_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
uint8_t v___x_267_; uint8_t v___x_268_; lean_object* v___x_269_; 
v___x_267_ = 2;
v___x_268_ = 0;
v___x_269_ = l_Lean_log___at___00Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1_spec__1(v_msgData_263_, v___x_267_, v___x_268_, v___y_264_, v___y_265_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1___boxed(lean_object* v_msgData_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v_msgData_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(lean_object* v_ref_275_, lean_object* v_msgData_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
uint8_t v___x_280_; uint8_t v___x_281_; lean_object* v___x_282_; 
v___x_280_ = 0;
v___x_281_ = 0;
v___x_282_ = l_Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3(v_ref_275_, v_msgData_276_, v___x_280_, v___x_281_, v___y_277_, v___y_278_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2___boxed(lean_object* v_ref_283_, lean_object* v_msgData_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_ref_283_, v_msgData_284_, v___y_285_, v___y_286_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v_ref_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10(lean_object* v_tk_292_, lean_object* v_as_293_, size_t v_sz_294_, size_t v_i_295_, lean_object* v_b_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
uint8_t v___x_300_; 
v___x_300_ = lean_usize_dec_lt(v_i_295_, v_sz_294_);
if (v___x_300_ == 0)
{
lean_object* v___x_301_; 
v___x_301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_301_, 0, v_b_296_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; lean_object* v_a_303_; lean_object* v___x_304_; 
lean_dec_ref(v_b_296_);
v___x_302_ = lean_box(0);
v_a_303_ = lean_array_uget_borrowed(v_as_293_, v_i_295_);
lean_inc(v_a_303_);
v___x_304_ = l_Lean_Elab_InfoTree_format(v_a_303_, v___x_302_);
if (lean_obj_tag(v___x_304_) == 0)
{
lean_object* v_a_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v_a_305_ = lean_ctor_get(v___x_304_, 0);
lean_inc(v_a_305_);
lean_dec_ref_known(v___x_304_, 1);
v___x_306_ = l_Lean_MessageData_ofFormat(v_a_305_);
v___x_307_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_292_, v___x_306_, v___y_297_, v___y_298_);
if (lean_obj_tag(v___x_307_) == 0)
{
lean_object* v___x_308_; size_t v___x_309_; size_t v___x_310_; 
lean_dec_ref_known(v___x_307_, 1);
v___x_308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___closed__0));
v___x_309_ = ((size_t)1ULL);
v___x_310_ = lean_usize_add(v_i_295_, v___x_309_);
v_i_295_ = v___x_310_;
v_b_296_ = v___x_308_;
goto _start;
}
else
{
lean_object* v_a_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_319_; 
v_a_312_ = lean_ctor_get(v___x_307_, 0);
v_isSharedCheck_319_ = !lean_is_exclusive(v___x_307_);
if (v_isSharedCheck_319_ == 0)
{
v___x_314_ = v___x_307_;
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_a_312_);
lean_dec(v___x_307_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_319_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_317_; 
if (v_isShared_315_ == 0)
{
v___x_317_ = v___x_314_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_318_; 
v_reuseFailAlloc_318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_318_, 0, v_a_312_);
v___x_317_ = v_reuseFailAlloc_318_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
return v___x_317_;
}
}
}
}
else
{
lean_object* v_a_320_; lean_object* v___x_322_; uint8_t v_isShared_323_; uint8_t v_isSharedCheck_332_; 
v_a_320_ = lean_ctor_get(v___x_304_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_304_);
if (v_isSharedCheck_332_ == 0)
{
v___x_322_ = v___x_304_;
v_isShared_323_ = v_isSharedCheck_332_;
goto v_resetjp_321_;
}
else
{
lean_inc(v_a_320_);
lean_dec(v___x_304_);
v___x_322_ = lean_box(0);
v_isShared_323_ = v_isSharedCheck_332_;
goto v_resetjp_321_;
}
v_resetjp_321_:
{
lean_object* v_ref_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_330_; 
v_ref_324_ = lean_ctor_get(v___y_297_, 7);
v___x_325_ = lean_io_error_to_string(v_a_320_);
v___x_326_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
v___x_327_ = l_Lean_MessageData_ofFormat(v___x_326_);
lean_inc(v_ref_324_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v_ref_324_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
if (v_isShared_323_ == 0)
{
lean_ctor_set(v___x_322_, 0, v___x_328_);
v___x_330_ = v___x_322_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___boxed(lean_object* v_tk_333_, lean_object* v_as_334_, lean_object* v_sz_335_, lean_object* v_i_336_, lean_object* v_b_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
size_t v_sz_boxed_341_; size_t v_i_boxed_342_; lean_object* v_res_343_; 
v_sz_boxed_341_ = lean_unbox_usize(v_sz_335_);
lean_dec(v_sz_335_);
v_i_boxed_342_ = lean_unbox_usize(v_i_336_);
lean_dec(v_i_336_);
v_res_343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10(v_tk_333_, v_as_334_, v_sz_boxed_341_, v_i_boxed_342_, v_b_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec_ref(v_as_334_);
lean_dec(v_tk_333_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9(lean_object* v_tk_344_, lean_object* v_as_345_, size_t v_sz_346_, size_t v_i_347_, lean_object* v_b_348_, lean_object* v___y_349_, lean_object* v___y_350_){
_start:
{
uint8_t v___x_352_; 
v___x_352_ = lean_usize_dec_lt(v_i_347_, v_sz_346_);
if (v___x_352_ == 0)
{
lean_object* v___x_353_; 
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v_b_348_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; lean_object* v_a_355_; lean_object* v___x_356_; 
lean_dec_ref(v_b_348_);
v___x_354_ = lean_box(0);
v_a_355_ = lean_array_uget_borrowed(v_as_345_, v_i_347_);
lean_inc(v_a_355_);
v___x_356_ = l_Lean_Elab_InfoTree_format(v_a_355_, v___x_354_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_a_357_);
lean_dec_ref_known(v___x_356_, 1);
v___x_358_ = l_Lean_MessageData_ofFormat(v_a_357_);
v___x_359_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_344_, v___x_358_, v___y_349_, v___y_350_);
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v___x_360_; size_t v___x_361_; size_t v___x_362_; lean_object* v___x_363_; 
lean_dec_ref_known(v___x_359_, 1);
v___x_360_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10___closed__0));
v___x_361_ = ((size_t)1ULL);
v___x_362_ = lean_usize_add(v_i_347_, v___x_361_);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9_spec__10(v_tk_344_, v_as_345_, v_sz_346_, v___x_362_, v___x_360_, v___y_349_, v___y_350_);
return v___x_363_;
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
v_a_364_ = lean_ctor_get(v___x_359_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_359_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_359_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v_a_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_384_; 
v_a_372_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_384_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_384_ == 0)
{
v___x_374_ = v___x_356_;
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_a_372_);
lean_dec(v___x_356_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v_ref_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v_ref_376_ = lean_ctor_get(v___y_349_, 7);
v___x_377_ = lean_io_error_to_string(v_a_372_);
v___x_378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_378_, 0, v___x_377_);
v___x_379_ = l_Lean_MessageData_ofFormat(v___x_378_);
lean_inc(v_ref_376_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_ref_376_);
lean_ctor_set(v___x_380_, 1, v___x_379_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 0, v___x_380_);
v___x_382_ = v___x_374_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9___boxed(lean_object* v_tk_385_, lean_object* v_as_386_, lean_object* v_sz_387_, lean_object* v_i_388_, lean_object* v_b_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
size_t v_sz_boxed_393_; size_t v_i_boxed_394_; lean_object* v_res_395_; 
v_sz_boxed_393_ = lean_unbox_usize(v_sz_387_);
lean_dec(v_sz_387_);
v_i_boxed_394_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9(v_tk_385_, v_as_386_, v_sz_boxed_393_, v_i_boxed_394_, v_b_389_, v___y_390_, v___y_391_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
lean_dec_ref(v_as_386_);
lean_dec(v_tk_385_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5(lean_object* v_init_396_, lean_object* v_tk_397_, lean_object* v_n_398_, lean_object* v_b_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
if (lean_obj_tag(v_n_398_) == 0)
{
lean_object* v_cs_403_; lean_object* v___x_404_; lean_object* v___x_405_; size_t v_sz_406_; size_t v___x_407_; lean_object* v___x_408_; 
v_cs_403_ = lean_ctor_get(v_n_398_, 0);
v___x_404_ = lean_box(0);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
lean_ctor_set(v___x_405_, 1, v_b_399_);
v_sz_406_ = lean_array_size(v_cs_403_);
v___x_407_ = ((size_t)0ULL);
v___x_408_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8(v_init_396_, v_tk_397_, v_cs_403_, v_sz_406_, v___x_407_, v___x_405_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_408_) == 0)
{
lean_object* v_a_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_423_; 
v_a_409_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_423_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_423_ == 0)
{
v___x_411_ = v___x_408_;
v_isShared_412_ = v_isSharedCheck_423_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_a_409_);
lean_dec(v___x_408_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_423_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_fst_413_; 
v_fst_413_ = lean_ctor_get(v_a_409_, 0);
if (lean_obj_tag(v_fst_413_) == 0)
{
lean_object* v_snd_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v_snd_414_ = lean_ctor_get(v_a_409_, 1);
lean_inc(v_snd_414_);
lean_dec(v_a_409_);
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v_snd_414_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v___x_415_);
v___x_417_ = v___x_411_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v___x_415_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
else
{
lean_object* v_val_419_; lean_object* v___x_421_; 
lean_inc_ref(v_fst_413_);
lean_dec(v_a_409_);
v_val_419_ = lean_ctor_get(v_fst_413_, 0);
lean_inc(v_val_419_);
lean_dec_ref_known(v_fst_413_, 1);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 0, v_val_419_);
v___x_421_ = v___x_411_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_val_419_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
else
{
lean_object* v_a_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_431_; 
v_a_424_ = lean_ctor_get(v___x_408_, 0);
v_isSharedCheck_431_ = !lean_is_exclusive(v___x_408_);
if (v_isSharedCheck_431_ == 0)
{
v___x_426_ = v___x_408_;
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_a_424_);
lean_dec(v___x_408_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_431_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_429_; 
if (v_isShared_427_ == 0)
{
v___x_429_ = v___x_426_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_a_424_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
else
{
lean_object* v_vs_432_; lean_object* v___x_433_; lean_object* v___x_434_; size_t v_sz_435_; size_t v___x_436_; lean_object* v___x_437_; 
v_vs_432_ = lean_ctor_get(v_n_398_, 0);
v___x_433_ = lean_box(0);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v_b_399_);
v_sz_435_ = lean_array_size(v_vs_432_);
v___x_436_ = ((size_t)0ULL);
v___x_437_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__9(v_tk_397_, v_vs_432_, v_sz_435_, v___x_436_, v___x_434_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_437_) == 0)
{
lean_object* v_a_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_452_; 
v_a_438_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_452_ == 0)
{
v___x_440_ = v___x_437_;
v_isShared_441_ = v_isSharedCheck_452_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_a_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_452_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_fst_442_; 
v_fst_442_ = lean_ctor_get(v_a_438_, 0);
if (lean_obj_tag(v_fst_442_) == 0)
{
lean_object* v_snd_443_; lean_object* v___x_444_; lean_object* v___x_446_; 
v_snd_443_ = lean_ctor_get(v_a_438_, 1);
lean_inc(v_snd_443_);
lean_dec(v_a_438_);
v___x_444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_444_, 0, v_snd_443_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v___x_444_);
v___x_446_ = v___x_440_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
else
{
lean_object* v_val_448_; lean_object* v___x_450_; 
lean_inc_ref(v_fst_442_);
lean_dec(v_a_438_);
v_val_448_ = lean_ctor_get(v_fst_442_, 0);
lean_inc(v_val_448_);
lean_dec_ref_known(v_fst_442_, 1);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 0, v_val_448_);
v___x_450_ = v___x_440_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_val_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
return v___x_450_;
}
}
}
}
else
{
lean_object* v_a_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_460_; 
v_a_453_ = lean_ctor_get(v___x_437_, 0);
v_isSharedCheck_460_ = !lean_is_exclusive(v___x_437_);
if (v_isSharedCheck_460_ == 0)
{
v___x_455_ = v___x_437_;
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_a_453_);
lean_dec(v___x_437_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_460_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_458_; 
if (v_isShared_456_ == 0)
{
v___x_458_ = v___x_455_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_a_453_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8(lean_object* v_init_461_, lean_object* v_tk_462_, lean_object* v_as_463_, size_t v_sz_464_, size_t v_i_465_, lean_object* v_b_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
uint8_t v___x_470_; 
v___x_470_ = lean_usize_dec_lt(v_i_465_, v_sz_464_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
v___x_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_471_, 0, v_b_466_);
return v___x_471_;
}
else
{
lean_object* v_snd_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_506_; 
v_snd_472_ = lean_ctor_get(v_b_466_, 1);
v_isSharedCheck_506_ = !lean_is_exclusive(v_b_466_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; 
v_unused_507_ = lean_ctor_get(v_b_466_, 0);
lean_dec(v_unused_507_);
v___x_474_ = v_b_466_;
v_isShared_475_ = v_isSharedCheck_506_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_snd_472_);
lean_dec(v_b_466_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_506_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v_a_477_; lean_object* v___x_478_; 
v___x_476_ = lean_box(0);
v_a_477_ = lean_array_uget_borrowed(v_as_463_, v_i_465_);
lean_inc(v_snd_472_);
v___x_478_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5(v_init_461_, v_tk_462_, v_a_477_, v_snd_472_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_497_; 
v_a_479_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_497_ == 0)
{
v___x_481_ = v___x_478_;
v_isShared_482_ = v_isSharedCheck_497_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_a_479_);
lean_dec(v___x_478_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_497_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
if (lean_obj_tag(v_a_479_) == 0)
{
lean_object* v___x_483_; lean_object* v___x_485_; 
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v_a_479_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v___x_483_);
v___x_485_ = v___x_474_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v___x_483_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_snd_472_);
v___x_485_ = v_reuseFailAlloc_489_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_487_; 
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 0, v___x_485_);
v___x_487_ = v___x_481_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v___x_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
else
{
lean_object* v_a_490_; lean_object* v___x_492_; 
lean_del_object(v___x_481_);
lean_dec(v_snd_472_);
v_a_490_ = lean_ctor_get(v_a_479_, 0);
lean_inc(v_a_490_);
lean_dec_ref_known(v_a_479_, 1);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v_a_490_);
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_492_ = v___x_474_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_a_490_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
size_t v___x_493_; size_t v___x_494_; 
v___x_493_ = ((size_t)1ULL);
v___x_494_ = lean_usize_add(v_i_465_, v___x_493_);
v_i_465_ = v___x_494_;
v_b_466_ = v___x_492_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
lean_del_object(v___x_474_);
lean_dec(v_snd_472_);
v_a_498_ = lean_ctor_get(v___x_478_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_478_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_478_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_478_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8___boxed(lean_object* v_init_508_, lean_object* v_tk_509_, lean_object* v_as_510_, lean_object* v_sz_511_, lean_object* v_i_512_, lean_object* v_b_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
size_t v_sz_boxed_517_; size_t v_i_boxed_518_; lean_object* v_res_519_; 
v_sz_boxed_517_ = lean_unbox_usize(v_sz_511_);
lean_dec(v_sz_511_);
v_i_boxed_518_ = lean_unbox_usize(v_i_512_);
lean_dec(v_i_512_);
v_res_519_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5_spec__8(v_init_508_, v_tk_509_, v_as_510_, v_sz_boxed_517_, v_i_boxed_518_, v_b_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec_ref(v_as_510_);
lean_dec(v_tk_509_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5___boxed(lean_object* v_init_520_, lean_object* v_tk_521_, lean_object* v_n_522_, lean_object* v_b_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5(v_init_520_, v_tk_521_, v_n_522_, v_b_523_, v___y_524_, v___y_525_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v_n_522_);
lean_dec(v_tk_521_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11(lean_object* v_tk_531_, lean_object* v_as_532_, size_t v_sz_533_, size_t v_i_534_, lean_object* v_b_535_, lean_object* v___y_536_, lean_object* v___y_537_){
_start:
{
uint8_t v___x_539_; 
v___x_539_ = lean_usize_dec_lt(v_i_534_, v_sz_533_);
if (v___x_539_ == 0)
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v_b_535_);
return v___x_540_;
}
else
{
lean_object* v___x_541_; lean_object* v_a_542_; lean_object* v___x_543_; 
lean_dec_ref(v_b_535_);
v___x_541_ = lean_box(0);
v_a_542_ = lean_array_uget_borrowed(v_as_532_, v_i_534_);
lean_inc(v_a_542_);
v___x_543_ = l_Lean_Elab_InfoTree_format(v_a_542_, v___x_541_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v_a_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_a_544_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_a_544_);
lean_dec_ref_known(v___x_543_, 1);
v___x_545_ = l_Lean_MessageData_ofFormat(v_a_544_);
v___x_546_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_531_, v___x_545_, v___y_536_, v___y_537_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; size_t v___x_548_; size_t v___x_549_; 
lean_dec_ref_known(v___x_546_, 1);
v___x_547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___closed__0));
v___x_548_ = ((size_t)1ULL);
v___x_549_ = lean_usize_add(v_i_534_, v___x_548_);
v_i_534_ = v___x_549_;
v_b_535_ = v___x_547_;
goto _start;
}
else
{
lean_object* v_a_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_558_; 
v_a_551_ = lean_ctor_get(v___x_546_, 0);
v_isSharedCheck_558_ = !lean_is_exclusive(v___x_546_);
if (v_isSharedCheck_558_ == 0)
{
v___x_553_ = v___x_546_;
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_a_551_);
lean_dec(v___x_546_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_558_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_554_ == 0)
{
v___x_556_ = v___x_553_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v_a_551_);
v___x_556_ = v_reuseFailAlloc_557_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
return v___x_556_;
}
}
}
}
else
{
lean_object* v_a_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_571_; 
v_a_559_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_571_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_571_ == 0)
{
v___x_561_ = v___x_543_;
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_a_559_);
lean_dec(v___x_543_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_571_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v_ref_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_569_; 
v_ref_563_ = lean_ctor_get(v___y_536_, 7);
v___x_564_ = lean_io_error_to_string(v_a_559_);
v___x_565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_565_, 0, v___x_564_);
v___x_566_ = l_Lean_MessageData_ofFormat(v___x_565_);
lean_inc(v_ref_563_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v_ref_563_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_567_);
v___x_569_ = v___x_561_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_567_);
v___x_569_ = v_reuseFailAlloc_570_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
return v___x_569_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___boxed(lean_object* v_tk_572_, lean_object* v_as_573_, lean_object* v_sz_574_, lean_object* v_i_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
size_t v_sz_boxed_580_; size_t v_i_boxed_581_; lean_object* v_res_582_; 
v_sz_boxed_580_ = lean_unbox_usize(v_sz_574_);
lean_dec(v_sz_574_);
v_i_boxed_581_ = lean_unbox_usize(v_i_575_);
lean_dec(v_i_575_);
v_res_582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11(v_tk_572_, v_as_573_, v_sz_boxed_580_, v_i_boxed_581_, v_b_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec_ref(v_as_573_);
lean_dec(v_tk_572_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(lean_object* v_tk_583_, lean_object* v_as_584_, size_t v_sz_585_, size_t v_i_586_, lean_object* v_b_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
uint8_t v___x_591_; 
v___x_591_ = lean_usize_dec_lt(v_i_586_, v_sz_585_);
if (v___x_591_ == 0)
{
lean_object* v___x_592_; 
v___x_592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_592_, 0, v_b_587_);
return v___x_592_;
}
else
{
lean_object* v___x_593_; lean_object* v_a_594_; lean_object* v___x_595_; 
lean_dec_ref(v_b_587_);
v___x_593_ = lean_box(0);
v_a_594_ = lean_array_uget_borrowed(v_as_584_, v_i_586_);
lean_inc(v_a_594_);
v___x_595_ = l_Lean_Elab_InfoTree_format(v_a_594_, v___x_593_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = l_Lean_MessageData_ofFormat(v_a_596_);
v___x_598_ = l_Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2(v_tk_583_, v___x_597_, v___y_588_, v___y_589_);
if (lean_obj_tag(v___x_598_) == 0)
{
lean_object* v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
lean_dec_ref_known(v___x_598_, 1);
v___x_599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11___closed__0));
v___x_600_ = ((size_t)1ULL);
v___x_601_ = lean_usize_add(v_i_586_, v___x_600_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6_spec__11(v_tk_583_, v_as_584_, v_sz_585_, v___x_601_, v___x_599_, v___y_588_, v___y_589_);
return v___x_602_;
}
else
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_598_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_598_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_623_; 
v_a_611_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_623_ == 0)
{
v___x_613_ = v___x_595_;
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_595_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_623_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_ref_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_621_; 
v_ref_615_ = lean_ctor_get(v___y_588_, 7);
v___x_616_ = lean_io_error_to_string(v_a_611_);
v___x_617_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
v___x_618_ = l_Lean_MessageData_ofFormat(v___x_617_);
lean_inc(v_ref_615_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v_ref_615_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_619_);
v___x_621_ = v___x_613_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_622_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
return v___x_621_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6___boxed(lean_object* v_tk_624_, lean_object* v_as_625_, lean_object* v_sz_626_, lean_object* v_i_627_, lean_object* v_b_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
size_t v_sz_boxed_632_; size_t v_i_boxed_633_; lean_object* v_res_634_; 
v_sz_boxed_632_ = lean_unbox_usize(v_sz_626_);
lean_dec(v_sz_626_);
v_i_boxed_633_ = lean_unbox_usize(v_i_627_);
lean_dec(v_i_627_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_tk_624_, v_as_625_, v_sz_boxed_632_, v_i_boxed_633_, v_b_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec_ref(v_as_625_);
lean_dec(v_tk_624_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(lean_object* v_tk_635_, lean_object* v_t_636_, lean_object* v_init_637_, lean_object* v___y_638_, lean_object* v___y_639_){
_start:
{
lean_object* v_root_641_; lean_object* v_tail_642_; lean_object* v___x_643_; 
v_root_641_ = lean_ctor_get(v_t_636_, 0);
v_tail_642_ = lean_ctor_get(v_t_636_, 1);
v___x_643_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__5(v_init_637_, v_tk_635_, v_root_641_, v_init_637_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_680_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_680_ == 0)
{
v___x_646_ = v___x_643_;
v_isShared_647_ = v_isSharedCheck_680_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_643_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_680_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
if (lean_obj_tag(v_a_644_) == 0)
{
lean_object* v_a_648_; lean_object* v___x_650_; 
v_a_648_ = lean_ctor_get(v_a_644_, 0);
lean_inc(v_a_648_);
lean_dec_ref_known(v_a_644_, 1);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v_a_648_);
v___x_650_ = v___x_646_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_a_648_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
else
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v___x_654_; size_t v_sz_655_; size_t v___x_656_; lean_object* v___x_657_; 
lean_del_object(v___x_646_);
v_a_652_ = lean_ctor_get(v_a_644_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v_a_644_, 1);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_a_652_);
v_sz_655_ = lean_array_size(v_tail_642_);
v___x_656_ = ((size_t)0ULL);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3_spec__6(v_tk_635_, v_tail_642_, v_sz_655_, v___x_656_, v___x_654_, v___y_638_, v___y_639_);
if (lean_obj_tag(v___x_657_) == 0)
{
lean_object* v_a_658_; lean_object* v___x_660_; uint8_t v_isShared_661_; uint8_t v_isSharedCheck_671_; 
v_a_658_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_671_ == 0)
{
v___x_660_ = v___x_657_;
v_isShared_661_ = v_isSharedCheck_671_;
goto v_resetjp_659_;
}
else
{
lean_inc(v_a_658_);
lean_dec(v___x_657_);
v___x_660_ = lean_box(0);
v_isShared_661_ = v_isSharedCheck_671_;
goto v_resetjp_659_;
}
v_resetjp_659_:
{
lean_object* v_fst_662_; 
v_fst_662_ = lean_ctor_get(v_a_658_, 0);
if (lean_obj_tag(v_fst_662_) == 0)
{
lean_object* v_snd_663_; lean_object* v___x_665_; 
v_snd_663_ = lean_ctor_get(v_a_658_, 1);
lean_inc(v_snd_663_);
lean_dec(v_a_658_);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v_snd_663_);
v___x_665_ = v___x_660_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_snd_663_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
else
{
lean_object* v_val_667_; lean_object* v___x_669_; 
lean_inc_ref(v_fst_662_);
lean_dec(v_a_658_);
v_val_667_ = lean_ctor_get(v_fst_662_, 0);
lean_inc(v_val_667_);
lean_dec_ref_known(v_fst_662_, 1);
if (v_isShared_661_ == 0)
{
lean_ctor_set(v___x_660_, 0, v_val_667_);
v___x_669_ = v___x_660_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_val_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
}
else
{
lean_object* v_a_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_679_; 
v_a_672_ = lean_ctor_get(v___x_657_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_657_);
if (v_isSharedCheck_679_ == 0)
{
v___x_674_ = v___x_657_;
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_a_672_);
lean_dec(v___x_657_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_679_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_677_; 
if (v_isShared_675_ == 0)
{
v___x_677_ = v___x_674_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v_a_672_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_643_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_643_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3___boxed(lean_object* v_tk_689_, lean_object* v_t_690_, lean_object* v_init_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v_tk_689_, v_t_690_, v_init_691_, v___y_692_, v___y_693_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec_ref(v_t_690_);
lean_dec(v_tk_689_);
return v_res_695_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5(void){
_start:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__4));
v___x_705_ = l_Lean_MessageData_ofFormat(v___x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(lean_object* v_x_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_710_; uint8_t v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
lean_inc(v_x_706_);
v___x_711_ = l_Lean_Syntax_isOfKind(v_x_706_, v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_dec(v_x_706_);
v___x_712_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__0___redArg();
return v___x_712_;
}
else
{
lean_object* v___x_713_; lean_object* v_tk_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v_infoState_718_; uint8_t v_enabled_719_; 
v___x_713_ = lean_unsigned_to_nat(0u);
v_tk_714_ = l_Lean_Syntax_getArg(v_x_706_, v___x_713_);
v___x_715_ = lean_unsigned_to_nat(2u);
v___x_716_ = l_Lean_Syntax_getArg(v_x_706_, v___x_715_);
lean_dec(v_x_706_);
v___x_717_ = lean_st_ref_get(v_a_708_);
v_infoState_718_ = lean_ctor_get(v___x_717_, 8);
lean_inc_ref(v_infoState_718_);
lean_dec(v___x_717_);
v_enabled_719_ = lean_ctor_get_uint8(v_infoState_718_, sizeof(void*)*3);
lean_dec_ref(v_infoState_718_);
if (v_enabled_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v___x_716_);
lean_dec(v_tk_714_);
v___x_720_ = lean_obj_once(&l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5, &l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5_once, _init_l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__5);
v___x_721_ = l_Lean_logError___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__1(v___x_720_, v_a_707_, v_a_708_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Elab_Command_elabCommand(v___x_716_, v_a_707_, v_a_708_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_723_; lean_object* v_infoState_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v_trees_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
lean_dec_ref_known(v___x_722_, 1);
v___x_723_ = lean_st_ref_get(v_a_708_);
v_infoState_724_ = lean_ctor_get(v___x_723_, 8);
lean_inc_ref(v_infoState_724_);
lean_dec(v___x_723_);
v___x_725_ = l_Lean_Elab_InfoState_substituteLazy(v_infoState_724_);
v___x_726_ = lean_task_get_own(v___x_725_);
v_trees_727_ = lean_ctor_get(v___x_726_, 2);
lean_inc_ref(v_trees_727_);
lean_dec(v___x_726_);
v___x_728_ = lean_box(0);
v___x_729_ = l_Lean_PersistentArray_forIn___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__3(v_tk_714_, v_trees_727_, v___x_728_, v_a_707_, v_a_708_);
lean_dec_ref(v_trees_727_);
lean_dec(v_tk_714_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v___x_729_, 0);
lean_dec(v_unused_737_);
v___x_731_ = v___x_729_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_dec(v___x_729_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 0, v___x_728_);
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_728_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
return v___x_729_;
}
}
else
{
lean_dec(v_tk_714_);
return v___x_722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed(lean_object* v_x_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees(v_x_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4(lean_object* v_msgData_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___redArg(v_msgData_743_, v___y_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4___boxed(lean_object* v_msgData_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_logInfoAt___at___00Lean_Elab_Tactic_InfoTrees_elabInfoTrees_spec__2_spec__3_spec__4(v_msgData_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1(){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_764_ = l_Lean_Elab_Command_commandElabAttribute;
v___x_765_ = ((lean_object*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___closed__2));
v___x_766_ = ((lean_object*)(l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___closed__4));
v___x_767_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_InfoTrees_elabInfoTrees___boxed), 4, 0);
v___x_768_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(v___x_764_, v___x_765_, v___x_766_, v___x_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1___boxed(lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Lean_Elab_InfoTrees_0__Lean_Elab_Tactic_InfoTrees_elabInfoTrees___regBuiltin_Lean_Elab_Tactic_InfoTrees_elabInfoTrees__1();
return v_res_770_;
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
