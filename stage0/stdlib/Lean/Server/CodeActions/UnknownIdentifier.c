// Lean compiler output
// Module: Lean.Server.CodeActions.UnknownIdentifier
// Imports: public import Lean.Server.Completion.CompletionInfoSelection public import Lean.Server.CodeActions.Basic
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
lean_object* l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_ofPosition(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Server_Completion_getDotCompletionTypeNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_getString_x21(lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
lean_object* l_Lean_Server_Completion_getDotIdCompletionTypeNames___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Server_RequestM_findCmdDataAtPos(lean_object*, lean_object*, uint8_t);
lean_object* lean_task_get_own(lean_object*);
lean_object* l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_requestCancellationTask(lean_object*);
lean_object* l_Lean_Server_ServerTask_waitAny___redArg(lean_object*);
lean_object* l_Lean_Server_RequestM_checkCancelled(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
lean_object* l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Server_instToJsonCodeActionResolveData_toJson(lean_object*);
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Environment_mainModule(lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* l_IO_AsyncList_waitAll___redArg(lean_object*);
lean_object* l_Lean_Syntax_getRange_x3f(lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
lean_object* l_Lean_Elab_InfoTree_foldInfo___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTask_map___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Language_Lean_pushOpt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_getAll(lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_MessageLog_append(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go(lean_object*);
lean_object* l_Lean_Server_RequestM_findCmdParsedSnap(lean_object*, lean_object*);
lean_object* l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(lean_object*);
lean_object* l_Lean_Language_SnapshotTree_collectMessagesInRange(lean_object*, lean_object*);
lean_object* l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value;
static const lean_closure_object l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1_value;
static const lean_ctor_object l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4(lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Language_Lean_instToSnapshotTreeCommandParsedSnapshot_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value;
static lean_once_cell_t l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1;
static lean_once_cell_t l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2;
static lean_once_cell_t l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3;
static const lean_closure_object l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0_value)} };
static const lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_computeQueries___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_computeQueries___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_computeQueries___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "allUnknownIdentifiers"};
static const lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 212, 41, 210, 145, 194, 60, 31)}};
static const lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider = (const lean_object*)&l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider___closed__1_value;
static const lean_string_object l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "unknownIdentifiers"};
static const lean_object* l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__0_value),LEAN_SCALAR_PTR_LITERAL(89, 183, 1, 9, 200, 225, 116, 235)}};
static const lean_object* l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_importUnknownIdentifiersProvider = (const lean_object*)&l_Lean_Server_FileWorker_importUnknownIdentifiersProvider___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Import all unambiguous unknown identifiers"};
static const lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0 = (const lean_object*)&l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0_value;
static const lean_string_object l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1 = (const lean_object*)&l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1_value;
static const lean_string_object l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "public "};
static const lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2 = (const lean_object*)&l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2_value;
static const lean_string_object l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "meta "};
static const lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3 = (const lean_object*)&l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Cannot parse server request response: "};
static const lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0(lean_object*);
static const lean_closure_object l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0 = (const lean_object*)&l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Change to "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Import "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " from "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "$/lean/queryModule"};
static const lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0_value;
static const lean_closure_object l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1_value;
static const lean_closure_object l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2 = (const lean_object*)&l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2_value;
static const lean_array_object l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3 = (const lean_object*)&l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3_value;
static const lean_string_object l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "quickfix"};
static const lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4 = (const lean_object*)&l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4_value;
static const lean_ctor_object l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5 = (const lean_object*)&l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0;
static const lean_array_object l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(lean_object* v_r1_1_, lean_object* v_r2_2_){
_start:
{
lean_object* v_start_3_; lean_object* v_stop_4_; lean_object* v_start_5_; lean_object* v_stop_6_; uint8_t v___x_7_; 
v_start_3_ = lean_ctor_get(v_r1_1_, 0);
v_stop_4_ = lean_ctor_get(v_r1_1_, 1);
v_start_5_ = lean_ctor_get(v_r2_2_, 0);
v_stop_6_ = lean_ctor_get(v_r2_2_, 1);
v___x_7_ = lean_nat_dec_lt(v_start_3_, v_start_5_);
if (v___x_7_ == 0)
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_lt(v_start_5_, v_start_3_);
if (v___x_8_ == 0)
{
uint8_t v___x_9_; 
v___x_9_ = lean_nat_dec_lt(v_stop_4_, v_stop_6_);
if (v___x_9_ == 0)
{
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_lt(v_stop_6_, v_stop_4_);
if (v___x_10_ == 0)
{
uint8_t v___x_11_; 
v___x_11_ = 1;
return v___x_11_;
}
else
{
uint8_t v___x_12_; 
v___x_12_ = 2;
return v___x_12_;
}
}
else
{
uint8_t v___x_13_; 
v___x_13_ = 0;
return v___x_13_;
}
}
else
{
uint8_t v___x_14_; 
v___x_14_ = 2;
return v___x_14_;
}
}
else
{
uint8_t v___x_15_; 
v___x_15_ = 0;
return v___x_15_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges___boxed(lean_object* v_r1_16_, lean_object* v_r2_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_r1_16_, v_r2_17_);
lean_dec_ref(v_r2_17_);
lean_dec_ref(v_r1_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(lean_object* v_k_20_, lean_object* v_t_21_){
_start:
{
if (lean_obj_tag(v_t_21_) == 0)
{
lean_object* v_k_22_; lean_object* v_l_23_; lean_object* v_r_24_; uint8_t v___x_25_; 
v_k_22_ = lean_ctor_get(v_t_21_, 1);
v_l_23_ = lean_ctor_get(v_t_21_, 3);
v_r_24_ = lean_ctor_get(v_t_21_, 4);
v___x_25_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_k_20_, v_k_22_);
switch(v___x_25_)
{
case 0:
{
v_t_21_ = v_l_23_;
goto _start;
}
case 1:
{
uint8_t v___x_27_; 
v___x_27_ = 1;
return v___x_27_;
}
default: 
{
v_t_21_ = v_r_24_;
goto _start;
}
}
}
else
{
uint8_t v___x_29_; 
v___x_29_ = 0;
return v___x_29_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg___boxed(lean_object* v_k_30_, lean_object* v_t_31_){
_start:
{
uint8_t v_res_32_; lean_object* v_r_33_; 
v_res_32_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_k_30_, v_t_31_);
lean_dec(v_t_31_);
lean_dec_ref(v_k_30_);
v_r_33_ = lean_box(v_res_32_);
return v_r_33_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(lean_object* v_k_34_, lean_object* v_v_35_, lean_object* v_t_36_){
_start:
{
if (lean_obj_tag(v_t_36_) == 0)
{
lean_object* v_size_37_; lean_object* v_k_38_; lean_object* v_v_39_; lean_object* v_l_40_; lean_object* v_r_41_; lean_object* v___x_43_; uint8_t v_isShared_44_; uint8_t v_isSharedCheck_321_; 
v_size_37_ = lean_ctor_get(v_t_36_, 0);
v_k_38_ = lean_ctor_get(v_t_36_, 1);
v_v_39_ = lean_ctor_get(v_t_36_, 2);
v_l_40_ = lean_ctor_get(v_t_36_, 3);
v_r_41_ = lean_ctor_get(v_t_36_, 4);
v_isSharedCheck_321_ = !lean_is_exclusive(v_t_36_);
if (v_isSharedCheck_321_ == 0)
{
v___x_43_ = v_t_36_;
v_isShared_44_ = v_isSharedCheck_321_;
goto v_resetjp_42_;
}
else
{
lean_inc(v_r_41_);
lean_inc(v_l_40_);
lean_inc(v_v_39_);
lean_inc(v_k_38_);
lean_inc(v_size_37_);
lean_dec(v_t_36_);
v___x_43_ = lean_box(0);
v_isShared_44_ = v_isSharedCheck_321_;
goto v_resetjp_42_;
}
v_resetjp_42_:
{
uint8_t v___x_45_; 
v___x_45_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_compareRanges(v_k_34_, v_k_38_);
switch(v___x_45_)
{
case 0:
{
lean_object* v_impl_46_; lean_object* v___x_47_; 
lean_dec(v_size_37_);
v_impl_46_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_34_, v_v_35_, v_l_40_);
v___x_47_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_41_) == 0)
{
lean_object* v_size_48_; lean_object* v_size_49_; lean_object* v_k_50_; lean_object* v_v_51_; lean_object* v_l_52_; lean_object* v_r_53_; lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v_size_48_ = lean_ctor_get(v_r_41_, 0);
v_size_49_ = lean_ctor_get(v_impl_46_, 0);
lean_inc(v_size_49_);
v_k_50_ = lean_ctor_get(v_impl_46_, 1);
lean_inc(v_k_50_);
v_v_51_ = lean_ctor_get(v_impl_46_, 2);
lean_inc(v_v_51_);
v_l_52_ = lean_ctor_get(v_impl_46_, 3);
lean_inc(v_l_52_);
v_r_53_ = lean_ctor_get(v_impl_46_, 4);
lean_inc(v_r_53_);
v___x_54_ = lean_unsigned_to_nat(3u);
v___x_55_ = lean_nat_mul(v___x_54_, v_size_48_);
v___x_56_ = lean_nat_dec_lt(v___x_55_, v_size_49_);
lean_dec(v___x_55_);
if (v___x_56_ == 0)
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_60_; 
lean_dec(v_r_53_);
lean_dec(v_l_52_);
lean_dec(v_v_51_);
lean_dec(v_k_50_);
v___x_57_ = lean_nat_add(v___x_47_, v_size_49_);
lean_dec(v_size_49_);
v___x_58_ = lean_nat_add(v___x_57_, v_size_48_);
lean_dec(v___x_57_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 3, v_impl_46_);
lean_ctor_set(v___x_43_, 0, v___x_58_);
v___x_60_ = v___x_43_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_61_, 3, v_impl_46_);
lean_ctor_set(v_reuseFailAlloc_61_, 4, v_r_41_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
else
{
lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_127_; 
v_isSharedCheck_127_ = !lean_is_exclusive(v_impl_46_);
if (v_isSharedCheck_127_ == 0)
{
lean_object* v_unused_128_; lean_object* v_unused_129_; lean_object* v_unused_130_; lean_object* v_unused_131_; lean_object* v_unused_132_; 
v_unused_128_ = lean_ctor_get(v_impl_46_, 4);
lean_dec(v_unused_128_);
v_unused_129_ = lean_ctor_get(v_impl_46_, 3);
lean_dec(v_unused_129_);
v_unused_130_ = lean_ctor_get(v_impl_46_, 2);
lean_dec(v_unused_130_);
v_unused_131_ = lean_ctor_get(v_impl_46_, 1);
lean_dec(v_unused_131_);
v_unused_132_ = lean_ctor_get(v_impl_46_, 0);
lean_dec(v_unused_132_);
v___x_63_ = v_impl_46_;
v_isShared_64_ = v_isSharedCheck_127_;
goto v_resetjp_62_;
}
else
{
lean_dec(v_impl_46_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_127_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v_size_65_; lean_object* v_size_66_; lean_object* v_k_67_; lean_object* v_v_68_; lean_object* v_l_69_; lean_object* v_r_70_; lean_object* v___x_71_; lean_object* v___x_72_; uint8_t v___x_73_; 
v_size_65_ = lean_ctor_get(v_l_52_, 0);
v_size_66_ = lean_ctor_get(v_r_53_, 0);
v_k_67_ = lean_ctor_get(v_r_53_, 1);
v_v_68_ = lean_ctor_get(v_r_53_, 2);
v_l_69_ = lean_ctor_get(v_r_53_, 3);
v_r_70_ = lean_ctor_get(v_r_53_, 4);
v___x_71_ = lean_unsigned_to_nat(2u);
v___x_72_ = lean_nat_mul(v___x_71_, v_size_65_);
v___x_73_ = lean_nat_dec_lt(v_size_66_, v___x_72_);
lean_dec(v___x_72_);
if (v___x_73_ == 0)
{
lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_102_; 
lean_inc(v_r_70_);
lean_inc(v_l_69_);
lean_inc(v_v_68_);
lean_inc(v_k_67_);
v_isSharedCheck_102_ = !lean_is_exclusive(v_r_53_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; lean_object* v_unused_104_; lean_object* v_unused_105_; lean_object* v_unused_106_; lean_object* v_unused_107_; 
v_unused_103_ = lean_ctor_get(v_r_53_, 4);
lean_dec(v_unused_103_);
v_unused_104_ = lean_ctor_get(v_r_53_, 3);
lean_dec(v_unused_104_);
v_unused_105_ = lean_ctor_get(v_r_53_, 2);
lean_dec(v_unused_105_);
v_unused_106_ = lean_ctor_get(v_r_53_, 1);
lean_dec(v_unused_106_);
v_unused_107_ = lean_ctor_get(v_r_53_, 0);
lean_dec(v_unused_107_);
v___x_75_ = v_r_53_;
v_isShared_76_ = v_isSharedCheck_102_;
goto v_resetjp_74_;
}
else
{
lean_dec(v_r_53_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_102_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___y_80_; lean_object* v___y_81_; lean_object* v___y_82_; lean_object* v___x_90_; lean_object* v___y_92_; 
v___x_77_ = lean_nat_add(v___x_47_, v_size_49_);
lean_dec(v_size_49_);
v___x_78_ = lean_nat_add(v___x_77_, v_size_48_);
lean_dec(v___x_77_);
v___x_90_ = lean_nat_add(v___x_47_, v_size_65_);
if (lean_obj_tag(v_l_69_) == 0)
{
lean_object* v_size_100_; 
v_size_100_ = lean_ctor_get(v_l_69_, 0);
lean_inc(v_size_100_);
v___y_92_ = v_size_100_;
goto v___jp_91_;
}
else
{
lean_object* v___x_101_; 
v___x_101_ = lean_unsigned_to_nat(0u);
v___y_92_ = v___x_101_;
goto v___jp_91_;
}
v___jp_79_:
{
lean_object* v___x_83_; lean_object* v___x_85_; 
v___x_83_ = lean_nat_add(v___y_81_, v___y_82_);
lean_dec(v___y_82_);
lean_dec(v___y_81_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 4, v_r_41_);
lean_ctor_set(v___x_75_, 3, v_r_70_);
lean_ctor_set(v___x_75_, 2, v_v_39_);
lean_ctor_set(v___x_75_, 1, v_k_38_);
lean_ctor_set(v___x_75_, 0, v___x_83_);
v___x_85_ = v___x_75_;
goto v_reusejp_84_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_83_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_89_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_89_, 3, v_r_70_);
lean_ctor_set(v_reuseFailAlloc_89_, 4, v_r_41_);
v___x_85_ = v_reuseFailAlloc_89_;
goto v_reusejp_84_;
}
v_reusejp_84_:
{
lean_object* v___x_87_; 
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 4, v___x_85_);
lean_ctor_set(v___x_63_, 3, v___y_80_);
lean_ctor_set(v___x_63_, 2, v_v_68_);
lean_ctor_set(v___x_63_, 1, v_k_67_);
lean_ctor_set(v___x_63_, 0, v___x_78_);
v___x_87_ = v___x_63_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_k_67_);
lean_ctor_set(v_reuseFailAlloc_88_, 2, v_v_68_);
lean_ctor_set(v_reuseFailAlloc_88_, 3, v___y_80_);
lean_ctor_set(v_reuseFailAlloc_88_, 4, v___x_85_);
v___x_87_ = v_reuseFailAlloc_88_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
return v___x_87_;
}
}
}
v___jp_91_:
{
lean_object* v___x_93_; lean_object* v___x_95_; 
v___x_93_ = lean_nat_add(v___x_90_, v___y_92_);
lean_dec(v___y_92_);
lean_dec(v___x_90_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v_l_69_);
lean_ctor_set(v___x_43_, 3, v_l_52_);
lean_ctor_set(v___x_43_, 2, v_v_51_);
lean_ctor_set(v___x_43_, 1, v_k_50_);
lean_ctor_set(v___x_43_, 0, v___x_93_);
v___x_95_ = v___x_43_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_k_50_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_v_51_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_l_52_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v_l_69_);
v___x_95_ = v_reuseFailAlloc_99_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; 
v___x_96_ = lean_nat_add(v___x_47_, v_size_48_);
if (lean_obj_tag(v_r_70_) == 0)
{
lean_object* v_size_97_; 
v_size_97_ = lean_ctor_get(v_r_70_, 0);
lean_inc(v_size_97_);
v___y_80_ = v___x_95_;
v___y_81_ = v___x_96_;
v___y_82_ = v_size_97_;
goto v___jp_79_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___y_80_ = v___x_95_;
v___y_81_ = v___x_96_;
v___y_82_ = v___x_98_;
goto v___jp_79_;
}
}
}
}
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
lean_del_object(v___x_43_);
v___x_108_ = lean_nat_add(v___x_47_, v_size_49_);
lean_dec(v_size_49_);
v___x_109_ = lean_nat_add(v___x_108_, v_size_48_);
lean_dec(v___x_108_);
v___x_110_ = lean_nat_add(v___x_47_, v_size_48_);
v___x_111_ = lean_nat_add(v___x_110_, v_size_66_);
lean_dec(v___x_110_);
lean_inc_ref(v_r_41_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 4, v_r_41_);
lean_ctor_set(v___x_63_, 3, v_r_53_);
lean_ctor_set(v___x_63_, 2, v_v_39_);
lean_ctor_set(v___x_63_, 1, v_k_38_);
lean_ctor_set(v___x_63_, 0, v___x_111_);
v___x_113_ = v___x_63_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v___x_111_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_126_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_126_, 3, v_r_53_);
lean_ctor_set(v_reuseFailAlloc_126_, 4, v_r_41_);
v___x_113_ = v_reuseFailAlloc_126_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_115_; uint8_t v_isShared_116_; uint8_t v_isSharedCheck_120_; 
v_isSharedCheck_120_ = !lean_is_exclusive(v_r_41_);
if (v_isSharedCheck_120_ == 0)
{
lean_object* v_unused_121_; lean_object* v_unused_122_; lean_object* v_unused_123_; lean_object* v_unused_124_; lean_object* v_unused_125_; 
v_unused_121_ = lean_ctor_get(v_r_41_, 4);
lean_dec(v_unused_121_);
v_unused_122_ = lean_ctor_get(v_r_41_, 3);
lean_dec(v_unused_122_);
v_unused_123_ = lean_ctor_get(v_r_41_, 2);
lean_dec(v_unused_123_);
v_unused_124_ = lean_ctor_get(v_r_41_, 1);
lean_dec(v_unused_124_);
v_unused_125_ = lean_ctor_get(v_r_41_, 0);
lean_dec(v_unused_125_);
v___x_115_ = v_r_41_;
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
else
{
lean_dec(v_r_41_);
v___x_115_ = lean_box(0);
v_isShared_116_ = v_isSharedCheck_120_;
goto v_resetjp_114_;
}
v_resetjp_114_:
{
lean_object* v___x_118_; 
if (v_isShared_116_ == 0)
{
lean_ctor_set(v___x_115_, 4, v___x_113_);
lean_ctor_set(v___x_115_, 3, v_l_52_);
lean_ctor_set(v___x_115_, 2, v_v_51_);
lean_ctor_set(v___x_115_, 1, v_k_50_);
lean_ctor_set(v___x_115_, 0, v___x_109_);
v___x_118_ = v___x_115_;
goto v_reusejp_117_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_119_, 1, v_k_50_);
lean_ctor_set(v_reuseFailAlloc_119_, 2, v_v_51_);
lean_ctor_set(v_reuseFailAlloc_119_, 3, v_l_52_);
lean_ctor_set(v_reuseFailAlloc_119_, 4, v___x_113_);
v___x_118_ = v_reuseFailAlloc_119_;
goto v_reusejp_117_;
}
v_reusejp_117_:
{
return v___x_118_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_133_; 
v_l_133_ = lean_ctor_get(v_impl_46_, 3);
lean_inc(v_l_133_);
if (lean_obj_tag(v_l_133_) == 0)
{
lean_object* v_r_134_; lean_object* v_k_135_; lean_object* v_v_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_147_; 
v_r_134_ = lean_ctor_get(v_impl_46_, 4);
v_k_135_ = lean_ctor_get(v_impl_46_, 1);
v_v_136_ = lean_ctor_get(v_impl_46_, 2);
v_isSharedCheck_147_ = !lean_is_exclusive(v_impl_46_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; lean_object* v_unused_149_; 
v_unused_148_ = lean_ctor_get(v_impl_46_, 3);
lean_dec(v_unused_148_);
v_unused_149_ = lean_ctor_get(v_impl_46_, 0);
lean_dec(v_unused_149_);
v___x_138_ = v_impl_46_;
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_r_134_);
lean_inc(v_v_136_);
lean_inc(v_k_135_);
lean_dec(v_impl_46_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_147_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_142_; 
v___x_140_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_134_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 3, v_r_134_);
lean_ctor_set(v___x_138_, 2, v_v_39_);
lean_ctor_set(v___x_138_, 1, v_k_38_);
lean_ctor_set(v___x_138_, 0, v___x_47_);
v___x_142_ = v___x_138_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_146_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_146_, 3, v_r_134_);
lean_ctor_set(v_reuseFailAlloc_146_, 4, v_r_134_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_144_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v___x_142_);
lean_ctor_set(v___x_43_, 3, v_l_133_);
lean_ctor_set(v___x_43_, 2, v_v_136_);
lean_ctor_set(v___x_43_, 1, v_k_135_);
lean_ctor_set(v___x_43_, 0, v___x_140_);
v___x_144_ = v___x_43_;
goto v_reusejp_143_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_140_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_k_135_);
lean_ctor_set(v_reuseFailAlloc_145_, 2, v_v_136_);
lean_ctor_set(v_reuseFailAlloc_145_, 3, v_l_133_);
lean_ctor_set(v_reuseFailAlloc_145_, 4, v___x_142_);
v___x_144_ = v_reuseFailAlloc_145_;
goto v_reusejp_143_;
}
v_reusejp_143_:
{
return v___x_144_;
}
}
}
}
else
{
lean_object* v_r_150_; 
v_r_150_ = lean_ctor_get(v_impl_46_, 4);
lean_inc(v_r_150_);
if (lean_obj_tag(v_r_150_) == 0)
{
lean_object* v_k_151_; lean_object* v_v_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_175_; 
v_k_151_ = lean_ctor_get(v_impl_46_, 1);
v_v_152_ = lean_ctor_get(v_impl_46_, 2);
v_isSharedCheck_175_ = !lean_is_exclusive(v_impl_46_);
if (v_isSharedCheck_175_ == 0)
{
lean_object* v_unused_176_; lean_object* v_unused_177_; lean_object* v_unused_178_; 
v_unused_176_ = lean_ctor_get(v_impl_46_, 4);
lean_dec(v_unused_176_);
v_unused_177_ = lean_ctor_get(v_impl_46_, 3);
lean_dec(v_unused_177_);
v_unused_178_ = lean_ctor_get(v_impl_46_, 0);
lean_dec(v_unused_178_);
v___x_154_ = v_impl_46_;
v_isShared_155_ = v_isSharedCheck_175_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_v_152_);
lean_inc(v_k_151_);
lean_dec(v_impl_46_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_175_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v_k_156_; lean_object* v_v_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_171_; 
v_k_156_ = lean_ctor_get(v_r_150_, 1);
v_v_157_ = lean_ctor_get(v_r_150_, 2);
v_isSharedCheck_171_ = !lean_is_exclusive(v_r_150_);
if (v_isSharedCheck_171_ == 0)
{
lean_object* v_unused_172_; lean_object* v_unused_173_; lean_object* v_unused_174_; 
v_unused_172_ = lean_ctor_get(v_r_150_, 4);
lean_dec(v_unused_172_);
v_unused_173_ = lean_ctor_get(v_r_150_, 3);
lean_dec(v_unused_173_);
v_unused_174_ = lean_ctor_get(v_r_150_, 0);
lean_dec(v_unused_174_);
v___x_159_ = v_r_150_;
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_v_157_);
lean_inc(v_k_156_);
lean_dec(v_r_150_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_171_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_163_; 
v___x_161_ = lean_unsigned_to_nat(3u);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 4, v_l_133_);
lean_ctor_set(v___x_159_, 3, v_l_133_);
lean_ctor_set(v___x_159_, 2, v_v_152_);
lean_ctor_set(v___x_159_, 1, v_k_151_);
lean_ctor_set(v___x_159_, 0, v___x_47_);
v___x_163_ = v___x_159_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_k_151_);
lean_ctor_set(v_reuseFailAlloc_170_, 2, v_v_152_);
lean_ctor_set(v_reuseFailAlloc_170_, 3, v_l_133_);
lean_ctor_set(v_reuseFailAlloc_170_, 4, v_l_133_);
v___x_163_ = v_reuseFailAlloc_170_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_165_; 
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 4, v_l_133_);
lean_ctor_set(v___x_154_, 2, v_v_39_);
lean_ctor_set(v___x_154_, 1, v_k_38_);
lean_ctor_set(v___x_154_, 0, v___x_47_);
v___x_165_ = v___x_154_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v___x_47_);
lean_ctor_set(v_reuseFailAlloc_169_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_169_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_169_, 3, v_l_133_);
lean_ctor_set(v_reuseFailAlloc_169_, 4, v_l_133_);
v___x_165_ = v_reuseFailAlloc_169_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_167_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v___x_165_);
lean_ctor_set(v___x_43_, 3, v___x_163_);
lean_ctor_set(v___x_43_, 2, v_v_157_);
lean_ctor_set(v___x_43_, 1, v_k_156_);
lean_ctor_set(v___x_43_, 0, v___x_161_);
v___x_167_ = v___x_43_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_k_156_);
lean_ctor_set(v_reuseFailAlloc_168_, 2, v_v_157_);
lean_ctor_set(v_reuseFailAlloc_168_, 3, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_168_, 4, v___x_165_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
}
}
else
{
lean_object* v___x_179_; lean_object* v___x_181_; 
v___x_179_ = lean_unsigned_to_nat(2u);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v_r_150_);
lean_ctor_set(v___x_43_, 3, v_impl_46_);
lean_ctor_set(v___x_43_, 0, v___x_179_);
v___x_181_ = v___x_43_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_179_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_impl_46_);
lean_ctor_set(v_reuseFailAlloc_182_, 4, v_r_150_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
}
case 1:
{
lean_object* v___x_184_; 
lean_dec(v_v_39_);
lean_dec(v_k_38_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 2, v_v_35_);
lean_ctor_set(v___x_43_, 1, v_k_34_);
v___x_184_ = v___x_43_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_185_; 
v_reuseFailAlloc_185_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_185_, 0, v_size_37_);
lean_ctor_set(v_reuseFailAlloc_185_, 1, v_k_34_);
lean_ctor_set(v_reuseFailAlloc_185_, 2, v_v_35_);
lean_ctor_set(v_reuseFailAlloc_185_, 3, v_l_40_);
lean_ctor_set(v_reuseFailAlloc_185_, 4, v_r_41_);
v___x_184_ = v_reuseFailAlloc_185_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
return v___x_184_;
}
}
default: 
{
lean_object* v_impl_186_; lean_object* v___x_187_; 
lean_dec(v_size_37_);
v_impl_186_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_34_, v_v_35_, v_r_41_);
v___x_187_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_40_) == 0)
{
lean_object* v_size_188_; lean_object* v_size_189_; lean_object* v_k_190_; lean_object* v_v_191_; lean_object* v_l_192_; lean_object* v_r_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_size_188_ = lean_ctor_get(v_l_40_, 0);
v_size_189_ = lean_ctor_get(v_impl_186_, 0);
lean_inc(v_size_189_);
v_k_190_ = lean_ctor_get(v_impl_186_, 1);
lean_inc(v_k_190_);
v_v_191_ = lean_ctor_get(v_impl_186_, 2);
lean_inc(v_v_191_);
v_l_192_ = lean_ctor_get(v_impl_186_, 3);
lean_inc(v_l_192_);
v_r_193_ = lean_ctor_get(v_impl_186_, 4);
lean_inc(v_r_193_);
v___x_194_ = lean_unsigned_to_nat(3u);
v___x_195_ = lean_nat_mul(v___x_194_, v_size_188_);
v___x_196_ = lean_nat_dec_lt(v___x_195_, v_size_189_);
lean_dec(v___x_195_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_200_; 
lean_dec(v_r_193_);
lean_dec(v_l_192_);
lean_dec(v_v_191_);
lean_dec(v_k_190_);
v___x_197_ = lean_nat_add(v___x_187_, v_size_188_);
v___x_198_ = lean_nat_add(v___x_197_, v_size_189_);
lean_dec(v_size_189_);
lean_dec(v___x_197_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v_impl_186_);
lean_ctor_set(v___x_43_, 0, v___x_198_);
v___x_200_ = v___x_43_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_l_40_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_impl_186_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
}
}
else
{
lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_265_; 
v_isSharedCheck_265_ = !lean_is_exclusive(v_impl_186_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; lean_object* v_unused_267_; lean_object* v_unused_268_; lean_object* v_unused_269_; lean_object* v_unused_270_; 
v_unused_266_ = lean_ctor_get(v_impl_186_, 4);
lean_dec(v_unused_266_);
v_unused_267_ = lean_ctor_get(v_impl_186_, 3);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_impl_186_, 2);
lean_dec(v_unused_268_);
v_unused_269_ = lean_ctor_get(v_impl_186_, 1);
lean_dec(v_unused_269_);
v_unused_270_ = lean_ctor_get(v_impl_186_, 0);
lean_dec(v_unused_270_);
v___x_203_ = v_impl_186_;
v_isShared_204_ = v_isSharedCheck_265_;
goto v_resetjp_202_;
}
else
{
lean_dec(v_impl_186_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_265_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v_size_205_; lean_object* v_k_206_; lean_object* v_v_207_; lean_object* v_l_208_; lean_object* v_r_209_; lean_object* v_size_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_size_205_ = lean_ctor_get(v_l_192_, 0);
v_k_206_ = lean_ctor_get(v_l_192_, 1);
v_v_207_ = lean_ctor_get(v_l_192_, 2);
v_l_208_ = lean_ctor_get(v_l_192_, 3);
v_r_209_ = lean_ctor_get(v_l_192_, 4);
v_size_210_ = lean_ctor_get(v_r_193_, 0);
v___x_211_ = lean_unsigned_to_nat(2u);
v___x_212_ = lean_nat_mul(v___x_211_, v_size_210_);
v___x_213_ = lean_nat_dec_lt(v_size_205_, v___x_212_);
lean_dec(v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_241_; 
lean_inc(v_r_209_);
lean_inc(v_l_208_);
lean_inc(v_v_207_);
lean_inc(v_k_206_);
v_isSharedCheck_241_ = !lean_is_exclusive(v_l_192_);
if (v_isSharedCheck_241_ == 0)
{
lean_object* v_unused_242_; lean_object* v_unused_243_; lean_object* v_unused_244_; lean_object* v_unused_245_; lean_object* v_unused_246_; 
v_unused_242_ = lean_ctor_get(v_l_192_, 4);
lean_dec(v_unused_242_);
v_unused_243_ = lean_ctor_get(v_l_192_, 3);
lean_dec(v_unused_243_);
v_unused_244_ = lean_ctor_get(v_l_192_, 2);
lean_dec(v_unused_244_);
v_unused_245_ = lean_ctor_get(v_l_192_, 1);
lean_dec(v_unused_245_);
v_unused_246_ = lean_ctor_get(v_l_192_, 0);
lean_dec(v_unused_246_);
v___x_215_ = v_l_192_;
v_isShared_216_ = v_isSharedCheck_241_;
goto v_resetjp_214_;
}
else
{
lean_dec(v_l_192_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_241_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___y_220_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_231_; 
v___x_217_ = lean_nat_add(v___x_187_, v_size_188_);
v___x_218_ = lean_nat_add(v___x_217_, v_size_189_);
lean_dec(v_size_189_);
if (lean_obj_tag(v_l_208_) == 0)
{
lean_object* v_size_239_; 
v_size_239_ = lean_ctor_get(v_l_208_, 0);
lean_inc(v_size_239_);
v___y_231_ = v_size_239_;
goto v___jp_230_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___y_231_ = v___x_240_;
goto v___jp_230_;
}
v___jp_219_:
{
lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_223_ = lean_nat_add(v___y_220_, v___y_222_);
lean_dec(v___y_222_);
lean_dec(v___y_220_);
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 4, v_r_193_);
lean_ctor_set(v___x_215_, 3, v_r_209_);
lean_ctor_set(v___x_215_, 2, v_v_191_);
lean_ctor_set(v___x_215_, 1, v_k_190_);
lean_ctor_set(v___x_215_, 0, v___x_223_);
v___x_225_ = v___x_215_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_223_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_k_190_);
lean_ctor_set(v_reuseFailAlloc_229_, 2, v_v_191_);
lean_ctor_set(v_reuseFailAlloc_229_, 3, v_r_209_);
lean_ctor_set(v_reuseFailAlloc_229_, 4, v_r_193_);
v___x_225_ = v_reuseFailAlloc_229_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_227_; 
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 4, v___x_225_);
lean_ctor_set(v___x_203_, 3, v___y_221_);
lean_ctor_set(v___x_203_, 2, v_v_207_);
lean_ctor_set(v___x_203_, 1, v_k_206_);
lean_ctor_set(v___x_203_, 0, v___x_218_);
v___x_227_ = v___x_203_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v___x_218_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_k_206_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_v_207_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v___y_221_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v___x_225_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
v___jp_230_:
{
lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_232_ = lean_nat_add(v___x_217_, v___y_231_);
lean_dec(v___y_231_);
lean_dec(v___x_217_);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v_l_208_);
lean_ctor_set(v___x_43_, 0, v___x_232_);
v___x_234_ = v___x_43_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_238_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_238_, 3, v_l_40_);
lean_ctor_set(v_reuseFailAlloc_238_, 4, v_l_208_);
v___x_234_ = v_reuseFailAlloc_238_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; 
v___x_235_ = lean_nat_add(v___x_187_, v_size_210_);
if (lean_obj_tag(v_r_209_) == 0)
{
lean_object* v_size_236_; 
v_size_236_ = lean_ctor_get(v_r_209_, 0);
lean_inc(v_size_236_);
v___y_220_ = v___x_235_;
v___y_221_ = v___x_234_;
v___y_222_ = v_size_236_;
goto v___jp_219_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___y_220_ = v___x_235_;
v___y_221_ = v___x_234_;
v___y_222_ = v___x_237_;
goto v___jp_219_;
}
}
}
}
}
else
{
lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_251_; 
lean_del_object(v___x_43_);
v___x_247_ = lean_nat_add(v___x_187_, v_size_188_);
v___x_248_ = lean_nat_add(v___x_247_, v_size_189_);
lean_dec(v_size_189_);
v___x_249_ = lean_nat_add(v___x_247_, v_size_205_);
lean_dec(v___x_247_);
lean_inc_ref(v_l_40_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 4, v_l_192_);
lean_ctor_set(v___x_203_, 3, v_l_40_);
lean_ctor_set(v___x_203_, 2, v_v_39_);
lean_ctor_set(v___x_203_, 1, v_k_38_);
lean_ctor_set(v___x_203_, 0, v___x_249_);
v___x_251_ = v___x_203_;
goto v_reusejp_250_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_264_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_264_, 3, v_l_40_);
lean_ctor_set(v_reuseFailAlloc_264_, 4, v_l_192_);
v___x_251_ = v_reuseFailAlloc_264_;
goto v_reusejp_250_;
}
v_reusejp_250_:
{
lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_258_; 
v_isSharedCheck_258_ = !lean_is_exclusive(v_l_40_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; lean_object* v_unused_260_; lean_object* v_unused_261_; lean_object* v_unused_262_; lean_object* v_unused_263_; 
v_unused_259_ = lean_ctor_get(v_l_40_, 4);
lean_dec(v_unused_259_);
v_unused_260_ = lean_ctor_get(v_l_40_, 3);
lean_dec(v_unused_260_);
v_unused_261_ = lean_ctor_get(v_l_40_, 2);
lean_dec(v_unused_261_);
v_unused_262_ = lean_ctor_get(v_l_40_, 1);
lean_dec(v_unused_262_);
v_unused_263_ = lean_ctor_get(v_l_40_, 0);
lean_dec(v_unused_263_);
v___x_253_ = v_l_40_;
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
else
{
lean_dec(v_l_40_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_258_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
lean_object* v___x_256_; 
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 4, v_r_193_);
lean_ctor_set(v___x_253_, 3, v___x_251_);
lean_ctor_set(v___x_253_, 2, v_v_191_);
lean_ctor_set(v___x_253_, 1, v_k_190_);
lean_ctor_set(v___x_253_, 0, v___x_248_);
v___x_256_ = v___x_253_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_k_190_);
lean_ctor_set(v_reuseFailAlloc_257_, 2, v_v_191_);
lean_ctor_set(v_reuseFailAlloc_257_, 3, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_257_, 4, v_r_193_);
v___x_256_ = v_reuseFailAlloc_257_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
return v___x_256_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_271_; 
v_l_271_ = lean_ctor_get(v_impl_186_, 3);
lean_inc(v_l_271_);
if (lean_obj_tag(v_l_271_) == 0)
{
lean_object* v_r_272_; lean_object* v_k_273_; lean_object* v_v_274_; lean_object* v___x_276_; uint8_t v_isShared_277_; uint8_t v_isSharedCheck_297_; 
v_r_272_ = lean_ctor_get(v_impl_186_, 4);
v_k_273_ = lean_ctor_get(v_impl_186_, 1);
v_v_274_ = lean_ctor_get(v_impl_186_, 2);
v_isSharedCheck_297_ = !lean_is_exclusive(v_impl_186_);
if (v_isSharedCheck_297_ == 0)
{
lean_object* v_unused_298_; lean_object* v_unused_299_; 
v_unused_298_ = lean_ctor_get(v_impl_186_, 3);
lean_dec(v_unused_298_);
v_unused_299_ = lean_ctor_get(v_impl_186_, 0);
lean_dec(v_unused_299_);
v___x_276_ = v_impl_186_;
v_isShared_277_ = v_isSharedCheck_297_;
goto v_resetjp_275_;
}
else
{
lean_inc(v_r_272_);
lean_inc(v_v_274_);
lean_inc(v_k_273_);
lean_dec(v_impl_186_);
v___x_276_ = lean_box(0);
v_isShared_277_ = v_isSharedCheck_297_;
goto v_resetjp_275_;
}
v_resetjp_275_:
{
lean_object* v_k_278_; lean_object* v_v_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_293_; 
v_k_278_ = lean_ctor_get(v_l_271_, 1);
v_v_279_ = lean_ctor_get(v_l_271_, 2);
v_isSharedCheck_293_ = !lean_is_exclusive(v_l_271_);
if (v_isSharedCheck_293_ == 0)
{
lean_object* v_unused_294_; lean_object* v_unused_295_; lean_object* v_unused_296_; 
v_unused_294_ = lean_ctor_get(v_l_271_, 4);
lean_dec(v_unused_294_);
v_unused_295_ = lean_ctor_get(v_l_271_, 3);
lean_dec(v_unused_295_);
v_unused_296_ = lean_ctor_get(v_l_271_, 0);
lean_dec(v_unused_296_);
v___x_281_ = v_l_271_;
v_isShared_282_ = v_isSharedCheck_293_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_v_279_);
lean_inc(v_k_278_);
lean_dec(v_l_271_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_293_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_283_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_272_, 2);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 4, v_r_272_);
lean_ctor_set(v___x_281_, 3, v_r_272_);
lean_ctor_set(v___x_281_, 2, v_v_39_);
lean_ctor_set(v___x_281_, 1, v_k_38_);
lean_ctor_set(v___x_281_, 0, v___x_187_);
v___x_285_ = v___x_281_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_292_, 3, v_r_272_);
lean_ctor_set(v_reuseFailAlloc_292_, 4, v_r_272_);
v___x_285_ = v_reuseFailAlloc_292_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
lean_object* v___x_287_; 
lean_inc(v_r_272_);
if (v_isShared_277_ == 0)
{
lean_ctor_set(v___x_276_, 3, v_r_272_);
lean_ctor_set(v___x_276_, 0, v___x_187_);
v___x_287_ = v___x_276_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_k_273_);
lean_ctor_set(v_reuseFailAlloc_291_, 2, v_v_274_);
lean_ctor_set(v_reuseFailAlloc_291_, 3, v_r_272_);
lean_ctor_set(v_reuseFailAlloc_291_, 4, v_r_272_);
v___x_287_ = v_reuseFailAlloc_291_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_289_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v___x_287_);
lean_ctor_set(v___x_43_, 3, v___x_285_);
lean_ctor_set(v___x_43_, 2, v_v_279_);
lean_ctor_set(v___x_43_, 1, v_k_278_);
lean_ctor_set(v___x_43_, 0, v___x_283_);
v___x_289_ = v___x_43_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_k_278_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_v_279_);
lean_ctor_set(v_reuseFailAlloc_290_, 3, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_290_, 4, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
}
}
}
else
{
lean_object* v_r_300_; 
v_r_300_ = lean_ctor_get(v_impl_186_, 4);
lean_inc(v_r_300_);
if (lean_obj_tag(v_r_300_) == 0)
{
lean_object* v_k_301_; lean_object* v_v_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_313_; 
v_k_301_ = lean_ctor_get(v_impl_186_, 1);
v_v_302_ = lean_ctor_get(v_impl_186_, 2);
v_isSharedCheck_313_ = !lean_is_exclusive(v_impl_186_);
if (v_isSharedCheck_313_ == 0)
{
lean_object* v_unused_314_; lean_object* v_unused_315_; lean_object* v_unused_316_; 
v_unused_314_ = lean_ctor_get(v_impl_186_, 4);
lean_dec(v_unused_314_);
v_unused_315_ = lean_ctor_get(v_impl_186_, 3);
lean_dec(v_unused_315_);
v_unused_316_ = lean_ctor_get(v_impl_186_, 0);
lean_dec(v_unused_316_);
v___x_304_ = v_impl_186_;
v_isShared_305_ = v_isSharedCheck_313_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_v_302_);
lean_inc(v_k_301_);
lean_dec(v_impl_186_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_313_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_308_; 
v___x_306_ = lean_unsigned_to_nat(3u);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 4, v_l_271_);
lean_ctor_set(v___x_304_, 2, v_v_39_);
lean_ctor_set(v___x_304_, 1, v_k_38_);
lean_ctor_set(v___x_304_, 0, v___x_187_);
v___x_308_ = v___x_304_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_312_; 
v_reuseFailAlloc_312_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_312_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_312_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_312_, 3, v_l_271_);
lean_ctor_set(v_reuseFailAlloc_312_, 4, v_l_271_);
v___x_308_ = v_reuseFailAlloc_312_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_310_; 
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v_r_300_);
lean_ctor_set(v___x_43_, 3, v___x_308_);
lean_ctor_set(v___x_43_, 2, v_v_302_);
lean_ctor_set(v___x_43_, 1, v_k_301_);
lean_ctor_set(v___x_43_, 0, v___x_306_);
v___x_310_ = v___x_43_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_311_; 
v_reuseFailAlloc_311_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_311_, 0, v___x_306_);
lean_ctor_set(v_reuseFailAlloc_311_, 1, v_k_301_);
lean_ctor_set(v_reuseFailAlloc_311_, 2, v_v_302_);
lean_ctor_set(v_reuseFailAlloc_311_, 3, v___x_308_);
lean_ctor_set(v_reuseFailAlloc_311_, 4, v_r_300_);
v___x_310_ = v_reuseFailAlloc_311_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
return v___x_310_;
}
}
}
}
else
{
lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_317_ = lean_unsigned_to_nat(2u);
if (v_isShared_44_ == 0)
{
lean_ctor_set(v___x_43_, 4, v_impl_186_);
lean_ctor_set(v___x_43_, 3, v_r_300_);
lean_ctor_set(v___x_43_, 0, v___x_317_);
v___x_319_ = v___x_43_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v_k_38_);
lean_ctor_set(v_reuseFailAlloc_320_, 2, v_v_39_);
lean_ctor_set(v_reuseFailAlloc_320_, 3, v_r_300_);
lean_ctor_set(v_reuseFailAlloc_320_, 4, v_impl_186_);
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
}
}
}
else
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_k_34_);
lean_ctor_set(v___x_323_, 2, v_v_35_);
lean_ctor_set(v___x_323_, 3, v_t_36_);
lean_ctor_set(v___x_323_, 4, v_t_36_);
return v___x_323_;
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3(lean_object* v_a_324_, lean_object* v_as_325_, size_t v_i_326_, size_t v_stop_327_){
_start:
{
uint8_t v___x_328_; 
v___x_328_ = lean_usize_dec_eq(v_i_326_, v_stop_327_);
if (v___x_328_ == 0)
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_array_uget_borrowed(v_as_325_, v_i_326_);
v___x_330_ = lean_expr_eqv(v_a_324_, v___x_329_);
if (v___x_330_ == 0)
{
size_t v___x_331_; size_t v___x_332_; 
v___x_331_ = ((size_t)1ULL);
v___x_332_ = lean_usize_add(v_i_326_, v___x_331_);
v_i_326_ = v___x_332_;
goto _start;
}
else
{
return v___x_330_;
}
}
else
{
uint8_t v___x_334_; 
v___x_334_ = 0;
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3___boxed(lean_object* v_a_335_, lean_object* v_as_336_, lean_object* v_i_337_, lean_object* v_stop_338_){
_start:
{
size_t v_i_boxed_339_; size_t v_stop_boxed_340_; uint8_t v_res_341_; lean_object* v_r_342_; 
v_i_boxed_339_ = lean_unbox_usize(v_i_337_);
lean_dec(v_i_337_);
v_stop_boxed_340_ = lean_unbox_usize(v_stop_338_);
lean_dec(v_stop_338_);
v_res_341_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3(v_a_335_, v_as_336_, v_i_boxed_339_, v_stop_boxed_340_);
lean_dec_ref(v_as_336_);
lean_dec_ref(v_a_335_);
v_r_342_ = lean_box(v_res_341_);
return v_r_342_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(lean_object* v_as_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; uint8_t v___x_347_; 
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_array_get_size(v_as_343_);
v___x_347_ = lean_nat_dec_lt(v___x_345_, v___x_346_);
if (v___x_347_ == 0)
{
return v___x_347_;
}
else
{
if (v___x_347_ == 0)
{
return v___x_347_;
}
else
{
size_t v___x_348_; size_t v___x_349_; uint8_t v___x_350_; 
v___x_348_ = ((size_t)0ULL);
v___x_349_ = lean_usize_of_nat(v___x_346_);
v___x_350_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1_spec__3(v_a_344_, v_as_343_, v___x_348_, v___x_349_);
return v___x_350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1___boxed(lean_object* v_as_351_, lean_object* v_a_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(v_as_351_, v_a_352_);
lean_dec_ref(v_a_352_);
lean_dec_ref(v_as_351_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(lean_object* v_ctx_355_, lean_object* v_i_356_, lean_object* v_acc_357_){
_start:
{
if (lean_obj_tag(v_i_356_) == 1)
{
lean_object* v_i_358_; lean_object* v_toElabInfo_359_; lean_object* v_expr_360_; lean_object* v_stx_361_; uint8_t v___x_362_; lean_object* v___x_363_; 
v_i_358_ = lean_ctor_get(v_i_356_, 0);
v_toElabInfo_359_ = lean_ctor_get(v_i_358_, 0);
v_expr_360_ = lean_ctor_get(v_i_358_, 3);
v_stx_361_ = lean_ctor_get(v_toElabInfo_359_, 1);
v___x_362_ = 1;
v___x_363_ = l_Lean_Syntax_getRange_x3f(v_stx_361_, v___x_362_);
if (lean_obj_tag(v___x_363_) == 1)
{
lean_object* v_val_364_; uint8_t v___x_365_; 
v_val_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_val_364_);
lean_dec_ref_known(v___x_363_, 1);
v___x_365_ = l_Lean_Expr_isFVar(v_expr_360_);
if (v___x_365_ == 0)
{
lean_dec(v_val_364_);
return v_acc_357_;
}
else
{
lean_object* v_autoImplicits_366_; uint8_t v___x_367_; 
v_autoImplicits_366_ = lean_ctor_get(v_ctx_355_, 2);
v___x_367_ = l_Array_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__1(v_autoImplicits_366_, v_expr_360_);
if (v___x_367_ == 0)
{
lean_dec(v_val_364_);
return v_acc_357_;
}
else
{
uint8_t v___x_368_; 
v___x_368_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_val_364_, v_acc_357_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_box(0);
v___x_370_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_val_364_, v___x_369_, v_acc_357_);
return v___x_370_;
}
else
{
lean_dec(v_val_364_);
return v_acc_357_;
}
}
}
}
else
{
lean_dec(v___x_363_);
return v_acc_357_;
}
}
else
{
return v_acc_357_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0___boxed(lean_object* v_ctx_371_, lean_object* v_i_372_, lean_object* v_acc_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___lam__0(v_ctx_371_, v_i_372_, v_acc_373_);
lean_dec_ref(v_i_372_);
lean_dec_ref(v_ctx_371_);
return v_res_374_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0(lean_object* v_x_375_){
_start:
{
lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_376_ = l_Lean_unknownIdentifierMessageTag;
v___x_377_ = lean_name_eq(v_x_375_, v___x_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0___boxed(lean_object* v_x_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___lam__0(v_x_378_);
lean_dec(v_x_378_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(lean_object* v_text_382_, lean_object* v_requestedRange_383_, lean_object* v_as_384_, size_t v_sz_385_, size_t v_i_386_, lean_object* v_b_387_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = lean_usize_dec_lt(v_i_386_, v_sz_385_);
if (v___x_389_ == 0)
{
return v_b_387_;
}
else
{
lean_object* v_snd_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_417_; 
v_snd_390_ = lean_ctor_get(v_b_387_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_b_387_);
if (v_isSharedCheck_417_ == 0)
{
lean_object* v_unused_418_; 
v_unused_418_ = lean_ctor_get(v_b_387_, 0);
lean_dec(v_unused_418_);
v___x_392_ = v_b_387_;
v_isShared_393_ = v_isSharedCheck_417_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_snd_390_);
lean_dec(v_b_387_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_417_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v_a_394_; lean_object* v_pos_395_; lean_object* v_endPos_396_; lean_object* v_data_397_; lean_object* v___f_398_; lean_object* v___x_399_; lean_object* v_a_401_; uint8_t v___x_408_; 
v_a_394_ = lean_array_uget_borrowed(v_as_384_, v_i_386_);
v_pos_395_ = lean_ctor_get(v_a_394_, 1);
v_endPos_396_ = lean_ctor_get(v_a_394_, 2);
v_data_397_ = lean_ctor_get(v_a_394_, 4);
v___f_398_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_399_ = lean_box(0);
lean_inc(v_data_397_);
v___x_408_ = l_Lean_MessageData_hasTag(v___f_398_, v_data_397_);
if (v___x_408_ == 0)
{
v_a_401_ = v_snd_390_;
goto v___jp_400_;
}
else
{
lean_object* v___x_409_; lean_object* v___y_411_; 
lean_inc_ref(v_pos_395_);
v___x_409_ = l_Lean_FileMap_ofPosition(v_text_382_, v_pos_395_);
if (lean_obj_tag(v_endPos_396_) == 0)
{
lean_inc_ref(v_pos_395_);
v___y_411_ = v_pos_395_;
goto v___jp_410_;
}
else
{
lean_object* v_val_416_; 
v_val_416_ = lean_ctor_get(v_endPos_396_, 0);
lean_inc(v_val_416_);
v___y_411_ = v_val_416_;
goto v___jp_410_;
}
v___jp_410_:
{
lean_object* v___x_412_; lean_object* v_msgRange_413_; uint8_t v___x_414_; 
v___x_412_ = l_Lean_FileMap_ofPosition(v_text_382_, v___y_411_);
v_msgRange_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_413_, 0, v___x_409_);
lean_ctor_set(v_msgRange_413_, 1, v___x_412_);
v___x_414_ = l_Lean_Syntax_Range_overlaps(v_msgRange_413_, v_requestedRange_383_, v___x_408_, v___x_408_);
if (v___x_414_ == 0)
{
lean_dec_ref_known(v_msgRange_413_, 2);
v_a_401_ = v_snd_390_;
goto v___jp_400_;
}
else
{
lean_object* v_ranges_415_; 
v_ranges_415_ = lean_array_push(v_snd_390_, v_msgRange_413_);
v_a_401_ = v_ranges_415_;
goto v___jp_400_;
}
}
}
v___jp_400_:
{
lean_object* v___x_403_; 
if (v_isShared_393_ == 0)
{
lean_ctor_set(v___x_392_, 1, v_a_401_);
lean_ctor_set(v___x_392_, 0, v___x_399_);
v___x_403_ = v___x_392_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_a_401_);
v___x_403_ = v_reuseFailAlloc_407_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
size_t v___x_404_; size_t v___x_405_; 
v___x_404_ = ((size_t)1ULL);
v___x_405_ = lean_usize_add(v_i_386_, v___x_404_);
v_i_386_ = v___x_405_;
v_b_387_ = v___x_403_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_text_419_, lean_object* v_requestedRange_420_, lean_object* v_as_421_, lean_object* v_sz_422_, lean_object* v_i_423_, lean_object* v_b_424_, lean_object* v___y_425_){
_start:
{
size_t v_sz_boxed_426_; size_t v_i_boxed_427_; lean_object* v_res_428_; 
v_sz_boxed_426_ = lean_unbox_usize(v_sz_422_);
lean_dec(v_sz_422_);
v_i_boxed_427_ = lean_unbox_usize(v_i_423_);
lean_dec(v_i_423_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(v_text_419_, v_requestedRange_420_, v_as_421_, v_sz_boxed_426_, v_i_boxed_427_, v_b_424_);
lean_dec_ref(v_as_421_);
lean_dec_ref(v_requestedRange_420_);
lean_dec_ref(v_text_419_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(lean_object* v_text_429_, lean_object* v_requestedRange_430_, lean_object* v_as_431_, size_t v_sz_432_, size_t v_i_433_, lean_object* v_b_434_){
_start:
{
uint8_t v___x_436_; 
v___x_436_ = lean_usize_dec_lt(v_i_433_, v_sz_432_);
if (v___x_436_ == 0)
{
return v_b_434_;
}
else
{
lean_object* v_snd_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_464_; 
v_snd_437_ = lean_ctor_get(v_b_434_, 1);
v_isSharedCheck_464_ = !lean_is_exclusive(v_b_434_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; 
v_unused_465_ = lean_ctor_get(v_b_434_, 0);
lean_dec(v_unused_465_);
v___x_439_ = v_b_434_;
v_isShared_440_ = v_isSharedCheck_464_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_snd_437_);
lean_dec(v_b_434_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_464_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v_a_441_; lean_object* v_pos_442_; lean_object* v_endPos_443_; lean_object* v_data_444_; lean_object* v___f_445_; lean_object* v___x_446_; lean_object* v_a_448_; uint8_t v___x_455_; 
v_a_441_ = lean_array_uget_borrowed(v_as_431_, v_i_433_);
v_pos_442_ = lean_ctor_get(v_a_441_, 1);
v_endPos_443_ = lean_ctor_get(v_a_441_, 2);
v_data_444_ = lean_ctor_get(v_a_441_, 4);
v___f_445_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_446_ = lean_box(0);
lean_inc(v_data_444_);
v___x_455_ = l_Lean_MessageData_hasTag(v___f_445_, v_data_444_);
if (v___x_455_ == 0)
{
v_a_448_ = v_snd_437_;
goto v___jp_447_;
}
else
{
lean_object* v___x_456_; lean_object* v___y_458_; 
lean_inc_ref(v_pos_442_);
v___x_456_ = l_Lean_FileMap_ofPosition(v_text_429_, v_pos_442_);
if (lean_obj_tag(v_endPos_443_) == 0)
{
lean_inc_ref(v_pos_442_);
v___y_458_ = v_pos_442_;
goto v___jp_457_;
}
else
{
lean_object* v_val_463_; 
v_val_463_ = lean_ctor_get(v_endPos_443_, 0);
lean_inc(v_val_463_);
v___y_458_ = v_val_463_;
goto v___jp_457_;
}
v___jp_457_:
{
lean_object* v___x_459_; lean_object* v_msgRange_460_; uint8_t v___x_461_; 
v___x_459_ = l_Lean_FileMap_ofPosition(v_text_429_, v___y_458_);
v_msgRange_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_460_, 0, v___x_456_);
lean_ctor_set(v_msgRange_460_, 1, v___x_459_);
v___x_461_ = l_Lean_Syntax_Range_overlaps(v_msgRange_460_, v_requestedRange_430_, v___x_455_, v___x_455_);
if (v___x_461_ == 0)
{
lean_dec_ref_known(v_msgRange_460_, 2);
v_a_448_ = v_snd_437_;
goto v___jp_447_;
}
else
{
lean_object* v_ranges_462_; 
v_ranges_462_ = lean_array_push(v_snd_437_, v_msgRange_460_);
v_a_448_ = v_ranges_462_;
goto v___jp_447_;
}
}
}
v___jp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 1, v_a_448_);
lean_ctor_set(v___x_439_, 0, v___x_446_);
v___x_450_ = v___x_439_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_a_448_);
v___x_450_ = v_reuseFailAlloc_454_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; 
v___x_451_ = ((size_t)1ULL);
v___x_452_ = lean_usize_add(v_i_433_, v___x_451_);
v___x_453_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7(v_text_429_, v_requestedRange_430_, v_as_431_, v_sz_432_, v___x_452_, v___x_450_);
return v___x_453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2___boxed(lean_object* v_text_466_, lean_object* v_requestedRange_467_, lean_object* v_as_468_, lean_object* v_sz_469_, lean_object* v_i_470_, lean_object* v_b_471_, lean_object* v___y_472_){
_start:
{
size_t v_sz_boxed_473_; size_t v_i_boxed_474_; lean_object* v_res_475_; 
v_sz_boxed_473_ = lean_unbox_usize(v_sz_469_);
lean_dec(v_sz_469_);
v_i_boxed_474_ = lean_unbox_usize(v_i_470_);
lean_dec(v_i_470_);
v_res_475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(v_text_466_, v_requestedRange_467_, v_as_468_, v_sz_boxed_473_, v_i_boxed_474_, v_b_471_);
lean_dec_ref(v_as_468_);
lean_dec_ref(v_requestedRange_467_);
lean_dec_ref(v_text_466_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(lean_object* v_init_476_, lean_object* v_text_477_, lean_object* v_requestedRange_478_, lean_object* v_n_479_, lean_object* v_b_480_){
_start:
{
if (lean_obj_tag(v_n_479_) == 0)
{
lean_object* v_cs_482_; lean_object* v___x_483_; lean_object* v___x_484_; size_t v_sz_485_; size_t v___x_486_; lean_object* v___x_487_; lean_object* v_fst_488_; 
v_cs_482_ = lean_ctor_get(v_n_479_, 0);
v___x_483_ = lean_box(0);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v_b_480_);
v_sz_485_ = lean_array_size(v_cs_482_);
v___x_486_ = ((size_t)0ULL);
v___x_487_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_476_, v_text_477_, v_requestedRange_478_, v_cs_482_, v_sz_485_, v___x_486_, v___x_484_);
v_fst_488_ = lean_ctor_get(v___x_487_, 0);
lean_inc(v_fst_488_);
if (lean_obj_tag(v_fst_488_) == 0)
{
lean_object* v_snd_489_; lean_object* v___x_490_; 
v_snd_489_ = lean_ctor_get(v___x_487_, 1);
lean_inc(v_snd_489_);
lean_dec_ref(v___x_487_);
v___x_490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_490_, 0, v_snd_489_);
return v___x_490_;
}
else
{
lean_object* v_val_491_; 
lean_dec_ref(v___x_487_);
v_val_491_ = lean_ctor_get(v_fst_488_, 0);
lean_inc(v_val_491_);
lean_dec_ref_known(v_fst_488_, 1);
return v_val_491_;
}
}
else
{
lean_object* v_vs_492_; lean_object* v___x_493_; lean_object* v___x_494_; size_t v_sz_495_; size_t v___x_496_; lean_object* v___x_497_; lean_object* v_fst_498_; 
v_vs_492_ = lean_ctor_get(v_n_479_, 0);
v___x_493_ = lean_box(0);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v_b_480_);
v_sz_495_ = lean_array_size(v_vs_492_);
v___x_496_ = ((size_t)0ULL);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(v_text_477_, v_requestedRange_478_, v_vs_492_, v_sz_495_, v___x_496_, v___x_494_);
v_fst_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_fst_498_);
if (lean_obj_tag(v_fst_498_) == 0)
{
lean_object* v_snd_499_; lean_object* v___x_500_; 
v_snd_499_ = lean_ctor_get(v___x_497_, 1);
lean_inc(v_snd_499_);
lean_dec_ref(v___x_497_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v_snd_499_);
return v___x_500_;
}
else
{
lean_object* v_val_501_; 
lean_dec_ref(v___x_497_);
v_val_501_ = lean_ctor_get(v_fst_498_, 0);
lean_inc(v_val_501_);
lean_dec_ref_known(v_fst_498_, 1);
return v_val_501_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(lean_object* v_init_502_, lean_object* v_text_503_, lean_object* v_requestedRange_504_, lean_object* v_as_505_, size_t v_sz_506_, size_t v_i_507_, lean_object* v_b_508_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = lean_usize_dec_lt(v_i_507_, v_sz_506_);
if (v___x_510_ == 0)
{
return v_b_508_;
}
else
{
lean_object* v_snd_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_529_; 
v_snd_511_ = lean_ctor_get(v_b_508_, 1);
v_isSharedCheck_529_ = !lean_is_exclusive(v_b_508_);
if (v_isSharedCheck_529_ == 0)
{
lean_object* v_unused_530_; 
v_unused_530_ = lean_ctor_get(v_b_508_, 0);
lean_dec(v_unused_530_);
v___x_513_ = v_b_508_;
v_isShared_514_ = v_isSharedCheck_529_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_snd_511_);
lean_dec(v_b_508_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_529_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_a_515_; lean_object* v___x_516_; 
v_a_515_ = lean_array_uget_borrowed(v_as_505_, v_i_507_);
lean_inc(v_snd_511_);
v___x_516_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_502_, v_text_503_, v_requestedRange_504_, v_a_515_, v_snd_511_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_517_);
v___x_519_ = v___x_513_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_snd_511_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
else
{
lean_object* v_a_521_; lean_object* v___x_522_; lean_object* v___x_524_; 
lean_dec(v_snd_511_);
v_a_521_ = lean_ctor_get(v___x_516_, 0);
lean_inc(v_a_521_);
lean_dec_ref_known(v___x_516_, 1);
v___x_522_ = lean_box(0);
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 1, v_a_521_);
lean_ctor_set(v___x_513_, 0, v___x_522_);
v___x_524_ = v___x_513_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_528_, 1, v_a_521_);
v___x_524_ = v_reuseFailAlloc_528_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
size_t v___x_525_; size_t v___x_526_; 
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_i_507_, v___x_525_);
v_i_507_ = v___x_526_;
v_b_508_ = v___x_524_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1___boxed(lean_object* v_init_531_, lean_object* v_text_532_, lean_object* v_requestedRange_533_, lean_object* v_as_534_, lean_object* v_sz_535_, lean_object* v_i_536_, lean_object* v_b_537_, lean_object* v___y_538_){
_start:
{
size_t v_sz_boxed_539_; size_t v_i_boxed_540_; lean_object* v_res_541_; 
v_sz_boxed_539_ = lean_unbox_usize(v_sz_535_);
lean_dec(v_sz_535_);
v_i_boxed_540_ = lean_unbox_usize(v_i_536_);
lean_dec(v_i_536_);
v_res_541_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_531_, v_text_532_, v_requestedRange_533_, v_as_534_, v_sz_boxed_539_, v_i_boxed_540_, v_b_537_);
lean_dec_ref(v_as_534_);
lean_dec_ref(v_requestedRange_533_);
lean_dec_ref(v_text_532_);
lean_dec_ref(v_init_531_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(lean_object* v_init_542_, lean_object* v_text_543_, lean_object* v_requestedRange_544_, lean_object* v_n_545_, lean_object* v_b_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_542_, v_text_543_, v_requestedRange_544_, v_n_545_, v_b_546_);
lean_dec_ref(v_n_545_);
lean_dec_ref(v_requestedRange_544_);
lean_dec_ref(v_text_543_);
lean_dec_ref(v_init_542_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(lean_object* v_text_549_, lean_object* v_requestedRange_550_, lean_object* v_as_551_, size_t v_sz_552_, size_t v_i_553_, lean_object* v_b_554_){
_start:
{
uint8_t v___x_556_; 
v___x_556_ = lean_usize_dec_lt(v_i_553_, v_sz_552_);
if (v___x_556_ == 0)
{
return v_b_554_;
}
else
{
lean_object* v_snd_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_584_; 
v_snd_557_ = lean_ctor_get(v_b_554_, 1);
v_isSharedCheck_584_ = !lean_is_exclusive(v_b_554_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v_b_554_, 0);
lean_dec(v_unused_585_);
v___x_559_ = v_b_554_;
v_isShared_560_ = v_isSharedCheck_584_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_snd_557_);
lean_dec(v_b_554_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_584_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v_a_561_; lean_object* v_pos_562_; lean_object* v_endPos_563_; lean_object* v_data_564_; lean_object* v___f_565_; lean_object* v___x_566_; lean_object* v_a_568_; uint8_t v___x_575_; 
v_a_561_ = lean_array_uget_borrowed(v_as_551_, v_i_553_);
v_pos_562_ = lean_ctor_get(v_a_561_, 1);
v_endPos_563_ = lean_ctor_get(v_a_561_, 2);
v_data_564_ = lean_ctor_get(v_a_561_, 4);
v___f_565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_566_ = lean_box(0);
lean_inc(v_data_564_);
v___x_575_ = l_Lean_MessageData_hasTag(v___f_565_, v_data_564_);
if (v___x_575_ == 0)
{
v_a_568_ = v_snd_557_;
goto v___jp_567_;
}
else
{
lean_object* v___x_576_; lean_object* v___y_578_; 
lean_inc_ref(v_pos_562_);
v___x_576_ = l_Lean_FileMap_ofPosition(v_text_549_, v_pos_562_);
if (lean_obj_tag(v_endPos_563_) == 0)
{
lean_inc_ref(v_pos_562_);
v___y_578_ = v_pos_562_;
goto v___jp_577_;
}
else
{
lean_object* v_val_583_; 
v_val_583_ = lean_ctor_get(v_endPos_563_, 0);
lean_inc(v_val_583_);
v___y_578_ = v_val_583_;
goto v___jp_577_;
}
v___jp_577_:
{
lean_object* v___x_579_; lean_object* v_msgRange_580_; uint8_t v___x_581_; 
v___x_579_ = l_Lean_FileMap_ofPosition(v_text_549_, v___y_578_);
v_msgRange_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_580_, 0, v___x_576_);
lean_ctor_set(v_msgRange_580_, 1, v___x_579_);
v___x_581_ = l_Lean_Syntax_Range_overlaps(v_msgRange_580_, v_requestedRange_550_, v___x_575_, v___x_575_);
if (v___x_581_ == 0)
{
lean_dec_ref_known(v_msgRange_580_, 2);
v_a_568_ = v_snd_557_;
goto v___jp_567_;
}
else
{
lean_object* v_ranges_582_; 
v_ranges_582_ = lean_array_push(v_snd_557_, v_msgRange_580_);
v_a_568_ = v_ranges_582_;
goto v___jp_567_;
}
}
}
v___jp_567_:
{
lean_object* v___x_570_; 
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v_a_568_);
lean_ctor_set(v___x_559_, 0, v___x_566_);
v___x_570_ = v___x_559_;
goto v_reusejp_569_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_a_568_);
v___x_570_ = v_reuseFailAlloc_574_;
goto v_reusejp_569_;
}
v_reusejp_569_:
{
size_t v___x_571_; size_t v___x_572_; 
v___x_571_ = ((size_t)1ULL);
v___x_572_ = lean_usize_add(v_i_553_, v___x_571_);
v_i_553_ = v___x_572_;
v_b_554_ = v___x_570_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4___boxed(lean_object* v_text_586_, lean_object* v_requestedRange_587_, lean_object* v_as_588_, lean_object* v_sz_589_, lean_object* v_i_590_, lean_object* v_b_591_, lean_object* v___y_592_){
_start:
{
size_t v_sz_boxed_593_; size_t v_i_boxed_594_; lean_object* v_res_595_; 
v_sz_boxed_593_ = lean_unbox_usize(v_sz_589_);
lean_dec(v_sz_589_);
v_i_boxed_594_ = lean_unbox_usize(v_i_590_);
lean_dec(v_i_590_);
v_res_595_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(v_text_586_, v_requestedRange_587_, v_as_588_, v_sz_boxed_593_, v_i_boxed_594_, v_b_591_);
lean_dec_ref(v_as_588_);
lean_dec_ref(v_requestedRange_587_);
lean_dec_ref(v_text_586_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(lean_object* v_text_596_, lean_object* v_requestedRange_597_, lean_object* v_as_598_, size_t v_sz_599_, size_t v_i_600_, lean_object* v_b_601_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = lean_usize_dec_lt(v_i_600_, v_sz_599_);
if (v___x_603_ == 0)
{
return v_b_601_;
}
else
{
lean_object* v_snd_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_631_; 
v_snd_604_ = lean_ctor_get(v_b_601_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_b_601_);
if (v_isSharedCheck_631_ == 0)
{
lean_object* v_unused_632_; 
v_unused_632_ = lean_ctor_get(v_b_601_, 0);
lean_dec(v_unused_632_);
v___x_606_ = v_b_601_;
v_isShared_607_ = v_isSharedCheck_631_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snd_604_);
lean_dec(v_b_601_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_631_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v_a_608_; lean_object* v_pos_609_; lean_object* v_endPos_610_; lean_object* v_data_611_; lean_object* v___f_612_; lean_object* v___x_613_; lean_object* v_a_615_; uint8_t v___x_622_; 
v_a_608_ = lean_array_uget_borrowed(v_as_598_, v_i_600_);
v_pos_609_ = lean_ctor_get(v_a_608_, 1);
v_endPos_610_ = lean_ctor_get(v_a_608_, 2);
v_data_611_ = lean_ctor_get(v_a_608_, 4);
v___f_612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_613_ = lean_box(0);
lean_inc(v_data_611_);
v___x_622_ = l_Lean_MessageData_hasTag(v___f_612_, v_data_611_);
if (v___x_622_ == 0)
{
v_a_615_ = v_snd_604_;
goto v___jp_614_;
}
else
{
lean_object* v___x_623_; lean_object* v___y_625_; 
lean_inc_ref(v_pos_609_);
v___x_623_ = l_Lean_FileMap_ofPosition(v_text_596_, v_pos_609_);
if (lean_obj_tag(v_endPos_610_) == 0)
{
lean_inc_ref(v_pos_609_);
v___y_625_ = v_pos_609_;
goto v___jp_624_;
}
else
{
lean_object* v_val_630_; 
v_val_630_ = lean_ctor_get(v_endPos_610_, 0);
lean_inc(v_val_630_);
v___y_625_ = v_val_630_;
goto v___jp_624_;
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v_msgRange_627_; uint8_t v___x_628_; 
v___x_626_ = l_Lean_FileMap_ofPosition(v_text_596_, v___y_625_);
v_msgRange_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_627_, 0, v___x_623_);
lean_ctor_set(v_msgRange_627_, 1, v___x_626_);
v___x_628_ = l_Lean_Syntax_Range_overlaps(v_msgRange_627_, v_requestedRange_597_, v___x_622_, v___x_622_);
if (v___x_628_ == 0)
{
lean_dec_ref_known(v_msgRange_627_, 2);
v_a_615_ = v_snd_604_;
goto v___jp_614_;
}
else
{
lean_object* v_ranges_629_; 
v_ranges_629_ = lean_array_push(v_snd_604_, v_msgRange_627_);
v_a_615_ = v_ranges_629_;
goto v___jp_614_;
}
}
}
v___jp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v_a_615_);
lean_ctor_set(v___x_606_, 0, v___x_613_);
v___x_617_ = v___x_606_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_613_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_a_615_);
v___x_617_ = v_reuseFailAlloc_621_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
size_t v___x_618_; size_t v___x_619_; lean_object* v___x_620_; 
v___x_618_ = ((size_t)1ULL);
v___x_619_ = lean_usize_add(v_i_600_, v___x_618_);
v___x_620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(v_text_596_, v_requestedRange_597_, v_as_598_, v_sz_599_, v___x_619_, v___x_617_);
return v___x_620_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___boxed(lean_object* v_text_633_, lean_object* v_requestedRange_634_, lean_object* v_as_635_, lean_object* v_sz_636_, lean_object* v_i_637_, lean_object* v_b_638_, lean_object* v___y_639_){
_start:
{
size_t v_sz_boxed_640_; size_t v_i_boxed_641_; lean_object* v_res_642_; 
v_sz_boxed_640_ = lean_unbox_usize(v_sz_636_);
lean_dec(v_sz_636_);
v_i_boxed_641_ = lean_unbox_usize(v_i_637_);
lean_dec(v_i_637_);
v_res_642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_633_, v_requestedRange_634_, v_as_635_, v_sz_boxed_640_, v_i_boxed_641_, v_b_638_);
lean_dec_ref(v_as_635_);
lean_dec_ref(v_requestedRange_634_);
lean_dec_ref(v_text_633_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(lean_object* v_text_643_, lean_object* v_requestedRange_644_, lean_object* v_t_645_, lean_object* v_init_646_){
_start:
{
lean_object* v_root_648_; lean_object* v_tail_649_; lean_object* v___x_650_; 
v_root_648_ = lean_ctor_get(v_t_645_, 0);
v_tail_649_ = lean_ctor_get(v_t_645_, 1);
lean_inc_ref(v_init_646_);
v___x_650_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_646_, v_text_643_, v_requestedRange_644_, v_root_648_, v_init_646_);
lean_dec_ref(v_init_646_);
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v_a_651_; 
v_a_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v___x_650_, 1);
return v_a_651_;
}
else
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v___x_654_; size_t v_sz_655_; size_t v___x_656_; lean_object* v___x_657_; lean_object* v_fst_658_; 
v_a_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_652_);
lean_dec_ref_known(v___x_650_, 1);
v___x_653_ = lean_box(0);
v___x_654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
lean_ctor_set(v___x_654_, 1, v_a_652_);
v_sz_655_ = lean_array_size(v_tail_649_);
v___x_656_ = ((size_t)0ULL);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_643_, v_requestedRange_644_, v_tail_649_, v_sz_655_, v___x_656_, v___x_654_);
v_fst_658_ = lean_ctor_get(v___x_657_, 0);
lean_inc(v_fst_658_);
if (lean_obj_tag(v_fst_658_) == 0)
{
lean_object* v_snd_659_; 
v_snd_659_ = lean_ctor_get(v___x_657_, 1);
lean_inc(v_snd_659_);
lean_dec_ref(v___x_657_);
return v_snd_659_;
}
else
{
lean_object* v_val_660_; 
lean_dec_ref(v___x_657_);
v_val_660_ = lean_ctor_get(v_fst_658_, 0);
lean_inc(v_val_660_);
lean_dec_ref_known(v_fst_658_, 1);
return v_val_660_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___boxed(lean_object* v_text_661_, lean_object* v_requestedRange_662_, lean_object* v_t_663_, lean_object* v_init_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_661_, v_requestedRange_662_, v_t_663_, v_init_664_);
lean_dec_ref(v_t_663_);
lean_dec_ref(v_requestedRange_662_);
lean_dec_ref(v_text_661_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(lean_object* v_init_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_668_) == 0)
{
lean_object* v_k_669_; lean_object* v_l_670_; lean_object* v_r_671_; lean_object* v___x_672_; lean_object* v___x_673_; 
v_k_669_ = lean_ctor_get(v_x_668_, 1);
lean_inc(v_k_669_);
v_l_670_ = lean_ctor_get(v_x_668_, 3);
lean_inc(v_l_670_);
v_r_671_ = lean_ctor_get(v_x_668_, 4);
lean_inc(v_r_671_);
lean_dec_ref_known(v_x_668_, 5);
v___x_672_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v_init_667_, v_l_670_);
v___x_673_ = lean_array_push(v___x_672_, v_k_669_);
v_init_667_ = v___x_673_;
v_x_668_ = v_r_671_;
goto _start;
}
else
{
return v_init_667_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object* v_doc_682_, lean_object* v_requestedRange_683_){
_start:
{
lean_object* v_toEditableDocumentCore_685_; lean_object* v_start_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v_toEditableDocumentCore_685_ = lean_ctor_get(v_doc_682_, 0);
lean_inc_ref(v_toEditableDocumentCore_685_);
v_start_686_ = lean_ctor_get(v_requestedRange_683_, 0);
lean_inc(v_start_686_);
v___x_687_ = l_Lean_Server_RequestM_findCmdParsedSnap(v_doc_682_, v_start_686_);
v___x_688_ = lean_task_get_own(v___x_687_);
if (lean_obj_tag(v___x_688_) == 1)
{
lean_object* v_meta_689_; lean_object* v_val_690_; lean_object* v_text_691_; lean_object* v_elabSnap_692_; lean_object* v_tree_693_; lean_object* v___x_694_; lean_object* v_msgLog_695_; lean_object* v_unreported_696_; lean_object* v___x_697_; lean_object* v_ranges_698_; lean_object* v___x_699_; uint8_t v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___f_709_; uint8_t v___y_711_; lean_object* v___x_716_; uint8_t v___x_717_; 
v_meta_689_ = lean_ctor_get(v_toEditableDocumentCore_685_, 0);
lean_inc_ref(v_meta_689_);
lean_dec_ref(v_toEditableDocumentCore_685_);
v_val_690_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_val_690_);
lean_dec_ref_known(v___x_688_, 1);
v_text_691_ = lean_ctor_get(v_meta_689_, 3);
lean_inc_ref(v_text_691_);
lean_dec_ref(v_meta_689_);
v_elabSnap_692_ = lean_ctor_get(v_val_690_, 3);
lean_inc_ref(v_elabSnap_692_);
lean_dec(v_val_690_);
v_tree_693_ = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(v_elabSnap_692_);
lean_inc_ref(v_requestedRange_683_);
lean_inc_ref(v_tree_693_);
v___x_694_ = l_Lean_Language_SnapshotTree_collectMessagesInRange(v_tree_693_, v_requestedRange_683_);
v_msgLog_695_ = lean_task_get_own(v___x_694_);
v_unreported_696_ = lean_ctor_get(v_msgLog_695_, 1);
lean_inc_ref(v_unreported_696_);
lean_dec(v_msgLog_695_);
v___x_697_ = lean_unsigned_to_nat(0u);
v_ranges_698_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0));
v___x_699_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_691_, v_requestedRange_683_, v_unreported_696_, v_ranges_698_);
lean_dec_ref(v_unreported_696_);
lean_dec_ref(v_text_691_);
v___f_709_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1));
v___x_716_ = lean_array_get_size(v___x_699_);
v___x_717_ = lean_nat_dec_eq(v___x_716_, v___x_697_);
if (v___x_717_ == 0)
{
uint8_t v___x_718_; 
v___x_718_ = 1;
v___y_711_ = v___x_718_;
goto v___jp_710_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = 0;
v___y_711_ = v___x_719_;
goto v___jp_710_;
}
v___jp_700_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_704_ = lean_mk_empty_array_with_capacity(v___y_703_);
lean_dec(v___y_703_);
v___x_705_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_704_, v___y_702_);
v___x_706_ = l_Array_append___redArg(v___x_699_, v___x_705_);
lean_dec_ref(v___x_705_);
v___x_707_ = lean_box(v___y_701_);
v___x_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_708_, 0, v___x_706_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
return v___x_708_;
}
v___jp_710_:
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_712_ = lean_box(1);
v___x_713_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(v_tree_693_, v_requestedRange_683_, v___x_712_, v___f_709_);
v___x_714_ = lean_task_get_own(v___x_713_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_size_715_; 
v_size_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_size_715_);
v___y_701_ = v___y_711_;
v___y_702_ = v___x_714_;
v___y_703_ = v_size_715_;
goto v___jp_700_;
}
else
{
v___y_701_ = v___y_711_;
v___y_702_ = v___x_714_;
v___y_703_ = v___x_697_;
goto v___jp_700_;
}
}
}
else
{
lean_object* v___x_720_; 
lean_dec(v___x_688_);
lean_dec_ref(v_toEditableDocumentCore_685_);
lean_dec_ref(v_requestedRange_683_);
v___x_720_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2));
return v___x_720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___boxed(lean_object* v_doc_721_, lean_object* v_requestedRange_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(v_doc_721_, v_requestedRange_722_);
return v_res_724_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(lean_object* v_00_u03b2_725_, lean_object* v_k_726_, lean_object* v_t_727_){
_start:
{
uint8_t v___x_728_; 
v___x_728_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_k_726_, v_t_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___boxed(lean_object* v_00_u03b2_729_, lean_object* v_k_730_, lean_object* v_t_731_){
_start:
{
uint8_t v_res_732_; lean_object* v_r_733_; 
v_res_732_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(v_00_u03b2_729_, v_k_730_, v_t_731_);
lean_dec(v_t_731_);
lean_dec_ref(v_k_730_);
v_r_733_ = lean_box(v_res_732_);
return v_r_733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3(lean_object* v_00_u03b2_734_, lean_object* v_k_735_, lean_object* v_v_736_, lean_object* v_t_737_, lean_object* v_hl_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_735_, v_v_736_, v_t_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4(lean_object* v_init_740_, lean_object* v_t_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v_init_740_, v_t_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0(lean_object* v_s_745_){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_746_ = ((lean_object*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0));
v___x_747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_747_, 0, v_s_745_);
lean_ctor_set(v___x_747_, 1, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2(lean_object* v___f_749_, lean_object* v_s_750_){
_start:
{
lean_object* v_toSnapshot_751_; lean_object* v_metaSnap_752_; lean_object* v_result_x3f_753_; lean_object* v___y_755_; 
v_toSnapshot_751_ = lean_ctor_get(v_s_750_, 0);
lean_inc_ref(v_toSnapshot_751_);
v_metaSnap_752_ = lean_ctor_get(v_s_750_, 1);
lean_inc_ref(v_metaSnap_752_);
v_result_x3f_753_ = lean_ctor_get(v_s_750_, 2);
lean_inc(v_result_x3f_753_);
lean_dec_ref(v_s_750_);
if (lean_obj_tag(v_result_x3f_753_) == 0)
{
lean_object* v___x_765_; 
v___x_765_ = lean_box(0);
v___y_755_ = v___x_765_;
goto v___jp_754_;
}
else
{
lean_object* v_val_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_779_; 
v_val_766_ = lean_ctor_get(v_result_x3f_753_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_result_x3f_753_);
if (v_isSharedCheck_779_ == 0)
{
v___x_768_ = v_result_x3f_753_;
v_isShared_769_ = v_isSharedCheck_779_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_val_766_);
lean_dec(v_result_x3f_753_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_779_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v_firstCmdSnap_770_; lean_object* v_stx_x3f_771_; lean_object* v_reportingRange_772_; lean_object* v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v_firstCmdSnap_770_ = lean_ctor_get(v_val_766_, 1);
lean_inc_ref(v_firstCmdSnap_770_);
lean_dec(v_val_766_);
v_stx_x3f_771_ = lean_ctor_get(v_firstCmdSnap_770_, 0);
lean_inc(v_stx_x3f_771_);
v_reportingRange_772_ = lean_ctor_get(v_firstCmdSnap_770_, 1);
lean_inc(v_reportingRange_772_);
v___x_773_ = ((lean_object*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0));
v___x_774_ = 1;
v___x_775_ = l_Lean_Language_SnapshotTask_map___redArg(v_firstCmdSnap_770_, v___x_773_, v_stx_x3f_771_, v_reportingRange_772_, v___x_774_);
if (v_isShared_769_ == 0)
{
lean_ctor_set(v___x_768_, 0, v___x_775_);
v___x_777_ = v___x_768_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
v___y_755_ = v___x_777_;
goto v___jp_754_;
}
}
}
v___jp_754_:
{
lean_object* v_stx_x3f_756_; lean_object* v_reportingRange_757_; uint8_t v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v_stx_x3f_756_ = lean_ctor_get(v_metaSnap_752_, 0);
lean_inc(v_stx_x3f_756_);
v_reportingRange_757_ = lean_ctor_get(v_metaSnap_752_, 1);
lean_inc(v_reportingRange_757_);
v___x_758_ = 1;
v___x_759_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_752_, v___f_749_, v_stx_x3f_756_, v_reportingRange_757_, v___x_758_);
v___x_760_ = lean_unsigned_to_nat(1u);
v___x_761_ = lean_mk_empty_array_with_capacity(v___x_760_);
v___x_762_ = lean_array_push(v___x_761_, v___x_759_);
v___x_763_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_755_, v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_toSnapshot_751_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(lean_object* v_as_780_, size_t v_i_781_, size_t v_stop_782_, lean_object* v_b_783_){
_start:
{
uint8_t v___x_784_; 
v___x_784_ = lean_usize_dec_eq(v_i_781_, v_stop_782_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; lean_object* v___x_786_; size_t v___x_787_; size_t v___x_788_; 
v___x_785_ = lean_array_uget_borrowed(v_as_780_, v_i_781_);
lean_inc(v___x_785_);
v___x_786_ = l_Lean_MessageLog_append(v_b_783_, v___x_785_);
v___x_787_ = ((size_t)1ULL);
v___x_788_ = lean_usize_add(v_i_781_, v___x_787_);
v_i_781_ = v___x_788_;
v_b_783_ = v___x_786_;
goto _start;
}
else
{
return v_b_783_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3___boxed(lean_object* v_as_790_, lean_object* v_i_791_, lean_object* v_stop_792_, lean_object* v_b_793_){
_start:
{
size_t v_i_boxed_794_; size_t v_stop_boxed_795_; lean_object* v_res_796_; 
v_i_boxed_794_ = lean_unbox_usize(v_i_791_);
lean_dec(v_i_791_);
v_stop_boxed_795_ = lean_unbox_usize(v_stop_792_);
lean_dec(v_stop_792_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v_as_790_, v_i_boxed_794_, v_stop_boxed_795_, v_b_793_);
lean_dec_ref(v_as_790_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(lean_object* v_as_x27_797_, lean_object* v_b_798_){
_start:
{
if (lean_obj_tag(v_as_x27_797_) == 0)
{
return v_b_798_;
}
else
{
lean_object* v_head_800_; lean_object* v_tail_801_; lean_object* v___f_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___y_807_; 
v_head_800_ = lean_ctor_get(v_as_x27_797_, 0);
v_tail_801_ = lean_ctor_get(v_as_x27_797_, 1);
v___f_802_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1));
v___x_803_ = lean_box(1);
lean_inc(v_head_800_);
v___x_804_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_800_);
v___x_805_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_802_, v___x_803_, v___x_804_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_size_812_; 
v_size_812_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_size_812_);
v___y_807_ = v_size_812_;
goto v___jp_806_;
}
else
{
lean_object* v___x_813_; 
v___x_813_ = lean_unsigned_to_nat(0u);
v___y_807_ = v___x_813_;
goto v___jp_806_;
}
v___jp_806_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_mk_empty_array_with_capacity(v___y_807_);
lean_dec(v___y_807_);
v___x_809_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_808_, v___x_805_);
v___x_810_ = l_Array_append___redArg(v_b_798_, v___x_809_);
lean_dec_ref(v___x_809_);
v_as_x27_797_ = v_tail_801_;
v_b_798_ = v___x_810_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg___boxed(lean_object* v_as_x27_814_, lean_object* v_b_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_814_, v_b_815_);
lean_dec(v_as_x27_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(lean_object* v_as_818_, lean_object* v_as_x27_819_, lean_object* v_b_820_){
_start:
{
if (lean_obj_tag(v_as_x27_819_) == 0)
{
return v_b_820_;
}
else
{
lean_object* v_head_822_; lean_object* v_tail_823_; lean_object* v___f_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___y_829_; 
v_head_822_ = lean_ctor_get(v_as_x27_819_, 0);
v_tail_823_ = lean_ctor_get(v_as_x27_819_, 1);
v___f_824_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1));
v___x_825_ = lean_box(1);
lean_inc(v_head_822_);
v___x_826_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_822_);
v___x_827_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_824_, v___x_825_, v___x_826_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_size_834_; 
v_size_834_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_size_834_);
v___y_829_ = v_size_834_;
goto v___jp_828_;
}
else
{
lean_object* v___x_835_; 
v___x_835_ = lean_unsigned_to_nat(0u);
v___y_829_ = v___x_835_;
goto v___jp_828_;
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; 
v___x_830_ = lean_mk_empty_array_with_capacity(v___y_829_);
lean_dec(v___y_829_);
v___x_831_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_830_, v___x_827_);
v___x_832_ = l_Array_append___redArg(v_b_820_, v___x_831_);
lean_dec_ref(v___x_831_);
v___x_833_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_tail_823_, v___x_832_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg___boxed(lean_object* v_as_836_, lean_object* v_as_x27_837_, lean_object* v_b_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_836_, v_as_x27_837_, v_b_838_);
lean_dec(v_as_x27_837_);
lean_dec(v_as_836_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(lean_object* v_text_841_, lean_object* v_as_842_, size_t v_sz_843_, size_t v_i_844_, lean_object* v_b_845_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_lt(v_i_844_, v_sz_843_);
if (v___x_847_ == 0)
{
return v_b_845_;
}
else
{
lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_874_; 
v_snd_848_ = lean_ctor_get(v_b_845_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_b_845_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v_b_845_, 0);
lean_dec(v_unused_875_);
v___x_850_ = v_b_845_;
v_isShared_851_ = v_isSharedCheck_874_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_dec(v_b_845_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_874_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_a_852_; lean_object* v_pos_853_; lean_object* v_endPos_854_; lean_object* v_data_855_; lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v_a_859_; uint8_t v___x_866_; 
v_a_852_ = lean_array_uget_borrowed(v_as_842_, v_i_844_);
v_pos_853_ = lean_ctor_get(v_a_852_, 1);
v_endPos_854_ = lean_ctor_get(v_a_852_, 2);
v_data_855_ = lean_ctor_get(v_a_852_, 4);
v___f_856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_857_ = lean_box(0);
lean_inc(v_data_855_);
v___x_866_ = l_Lean_MessageData_hasTag(v___f_856_, v_data_855_);
if (v___x_866_ == 0)
{
v_a_859_ = v_snd_848_;
goto v___jp_858_;
}
else
{
lean_object* v___x_867_; lean_object* v___y_869_; 
lean_inc_ref(v_pos_853_);
v___x_867_ = l_Lean_FileMap_ofPosition(v_text_841_, v_pos_853_);
if (lean_obj_tag(v_endPos_854_) == 0)
{
lean_inc_ref(v_pos_853_);
v___y_869_ = v_pos_853_;
goto v___jp_868_;
}
else
{
lean_object* v_val_873_; 
v_val_873_ = lean_ctor_get(v_endPos_854_, 0);
lean_inc(v_val_873_);
v___y_869_ = v_val_873_;
goto v___jp_868_;
}
v___jp_868_:
{
lean_object* v___x_870_; lean_object* v_msgRange_871_; lean_object* v_ranges_872_; 
v___x_870_ = l_Lean_FileMap_ofPosition(v_text_841_, v___y_869_);
v_msgRange_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_871_, 0, v___x_867_);
lean_ctor_set(v_msgRange_871_, 1, v___x_870_);
v_ranges_872_ = lean_array_push(v_snd_848_, v_msgRange_871_);
v_a_859_ = v_ranges_872_;
goto v___jp_858_;
}
}
v___jp_858_:
{
lean_object* v___x_861_; 
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v_a_859_);
lean_ctor_set(v___x_850_, 0, v___x_857_);
v___x_861_ = v___x_850_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_a_859_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
size_t v___x_862_; size_t v___x_863_; 
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_add(v_i_844_, v___x_862_);
v_i_844_ = v___x_863_;
v_b_845_ = v___x_861_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4___boxed(lean_object* v_text_876_, lean_object* v_as_877_, lean_object* v_sz_878_, lean_object* v_i_879_, lean_object* v_b_880_, lean_object* v___y_881_){
_start:
{
size_t v_sz_boxed_882_; size_t v_i_boxed_883_; lean_object* v_res_884_; 
v_sz_boxed_882_ = lean_unbox_usize(v_sz_878_);
lean_dec(v_sz_878_);
v_i_boxed_883_ = lean_unbox_usize(v_i_879_);
lean_dec(v_i_879_);
v_res_884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(v_text_876_, v_as_877_, v_sz_boxed_882_, v_i_boxed_883_, v_b_880_);
lean_dec_ref(v_as_877_);
lean_dec_ref(v_text_876_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(lean_object* v_text_885_, lean_object* v_as_886_, size_t v_sz_887_, size_t v_i_888_, lean_object* v_b_889_){
_start:
{
uint8_t v___x_891_; 
v___x_891_ = lean_usize_dec_lt(v_i_888_, v_sz_887_);
if (v___x_891_ == 0)
{
return v_b_889_;
}
else
{
lean_object* v_snd_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_918_; 
v_snd_892_ = lean_ctor_get(v_b_889_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_b_889_);
if (v_isSharedCheck_918_ == 0)
{
lean_object* v_unused_919_; 
v_unused_919_ = lean_ctor_get(v_b_889_, 0);
lean_dec(v_unused_919_);
v___x_894_ = v_b_889_;
v_isShared_895_ = v_isSharedCheck_918_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_snd_892_);
lean_dec(v_b_889_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_918_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_a_896_; lean_object* v_pos_897_; lean_object* v_endPos_898_; lean_object* v_data_899_; lean_object* v___f_900_; lean_object* v___x_901_; lean_object* v_a_903_; uint8_t v___x_910_; 
v_a_896_ = lean_array_uget_borrowed(v_as_886_, v_i_888_);
v_pos_897_ = lean_ctor_get(v_a_896_, 1);
v_endPos_898_ = lean_ctor_get(v_a_896_, 2);
v_data_899_ = lean_ctor_get(v_a_896_, 4);
v___f_900_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_901_ = lean_box(0);
lean_inc(v_data_899_);
v___x_910_ = l_Lean_MessageData_hasTag(v___f_900_, v_data_899_);
if (v___x_910_ == 0)
{
v_a_903_ = v_snd_892_;
goto v___jp_902_;
}
else
{
lean_object* v___x_911_; lean_object* v___y_913_; 
lean_inc_ref(v_pos_897_);
v___x_911_ = l_Lean_FileMap_ofPosition(v_text_885_, v_pos_897_);
if (lean_obj_tag(v_endPos_898_) == 0)
{
lean_inc_ref(v_pos_897_);
v___y_913_ = v_pos_897_;
goto v___jp_912_;
}
else
{
lean_object* v_val_917_; 
v_val_917_ = lean_ctor_get(v_endPos_898_, 0);
lean_inc(v_val_917_);
v___y_913_ = v_val_917_;
goto v___jp_912_;
}
v___jp_912_:
{
lean_object* v___x_914_; lean_object* v_msgRange_915_; lean_object* v_ranges_916_; 
v___x_914_ = l_Lean_FileMap_ofPosition(v_text_885_, v___y_913_);
v_msgRange_915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_915_, 0, v___x_911_);
lean_ctor_set(v_msgRange_915_, 1, v___x_914_);
v_ranges_916_ = lean_array_push(v_snd_892_, v_msgRange_915_);
v_a_903_ = v_ranges_916_;
goto v___jp_902_;
}
}
v___jp_902_:
{
lean_object* v___x_905_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 1, v_a_903_);
lean_ctor_set(v___x_894_, 0, v___x_901_);
v___x_905_ = v___x_894_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_901_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_a_903_);
v___x_905_ = v_reuseFailAlloc_909_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
size_t v___x_906_; size_t v___x_907_; lean_object* v___x_908_; 
v___x_906_ = ((size_t)1ULL);
v___x_907_ = lean_usize_add(v_i_888_, v___x_906_);
v___x_908_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(v_text_885_, v_as_886_, v_sz_887_, v___x_907_, v___x_905_);
return v___x_908_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1___boxed(lean_object* v_text_920_, lean_object* v_as_921_, lean_object* v_sz_922_, lean_object* v_i_923_, lean_object* v_b_924_, lean_object* v___y_925_){
_start:
{
size_t v_sz_boxed_926_; size_t v_i_boxed_927_; lean_object* v_res_928_; 
v_sz_boxed_926_ = lean_unbox_usize(v_sz_922_);
lean_dec(v_sz_922_);
v_i_boxed_927_ = lean_unbox_usize(v_i_923_);
lean_dec(v_i_923_);
v_res_928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_920_, v_as_921_, v_sz_boxed_926_, v_i_boxed_927_, v_b_924_);
lean_dec_ref(v_as_921_);
lean_dec_ref(v_text_920_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(lean_object* v_text_929_, lean_object* v_as_930_, size_t v_sz_931_, size_t v_i_932_, lean_object* v_b_933_){
_start:
{
uint8_t v___x_935_; 
v___x_935_ = lean_usize_dec_lt(v_i_932_, v_sz_931_);
if (v___x_935_ == 0)
{
return v_b_933_;
}
else
{
lean_object* v_snd_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_962_; 
v_snd_936_ = lean_ctor_get(v_b_933_, 1);
v_isSharedCheck_962_ = !lean_is_exclusive(v_b_933_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_b_933_, 0);
lean_dec(v_unused_963_);
v___x_938_ = v_b_933_;
v_isShared_939_ = v_isSharedCheck_962_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_snd_936_);
lean_dec(v_b_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_962_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v_a_940_; lean_object* v_pos_941_; lean_object* v_endPos_942_; lean_object* v_data_943_; lean_object* v___f_944_; lean_object* v___x_945_; lean_object* v_a_947_; uint8_t v___x_954_; 
v_a_940_ = lean_array_uget_borrowed(v_as_930_, v_i_932_);
v_pos_941_ = lean_ctor_get(v_a_940_, 1);
v_endPos_942_ = lean_ctor_get(v_a_940_, 2);
v_data_943_ = lean_ctor_get(v_a_940_, 4);
v___f_944_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_945_ = lean_box(0);
lean_inc(v_data_943_);
v___x_954_ = l_Lean_MessageData_hasTag(v___f_944_, v_data_943_);
if (v___x_954_ == 0)
{
v_a_947_ = v_snd_936_;
goto v___jp_946_;
}
else
{
lean_object* v___x_955_; lean_object* v___y_957_; 
lean_inc_ref(v_pos_941_);
v___x_955_ = l_Lean_FileMap_ofPosition(v_text_929_, v_pos_941_);
if (lean_obj_tag(v_endPos_942_) == 0)
{
lean_inc_ref(v_pos_941_);
v___y_957_ = v_pos_941_;
goto v___jp_956_;
}
else
{
lean_object* v_val_961_; 
v_val_961_ = lean_ctor_get(v_endPos_942_, 0);
lean_inc(v_val_961_);
v___y_957_ = v_val_961_;
goto v___jp_956_;
}
v___jp_956_:
{
lean_object* v___x_958_; lean_object* v_msgRange_959_; lean_object* v_ranges_960_; 
v___x_958_ = l_Lean_FileMap_ofPosition(v_text_929_, v___y_957_);
v_msgRange_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_959_, 0, v___x_955_);
lean_ctor_set(v_msgRange_959_, 1, v___x_958_);
v_ranges_960_ = lean_array_push(v_snd_936_, v_msgRange_959_);
v_a_947_ = v_ranges_960_;
goto v___jp_946_;
}
}
v___jp_946_:
{
lean_object* v___x_949_; 
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v_a_947_);
lean_ctor_set(v___x_938_, 0, v___x_945_);
v___x_949_ = v___x_938_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_953_, 1, v_a_947_);
v___x_949_ = v_reuseFailAlloc_953_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
size_t v___x_950_; size_t v___x_951_; 
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_add(v_i_932_, v___x_950_);
v_i_932_ = v___x_951_;
v_b_933_ = v___x_949_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_text_964_, lean_object* v_as_965_, lean_object* v_sz_966_, lean_object* v_i_967_, lean_object* v_b_968_, lean_object* v___y_969_){
_start:
{
size_t v_sz_boxed_970_; size_t v_i_boxed_971_; lean_object* v_res_972_; 
v_sz_boxed_970_ = lean_unbox_usize(v_sz_966_);
lean_dec(v_sz_966_);
v_i_boxed_971_ = lean_unbox_usize(v_i_967_);
lean_dec(v_i_967_);
v_res_972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(v_text_964_, v_as_965_, v_sz_boxed_970_, v_i_boxed_971_, v_b_968_);
lean_dec_ref(v_as_965_);
lean_dec_ref(v_text_964_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(lean_object* v_text_973_, lean_object* v_as_974_, size_t v_sz_975_, size_t v_i_976_, lean_object* v_b_977_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_lt(v_i_976_, v_sz_975_);
if (v___x_979_ == 0)
{
return v_b_977_;
}
else
{
lean_object* v_snd_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_1006_; 
v_snd_980_ = lean_ctor_get(v_b_977_, 1);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_b_977_);
if (v_isSharedCheck_1006_ == 0)
{
lean_object* v_unused_1007_; 
v_unused_1007_ = lean_ctor_get(v_b_977_, 0);
lean_dec(v_unused_1007_);
v___x_982_ = v_b_977_;
v_isShared_983_ = v_isSharedCheck_1006_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_snd_980_);
lean_dec(v_b_977_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_1006_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v_a_984_; lean_object* v_pos_985_; lean_object* v_endPos_986_; lean_object* v_data_987_; lean_object* v___f_988_; lean_object* v___x_989_; lean_object* v_a_991_; uint8_t v___x_998_; 
v_a_984_ = lean_array_uget_borrowed(v_as_974_, v_i_976_);
v_pos_985_ = lean_ctor_get(v_a_984_, 1);
v_endPos_986_ = lean_ctor_get(v_a_984_, 2);
v_data_987_ = lean_ctor_get(v_a_984_, 4);
v___f_988_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_989_ = lean_box(0);
lean_inc(v_data_987_);
v___x_998_ = l_Lean_MessageData_hasTag(v___f_988_, v_data_987_);
if (v___x_998_ == 0)
{
v_a_991_ = v_snd_980_;
goto v___jp_990_;
}
else
{
lean_object* v___x_999_; lean_object* v___y_1001_; 
lean_inc_ref(v_pos_985_);
v___x_999_ = l_Lean_FileMap_ofPosition(v_text_973_, v_pos_985_);
if (lean_obj_tag(v_endPos_986_) == 0)
{
lean_inc_ref(v_pos_985_);
v___y_1001_ = v_pos_985_;
goto v___jp_1000_;
}
else
{
lean_object* v_val_1005_; 
v_val_1005_ = lean_ctor_get(v_endPos_986_, 0);
lean_inc(v_val_1005_);
v___y_1001_ = v_val_1005_;
goto v___jp_1000_;
}
v___jp_1000_:
{
lean_object* v___x_1002_; lean_object* v_msgRange_1003_; lean_object* v_ranges_1004_; 
v___x_1002_ = l_Lean_FileMap_ofPosition(v_text_973_, v___y_1001_);
v_msgRange_1003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_1003_, 0, v___x_999_);
lean_ctor_set(v_msgRange_1003_, 1, v___x_1002_);
v_ranges_1004_ = lean_array_push(v_snd_980_, v_msgRange_1003_);
v_a_991_ = v_ranges_1004_;
goto v___jp_990_;
}
}
v___jp_990_:
{
lean_object* v___x_993_; 
if (v_isShared_983_ == 0)
{
lean_ctor_set(v___x_982_, 1, v_a_991_);
lean_ctor_set(v___x_982_, 0, v___x_989_);
v___x_993_ = v___x_982_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_a_991_);
v___x_993_ = v_reuseFailAlloc_997_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_add(v_i_976_, v___x_994_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(v_text_973_, v_as_974_, v_sz_975_, v___x_995_, v___x_993_);
return v___x_996_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2___boxed(lean_object* v_text_1008_, lean_object* v_as_1009_, lean_object* v_sz_1010_, lean_object* v_i_1011_, lean_object* v_b_1012_, lean_object* v___y_1013_){
_start:
{
size_t v_sz_boxed_1014_; size_t v_i_boxed_1015_; lean_object* v_res_1016_; 
v_sz_boxed_1014_ = lean_unbox_usize(v_sz_1010_);
lean_dec(v_sz_1010_);
v_i_boxed_1015_ = lean_unbox_usize(v_i_1011_);
lean_dec(v_i_1011_);
v_res_1016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_1008_, v_as_1009_, v_sz_boxed_1014_, v_i_boxed_1015_, v_b_1012_);
lean_dec_ref(v_as_1009_);
lean_dec_ref(v_text_1008_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(lean_object* v_init_1017_, lean_object* v_text_1018_, lean_object* v_n_1019_, lean_object* v_b_1020_){
_start:
{
if (lean_obj_tag(v_n_1019_) == 0)
{
lean_object* v_cs_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; size_t v_sz_1025_; size_t v___x_1026_; lean_object* v___x_1027_; lean_object* v_fst_1028_; 
v_cs_1022_ = lean_ctor_get(v_n_1019_, 0);
v___x_1023_ = lean_box(0);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_b_1020_);
v_sz_1025_ = lean_array_size(v_cs_1022_);
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_1017_, v_text_1018_, v_cs_1022_, v_sz_1025_, v___x_1026_, v___x_1024_);
v_fst_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_fst_1028_);
if (lean_obj_tag(v_fst_1028_) == 0)
{
lean_object* v_snd_1029_; lean_object* v___x_1030_; 
v_snd_1029_ = lean_ctor_get(v___x_1027_, 1);
lean_inc(v_snd_1029_);
lean_dec_ref(v___x_1027_);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v_snd_1029_);
return v___x_1030_;
}
else
{
lean_object* v_val_1031_; 
lean_dec_ref(v___x_1027_);
v_val_1031_ = lean_ctor_get(v_fst_1028_, 0);
lean_inc(v_val_1031_);
lean_dec_ref_known(v_fst_1028_, 1);
return v_val_1031_;
}
}
else
{
lean_object* v_vs_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; size_t v_sz_1035_; size_t v___x_1036_; lean_object* v___x_1037_; lean_object* v_fst_1038_; 
v_vs_1032_ = lean_ctor_get(v_n_1019_, 0);
v___x_1033_ = lean_box(0);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1033_);
lean_ctor_set(v___x_1034_, 1, v_b_1020_);
v_sz_1035_ = lean_array_size(v_vs_1032_);
v___x_1036_ = ((size_t)0ULL);
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_1018_, v_vs_1032_, v_sz_1035_, v___x_1036_, v___x_1034_);
v_fst_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_fst_1038_);
if (lean_obj_tag(v_fst_1038_) == 0)
{
lean_object* v_snd_1039_; lean_object* v___x_1040_; 
v_snd_1039_ = lean_ctor_get(v___x_1037_, 1);
lean_inc(v_snd_1039_);
lean_dec_ref(v___x_1037_);
v___x_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1040_, 0, v_snd_1039_);
return v___x_1040_;
}
else
{
lean_object* v_val_1041_; 
lean_dec_ref(v___x_1037_);
v_val_1041_ = lean_ctor_get(v_fst_1038_, 0);
lean_inc(v_val_1041_);
lean_dec_ref_known(v_fst_1038_, 1);
return v_val_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(lean_object* v_init_1042_, lean_object* v_text_1043_, lean_object* v_as_1044_, size_t v_sz_1045_, size_t v_i_1046_, lean_object* v_b_1047_){
_start:
{
uint8_t v___x_1049_; 
v___x_1049_ = lean_usize_dec_lt(v_i_1046_, v_sz_1045_);
if (v___x_1049_ == 0)
{
return v_b_1047_;
}
else
{
lean_object* v_snd_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1068_; 
v_snd_1050_ = lean_ctor_get(v_b_1047_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_b_1047_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_b_1047_, 0);
lean_dec(v_unused_1069_);
v___x_1052_ = v_b_1047_;
v_isShared_1053_ = v_isSharedCheck_1068_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_snd_1050_);
lean_dec(v_b_1047_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1068_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v_a_1054_; lean_object* v___x_1055_; 
v_a_1054_ = lean_array_uget_borrowed(v_as_1044_, v_i_1046_);
lean_inc(v_snd_1050_);
v___x_1055_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_1042_, v_text_1043_, v_a_1054_, v_snd_1050_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1055_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v___x_1056_);
v___x_1058_ = v___x_1052_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_snd_1050_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1061_; lean_object* v___x_1063_; 
lean_dec(v_snd_1050_);
v_a_1060_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1060_);
lean_dec_ref_known(v___x_1055_, 1);
v___x_1061_ = lean_box(0);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v_a_1060_);
lean_ctor_set(v___x_1052_, 0, v___x_1061_);
v___x_1063_ = v___x_1052_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v___x_1061_);
lean_ctor_set(v_reuseFailAlloc_1067_, 1, v_a_1060_);
v___x_1063_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
size_t v___x_1064_; size_t v___x_1065_; 
v___x_1064_ = ((size_t)1ULL);
v___x_1065_ = lean_usize_add(v_i_1046_, v___x_1064_);
v_i_1046_ = v___x_1065_;
v_b_1047_ = v___x_1063_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1070_, lean_object* v_text_1071_, lean_object* v_as_1072_, lean_object* v_sz_1073_, lean_object* v_i_1074_, lean_object* v_b_1075_, lean_object* v___y_1076_){
_start:
{
size_t v_sz_boxed_1077_; size_t v_i_boxed_1078_; lean_object* v_res_1079_; 
v_sz_boxed_1077_ = lean_unbox_usize(v_sz_1073_);
lean_dec(v_sz_1073_);
v_i_boxed_1078_ = lean_unbox_usize(v_i_1074_);
lean_dec(v_i_1074_);
v_res_1079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_1070_, v_text_1071_, v_as_1072_, v_sz_boxed_1077_, v_i_boxed_1078_, v_b_1075_);
lean_dec_ref(v_as_1072_);
lean_dec_ref(v_text_1071_);
lean_dec_ref(v_init_1070_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0___boxed(lean_object* v_init_1080_, lean_object* v_text_1081_, lean_object* v_n_1082_, lean_object* v_b_1083_, lean_object* v___y_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_1080_, v_text_1081_, v_n_1082_, v_b_1083_);
lean_dec_ref(v_n_1082_);
lean_dec_ref(v_text_1081_);
lean_dec_ref(v_init_1080_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(lean_object* v_text_1086_, lean_object* v_t_1087_, lean_object* v_init_1088_){
_start:
{
lean_object* v_root_1090_; lean_object* v_tail_1091_; lean_object* v___x_1092_; 
v_root_1090_ = lean_ctor_get(v_t_1087_, 0);
v_tail_1091_ = lean_ctor_get(v_t_1087_, 1);
lean_inc_ref(v_init_1088_);
v___x_1092_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_1088_, v_text_1086_, v_root_1090_, v_init_1088_);
lean_dec_ref(v_init_1088_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref_known(v___x_1092_, 1);
return v_a_1093_;
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; size_t v_sz_1097_; size_t v___x_1098_; lean_object* v___x_1099_; lean_object* v_fst_1100_; 
v_a_1094_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1094_);
lean_dec_ref_known(v___x_1092_, 1);
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_a_1094_);
v_sz_1097_ = lean_array_size(v_tail_1091_);
v___x_1098_ = ((size_t)0ULL);
v___x_1099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_1086_, v_tail_1091_, v_sz_1097_, v___x_1098_, v___x_1096_);
v_fst_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_fst_1100_);
if (lean_obj_tag(v_fst_1100_) == 0)
{
lean_object* v_snd_1101_; 
v_snd_1101_ = lean_ctor_get(v___x_1099_, 1);
lean_inc(v_snd_1101_);
lean_dec_ref(v___x_1099_);
return v_snd_1101_;
}
else
{
lean_object* v_val_1102_; 
lean_dec_ref(v___x_1099_);
v_val_1102_ = lean_ctor_get(v_fst_1100_, 0);
lean_inc(v_val_1102_);
lean_dec_ref_known(v_fst_1100_, 1);
return v_val_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0___boxed(lean_object* v_text_1103_, lean_object* v_t_1104_, lean_object* v_init_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_1103_, v_t_1104_, v_init_1105_);
lean_dec_ref(v_t_1104_);
lean_dec_ref(v_text_1103_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(size_t v_sz_1108_, size_t v_i_1109_, lean_object* v_bs_1110_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_usize_dec_lt(v_i_1109_, v_sz_1108_);
if (v___x_1111_ == 0)
{
return v_bs_1110_;
}
else
{
lean_object* v_v_1112_; lean_object* v_diagnostics_1113_; lean_object* v_msgLog_1114_; lean_object* v___x_1115_; lean_object* v_bs_x27_1116_; size_t v___x_1117_; size_t v___x_1118_; lean_object* v___x_1119_; 
v_v_1112_ = lean_array_uget_borrowed(v_bs_1110_, v_i_1109_);
v_diagnostics_1113_ = lean_ctor_get(v_v_1112_, 1);
v_msgLog_1114_ = lean_ctor_get(v_diagnostics_1113_, 0);
lean_inc_ref(v_msgLog_1114_);
v___x_1115_ = lean_unsigned_to_nat(0u);
v_bs_x27_1116_ = lean_array_uset(v_bs_1110_, v_i_1109_, v___x_1115_);
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_add(v_i_1109_, v___x_1117_);
v___x_1119_ = lean_array_uset(v_bs_x27_1116_, v_i_1109_, v_msgLog_1114_);
v_i_1109_ = v___x_1118_;
v_bs_1110_ = v___x_1119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2___boxed(lean_object* v_sz_1121_, lean_object* v_i_1122_, lean_object* v_bs_1123_){
_start:
{
size_t v_sz_boxed_1124_; size_t v_i_boxed_1125_; lean_object* v_res_1126_; 
v_sz_boxed_1124_ = lean_unbox_usize(v_sz_1121_);
lean_dec(v_sz_1121_);
v_i_boxed_1125_ = lean_unbox_usize(v_i_1122_);
lean_dec(v_i_1122_);
v_res_1126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_boxed_1124_, v_i_boxed_1125_, v_bs_1123_);
return v_res_1126_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1(void){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1128_ = lean_unsigned_to_nat(32u);
v___x_1129_ = lean_mk_empty_array_with_capacity(v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
return v___x_1130_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2(void){
_start:
{
size_t v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1131_ = ((size_t)5ULL);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_unsigned_to_nat(32u);
v___x_1134_ = lean_mk_empty_array_with_capacity(v___x_1133_);
v___x_1135_ = lean_obj_once(&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1, &l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1_once, _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1);
v___x_1136_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v___x_1134_);
lean_ctor_set(v___x_1136_, 2, v___x_1132_);
lean_ctor_set(v___x_1136_, 3, v___x_1132_);
lean_ctor_set_usize(v___x_1136_, 4, v___x_1131_);
return v___x_1136_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3(void){
_start:
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1137_ = l_Lean_NameSet_empty;
v___x_1138_ = lean_obj_once(&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2, &l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once, _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2);
v___x_1139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
lean_ctor_set(v___x_1139_, 2, v___x_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(lean_object* v_doc_1142_){
_start:
{
lean_object* v_toEditableDocumentCore_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1209_; 
v_toEditableDocumentCore_1144_ = lean_ctor_get(v_doc_1142_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_doc_1142_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_doc_1142_, 1);
lean_dec(v_unused_1210_);
v___x_1146_ = v_doc_1142_;
v_isShared_1147_ = v_isSharedCheck_1209_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_toEditableDocumentCore_1144_);
lean_dec(v_doc_1142_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1209_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_meta_1148_; lean_object* v_initSnap_1149_; lean_object* v_cmdSnaps_1150_; lean_object* v_text_1151_; lean_object* v_unreported_1153_; lean_object* v___y_1161_; lean_object* v_toSnapshot_1163_; lean_object* v_metaSnap_1164_; lean_object* v_result_x3f_1165_; lean_object* v___f_1166_; lean_object* v___y_1168_; 
v_meta_1148_ = lean_ctor_get(v_toEditableDocumentCore_1144_, 0);
lean_inc_ref(v_meta_1148_);
v_initSnap_1149_ = lean_ctor_get(v_toEditableDocumentCore_1144_, 1);
lean_inc_ref(v_initSnap_1149_);
v_cmdSnaps_1150_ = lean_ctor_get(v_toEditableDocumentCore_1144_, 2);
lean_inc(v_cmdSnaps_1150_);
lean_dec_ref(v_toEditableDocumentCore_1144_);
v_text_1151_ = lean_ctor_get(v_meta_1148_, 3);
lean_inc_ref(v_text_1151_);
lean_dec_ref(v_meta_1148_);
v_toSnapshot_1163_ = lean_ctor_get(v_initSnap_1149_, 0);
lean_inc_ref(v_toSnapshot_1163_);
v_metaSnap_1164_ = lean_ctor_get(v_initSnap_1149_, 1);
lean_inc_ref(v_metaSnap_1164_);
v_result_x3f_1165_ = lean_ctor_get(v_initSnap_1149_, 4);
lean_inc(v_result_x3f_1165_);
lean_dec_ref(v_initSnap_1149_);
v___f_1166_ = ((lean_object*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0));
if (lean_obj_tag(v_result_x3f_1165_) == 0)
{
lean_object* v___x_1194_; 
v___x_1194_ = lean_box(0);
v___y_1168_ = v___x_1194_;
goto v___jp_1167_;
}
else
{
lean_object* v_val_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1208_; 
v_val_1195_ = lean_ctor_get(v_result_x3f_1165_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_result_x3f_1165_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1197_ = v_result_x3f_1165_;
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_val_1195_);
lean_dec(v_result_x3f_1165_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1208_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_processedSnap_1199_; lean_object* v_stx_x3f_1200_; lean_object* v_reportingRange_1201_; lean_object* v___f_1202_; uint8_t v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
v_processedSnap_1199_ = lean_ctor_get(v_val_1195_, 1);
lean_inc_ref(v_processedSnap_1199_);
lean_dec(v_val_1195_);
v_stx_x3f_1200_ = lean_ctor_get(v_processedSnap_1199_, 0);
lean_inc(v_stx_x3f_1200_);
v_reportingRange_1201_ = lean_ctor_get(v_processedSnap_1199_, 1);
lean_inc(v_reportingRange_1201_);
v___f_1202_ = ((lean_object*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4));
v___x_1203_ = 1;
v___x_1204_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_1199_, v___f_1202_, v_stx_x3f_1200_, v_reportingRange_1201_, v___x_1203_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1204_);
v___x_1206_ = v___x_1197_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
v___y_1168_ = v___x_1206_;
goto v___jp_1167_;
}
}
}
v___jp_1152_:
{
lean_object* v_ranges_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v_fst_1158_; lean_object* v___x_1159_; 
v_ranges_1154_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0));
v___x_1155_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_1151_, v_unreported_1153_, v_ranges_1154_);
lean_dec_ref(v_unreported_1153_);
lean_dec_ref(v_text_1151_);
v___x_1156_ = l_IO_AsyncList_waitAll___redArg(v_cmdSnaps_1150_);
v___x_1157_ = lean_task_get_own(v___x_1156_);
v_fst_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_fst_1158_);
lean_dec(v___x_1157_);
v___x_1159_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_fst_1158_, v_fst_1158_, v___x_1155_);
lean_dec(v_fst_1158_);
return v___x_1159_;
}
v___jp_1160_:
{
lean_object* v_unreported_1162_; 
v_unreported_1162_ = lean_ctor_get(v___y_1161_, 1);
lean_inc_ref(v_unreported_1162_);
lean_dec_ref(v___y_1161_);
v_unreported_1153_ = v_unreported_1162_;
goto v___jp_1152_;
}
v___jp_1167_:
{
lean_object* v_stx_x3f_1169_; lean_object* v_reportingRange_1170_; uint8_t v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
v_stx_x3f_1169_ = lean_ctor_get(v_metaSnap_1164_, 0);
lean_inc(v_stx_x3f_1169_);
v_reportingRange_1170_ = lean_ctor_get(v_metaSnap_1164_, 1);
lean_inc(v_reportingRange_1170_);
v___x_1171_ = 1;
v___x_1172_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_1164_, v___f_1166_, v_stx_x3f_1169_, v_reportingRange_1170_, v___x_1171_);
v___x_1173_ = lean_unsigned_to_nat(1u);
v___x_1174_ = lean_mk_empty_array_with_capacity(v___x_1173_);
v___x_1175_ = lean_array_push(v___x_1174_, v___x_1172_);
v___x_1176_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_1168_, v___x_1175_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v___x_1176_);
lean_ctor_set(v___x_1146_, 0, v_toSnapshot_1163_);
v___x_1178_ = v___x_1146_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_toSnapshot_1163_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v_snaps_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; size_t v_sz_1183_; size_t v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; 
v_snaps_1179_ = l_Lean_Language_SnapshotTree_getAll(v___x_1178_);
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = lean_obj_once(&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2, &l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once, _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2);
v___x_1182_ = lean_obj_once(&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3, &l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3_once, _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3);
v_sz_1183_ = lean_array_size(v_snaps_1179_);
v___x_1184_ = ((size_t)0ULL);
v___x_1185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_1183_, v___x_1184_, v_snaps_1179_);
v___x_1186_ = lean_array_get_size(v___x_1185_);
v___x_1187_ = lean_nat_dec_lt(v___x_1180_, v___x_1186_);
if (v___x_1187_ == 0)
{
lean_dec_ref(v___x_1185_);
v_unreported_1153_ = v___x_1181_;
goto v___jp_1152_;
}
else
{
uint8_t v___x_1188_; 
v___x_1188_ = lean_nat_dec_le(v___x_1186_, v___x_1186_);
if (v___x_1188_ == 0)
{
if (v___x_1187_ == 0)
{
lean_dec_ref(v___x_1185_);
v_unreported_1153_ = v___x_1181_;
goto v___jp_1152_;
}
else
{
size_t v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_usize_of_nat(v___x_1186_);
v___x_1190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_1185_, v___x_1184_, v___x_1189_, v___x_1182_);
lean_dec_ref(v___x_1185_);
v___y_1161_ = v___x_1190_;
goto v___jp_1160_;
}
}
else
{
size_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1191_ = lean_usize_of_nat(v___x_1186_);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_1185_, v___x_1184_, v___x_1191_, v___x_1182_);
lean_dec_ref(v___x_1185_);
v___y_1161_ = v___x_1192_;
goto v___jp_1160_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___boxed(lean_object* v_doc_1211_, lean_object* v_a_1212_){
_start:
{
lean_object* v_res_1213_; 
v_res_1213_ = l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(v_doc_1211_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(lean_object* v_as_1214_, lean_object* v_as_x27_1215_, lean_object* v_b_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_1214_, v_as_x27_1215_, v_b_1216_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___boxed(lean_object* v_as_1220_, lean_object* v_as_x27_1221_, lean_object* v_b_1222_, lean_object* v_a_1223_, lean_object* v___y_1224_){
_start:
{
lean_object* v_res_1225_; 
v_res_1225_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(v_as_1220_, v_as_x27_1221_, v_b_1222_, v_a_1223_);
lean_dec(v_as_x27_1221_);
lean_dec(v_as_1220_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(lean_object* v_as_1226_, lean_object* v_as_x27_1227_, lean_object* v_b_1228_, lean_object* v_a_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_1227_, v_b_1228_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___boxed(lean_object* v_as_1232_, lean_object* v_as_x27_1233_, lean_object* v_b_1234_, lean_object* v_a_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(v_as_1232_, v_as_x27_1233_, v_b_1234_, v_a_1235_);
lean_dec(v_as_x27_1233_);
lean_dec(v_as_1232_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(lean_object* v_a_1240_){
_start:
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1258_; 
v_fst_1241_ = lean_ctor_get(v_a_1240_, 0);
v_snd_1242_ = lean_ctor_get(v_a_1240_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_a_1240_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1244_ = v_a_1240_;
v_isShared_1245_ = v_isSharedCheck_1258_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_a_1240_);
v___x_1244_ = lean_box(0);
v_isShared_1245_ = v_isSharedCheck_1258_;
goto v_resetjp_1243_;
}
v_resetjp_1243_:
{
uint8_t v___x_1246_; 
v___x_1246_ = l_Lean_Name_isAnonymous(v_snd_1242_);
if (v___x_1246_ == 0)
{
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1252_; 
v___x_1247_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0));
lean_inc(v_snd_1242_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_snd_1242_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v___x_1249_ = lean_array_push(v_fst_1241_, v___x_1248_);
v___x_1250_ = l_Lean_Name_getPrefix(v_snd_1242_);
lean_dec(v_snd_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v___x_1250_);
lean_ctor_set(v___x_1244_, 0, v___x_1249_);
v___x_1252_ = v___x_1244_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v___x_1249_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1250_);
v___x_1252_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
v_a_1240_ = v___x_1252_;
goto _start;
}
}
else
{
lean_object* v___x_1256_; 
if (v_isShared_1245_ == 0)
{
v___x_1256_ = v___x_1244_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_fst_1241_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v_snd_1242_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
if (lean_obj_tag(v_a_1259_) == 0)
{
lean_object* v___x_1261_; 
v___x_1261_ = l_List_reverse___redArg(v_a_1260_);
return v___x_1261_;
}
else
{
lean_object* v_head_1262_; lean_object* v_tail_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1292_; 
v_head_1262_ = lean_ctor_get(v_a_1259_, 0);
v_tail_1263_ = lean_ctor_get(v_a_1259_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_a_1259_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1265_ = v_a_1259_;
v_isShared_1266_ = v_isSharedCheck_1292_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_tail_1263_);
lean_inc(v_head_1262_);
lean_dec(v_a_1259_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1292_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___y_1268_; 
if (lean_obj_tag(v_head_1262_) == 0)
{
lean_object* v_ns_1273_; lean_object* v_except_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1282_; 
v_ns_1273_ = lean_ctor_get(v_head_1262_, 0);
v_except_1274_ = lean_ctor_get(v_head_1262_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_head_1262_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1276_ = v_head_1262_;
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_except_1274_);
lean_inc(v_ns_1273_);
lean_dec(v_head_1262_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1282_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; lean_object* v___x_1280_; 
v___x_1278_ = lean_array_mk(v_except_1274_);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 1, v___x_1278_);
v___x_1280_ = v___x_1276_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_ns_1273_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v___x_1278_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
v___y_1268_ = v___x_1280_;
goto v___jp_1267_;
}
}
}
else
{
lean_object* v_id_1283_; lean_object* v_declName_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
v_id_1283_ = lean_ctor_get(v_head_1262_, 0);
v_declName_1284_ = lean_ctor_get(v_head_1262_, 1);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_head_1262_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v_head_1262_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_declName_1284_);
lean_inc(v_id_1283_);
lean_dec(v_head_1262_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 1, v_id_1283_);
lean_ctor_set(v___x_1286_, 0, v_declName_1284_);
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_declName_1284_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v_id_1283_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
v___y_1268_ = v___x_1289_;
goto v___jp_1267_;
}
}
}
v___jp_1267_:
{
lean_object* v___x_1270_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 1, v_a_1260_);
lean_ctor_set(v___x_1265_, 0, v___y_1268_);
v___x_1270_ = v___x_1265_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v___y_1268_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_a_1260_);
v___x_1270_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
v_a_1259_ = v_tail_1263_;
v_a_1260_ = v___x_1270_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object* v_currentNamespace_1295_, lean_object* v_openDecls_1296_){
_start:
{
lean_object* v_openNamespaces_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v_fst_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v_openNamespaces_1297_ = ((lean_object*)(l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0));
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_openNamespaces_1297_);
lean_ctor_set(v___x_1298_, 1, v_currentNamespace_1295_);
v___x_1299_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(v___x_1298_);
v_fst_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_fst_1300_);
lean_dec_ref(v___x_1299_);
v___x_1301_ = lean_box(0);
v___x_1302_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(v_openDecls_1296_, v___x_1301_);
v___x_1303_ = lean_array_mk(v___x_1302_);
v___x_1304_ = l_Array_append___redArg(v_fst_1300_, v___x_1303_);
lean_dec_ref(v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(lean_object* v_inst_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v___x_1307_; 
v___x_1307_ = l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg(v_a_1306_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(lean_object* v_doc_1308_, lean_object* v_currNamespace_1309_, lean_object* v_openDecls_1310_, lean_object* v_val_1311_, lean_object* v_val_1312_, uint8_t v___x_1313_, lean_object* v_decl_1314_){
_start:
{
lean_object* v_toEditableDocumentCore_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1339_; 
v_toEditableDocumentCore_1315_ = lean_ctor_get(v_doc_1308_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v_doc_1308_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; 
v_unused_1340_ = lean_ctor_get(v_doc_1308_, 1);
lean_dec(v_unused_1340_);
v___x_1317_ = v_doc_1308_;
v_isShared_1318_ = v_isSharedCheck_1339_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_toEditableDocumentCore_1315_);
lean_dec(v_doc_1308_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1339_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v_meta_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1335_; 
v_meta_1319_ = lean_ctor_get(v_toEditableDocumentCore_1315_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v_toEditableDocumentCore_1315_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; lean_object* v_unused_1337_; lean_object* v_unused_1338_; 
v_unused_1336_ = lean_ctor_get(v_toEditableDocumentCore_1315_, 3);
lean_dec(v_unused_1336_);
v_unused_1337_ = lean_ctor_get(v_toEditableDocumentCore_1315_, 2);
lean_dec(v_unused_1337_);
v_unused_1338_ = lean_ctor_get(v_toEditableDocumentCore_1315_, 1);
lean_dec(v_unused_1338_);
v___x_1321_ = v_toEditableDocumentCore_1315_;
v_isShared_1322_ = v_isSharedCheck_1335_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_meta_1319_);
lean_dec(v_toEditableDocumentCore_1315_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1335_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v_text_1323_; lean_object* v_minimizedId_1324_; lean_object* v___x_1326_; 
v_text_1323_ = lean_ctor_get(v_meta_1319_, 3);
lean_inc_ref(v_text_1323_);
lean_dec_ref(v_meta_1319_);
v_minimizedId_1324_ = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(v_currNamespace_1309_, v_openDecls_1310_, v_decl_1314_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v_val_1312_);
lean_ctor_set(v___x_1317_, 0, v_val_1311_);
v___x_1326_ = v___x_1317_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_val_1311_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_val_1312_);
v___x_1326_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1327_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1323_, v___x_1326_);
lean_inc(v_minimizedId_1324_);
v___x_1328_ = l_Lean_Name_toString(v_minimizedId_1324_, v___x_1313_);
v___x_1329_ = lean_box(0);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 3, v___x_1329_);
lean_ctor_set(v___x_1321_, 2, v___x_1329_);
lean_ctor_set(v___x_1321_, 1, v___x_1328_);
lean_ctor_set(v___x_1321_, 0, v___x_1327_);
v___x_1331_ = v___x_1321_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1333_, 2, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1333_, 3, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1332_; 
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v_minimizedId_1324_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
return v___x_1332_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed(lean_object* v_doc_1341_, lean_object* v_currNamespace_1342_, lean_object* v_openDecls_1343_, lean_object* v_val_1344_, lean_object* v_val_1345_, lean_object* v___x_1346_, lean_object* v_decl_1347_){
_start:
{
uint8_t v___x_172__boxed_1348_; lean_object* v_res_1349_; 
v___x_172__boxed_1348_ = lean_unbox(v___x_1346_);
v_res_1349_ = l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(v_doc_1341_, v_currNamespace_1342_, v_openDecls_1343_, v_val_1344_, v_val_1345_, v___x_172__boxed_1348_, v_decl_1347_);
lean_dec(v_openDecls_1343_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object* v_doc_1350_, lean_object* v_ctx_1351_, lean_object* v_stx_1352_, lean_object* v_id_1353_){
_start:
{
uint8_t v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = 1;
v___x_1355_ = l_Lean_Syntax_getPos_x3f(v_stx_1352_, v___x_1354_);
if (lean_obj_tag(v___x_1355_) == 1)
{
lean_object* v_val_1356_; lean_object* v___x_1357_; 
v_val_1356_ = lean_ctor_get(v___x_1355_, 0);
lean_inc(v_val_1356_);
lean_dec_ref_known(v___x_1355_, 1);
v___x_1357_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1352_, v___x_1354_);
if (lean_obj_tag(v___x_1357_) == 1)
{
lean_object* v_toCommandContextInfo_1358_; lean_object* v_val_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1374_; 
v_toCommandContextInfo_1358_ = lean_ctor_get(v_ctx_1351_, 0);
v_val_1359_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1361_ = v___x_1357_;
v_isShared_1362_ = v_isSharedCheck_1374_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_val_1359_);
lean_dec(v___x_1357_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1374_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v_currNamespace_1363_; lean_object* v_openDecls_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___f_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1372_; 
v_currNamespace_1363_ = lean_ctor_get(v_toCommandContextInfo_1358_, 5);
v_openDecls_1364_ = lean_ctor_get(v_toCommandContextInfo_1358_, 6);
v___x_1365_ = l_Lean_Name_toString(v_id_1353_, v___x_1354_);
v___x_1366_ = lean_box(v___x_1354_);
lean_inc_n(v_openDecls_1364_, 2);
lean_inc_n(v_currNamespace_1363_, 2);
v___f_1367_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1367_, 0, v_doc_1350_);
lean_closure_set(v___f_1367_, 1, v_currNamespace_1363_);
lean_closure_set(v___f_1367_, 2, v_openDecls_1364_);
lean_closure_set(v___f_1367_, 3, v_val_1356_);
lean_closure_set(v___f_1367_, 4, v_val_1359_);
lean_closure_set(v___f_1367_, 5, v___x_1366_);
v___x_1368_ = l_Lean_Server_FileWorker_collectOpenNamespaces(v_currNamespace_1363_, v_openDecls_1364_);
v___x_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1365_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1369_);
lean_ctor_set(v___x_1370_, 1, v_ctx_1351_);
lean_ctor_set(v___x_1370_, 2, v___f_1367_);
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1370_);
v___x_1372_ = v___x_1361_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
else
{
lean_object* v___x_1375_; 
lean_dec(v___x_1357_);
lean_dec(v_val_1356_);
lean_dec(v_id_1353_);
lean_dec_ref(v_ctx_1351_);
lean_dec_ref(v_doc_1350_);
v___x_1375_ = lean_box(0);
return v___x_1375_;
}
}
else
{
lean_object* v___x_1376_; 
lean_dec(v___x_1355_);
lean_dec(v_id_1353_);
lean_dec_ref(v_ctx_1351_);
lean_dec_ref(v_doc_1350_);
v___x_1376_ = lean_box(0);
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object* v_doc_1377_, lean_object* v_ctx_1378_, lean_object* v_stx_1379_, lean_object* v_id_1380_){
_start:
{
lean_object* v_res_1381_; 
v_res_1381_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(v_doc_1377_, v_ctx_1378_, v_stx_1379_, v_id_1380_);
lean_dec(v_stx_1379_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(lean_object* v_e_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v___x_1385_; 
v___x_1385_ = l_Lean_Expr_hasMVar(v_e_1382_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
v___x_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1386_, 0, v_e_1382_);
return v___x_1386_;
}
else
{
lean_object* v___x_1387_; lean_object* v_mctx_1388_; lean_object* v___x_1389_; lean_object* v_fst_1390_; lean_object* v_snd_1391_; lean_object* v___x_1392_; lean_object* v_cache_1393_; lean_object* v_zetaDeltaFVarIds_1394_; lean_object* v_postponed_1395_; lean_object* v_diag_1396_; lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1405_; 
v___x_1387_ = lean_st_ref_get(v___y_1383_);
v_mctx_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc_ref(v_mctx_1388_);
lean_dec(v___x_1387_);
v___x_1389_ = l_Lean_instantiateMVarsCore(v_mctx_1388_, v_e_1382_);
v_fst_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_fst_1390_);
v_snd_1391_ = lean_ctor_get(v___x_1389_, 1);
lean_inc(v_snd_1391_);
lean_dec_ref(v___x_1389_);
v___x_1392_ = lean_st_ref_take(v___y_1383_);
v_cache_1393_ = lean_ctor_get(v___x_1392_, 1);
v_zetaDeltaFVarIds_1394_ = lean_ctor_get(v___x_1392_, 2);
v_postponed_1395_ = lean_ctor_get(v___x_1392_, 3);
v_diag_1396_ = lean_ctor_get(v___x_1392_, 4);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v___x_1392_, 0);
lean_dec(v_unused_1406_);
v___x_1398_ = v___x_1392_;
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
else
{
lean_inc(v_diag_1396_);
lean_inc(v_postponed_1395_);
lean_inc(v_zetaDeltaFVarIds_1394_);
lean_inc(v_cache_1393_);
lean_dec(v___x_1392_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1405_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1401_; 
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v_snd_1391_);
v___x_1401_ = v___x_1398_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_snd_1391_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v_cache_1393_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v_zetaDeltaFVarIds_1394_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v_postponed_1395_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v_diag_1396_);
v___x_1401_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_st_ref_set(v___y_1383_, v___x_1401_);
v___x_1403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1403_, 0, v_fst_1390_);
return v___x_1403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg___boxed(lean_object* v_e_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_1407_, v___y_1408_);
lean_dec(v___y_1408_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(lean_object* v_e_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_1411_, v___y_1413_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(lean_object* v_e_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(v_e_1418_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(lean_object* v_expr_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v___y_1432_; uint8_t v___y_1433_; lean_object* v_a_1438_; lean_object* v___x_1441_; 
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
v___x_1441_ = lean_infer_type(v_expr_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v_a_1442_; lean_object* v___x_1443_; lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1461_; 
v_a_1442_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___x_1441_, 1);
v___x_1443_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_a_1442_, v___y_1427_);
v_a_1444_ = lean_ctor_get(v___x_1443_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v___x_1443_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1446_ = v___x_1443_;
v_isShared_1447_ = v_isSharedCheck_1461_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1443_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1461_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_a_1444_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1459_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1459_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1447_ == 0)
{
lean_ctor_set_tag(v___x_1446_, 1);
lean_ctor_set(v___x_1446_, 0, v_a_1449_);
v___x_1454_ = v___x_1446_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1458_; 
v_reuseFailAlloc_1458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1458_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1458_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
lean_object* v___x_1456_; 
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1454_);
v___x_1456_ = v___x_1451_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1454_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_object* v_a_1460_; 
lean_del_object(v___x_1446_);
v_a_1460_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1460_);
lean_dec_ref_known(v___x_1448_, 1);
v_a_1438_ = v_a_1460_;
goto v___jp_1437_;
}
}
}
else
{
lean_object* v_a_1462_; 
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
v_a_1462_ = lean_ctor_get(v___x_1441_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1441_, 1);
v_a_1438_ = v_a_1462_;
goto v___jp_1437_;
}
v___jp_1431_:
{
if (v___y_1433_ == 0)
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
lean_dec_ref(v___y_1432_);
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1434_);
return v___x_1435_;
}
else
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___y_1432_);
return v___x_1436_;
}
}
v___jp_1437_:
{
uint8_t v___x_1439_; 
v___x_1439_ = l_Lean_Exception_isInterrupt(v_a_1438_);
if (v___x_1439_ == 0)
{
uint8_t v___x_1440_; 
lean_inc_ref(v_a_1438_);
v___x_1440_ = l_Lean_Exception_isRuntime(v_a_1438_);
v___y_1432_ = v_a_1438_;
v___y_1433_ = v___x_1440_;
goto v___jp_1431_;
}
else
{
v___y_1432_ = v_a_1438_;
v___y_1433_ = v___x_1439_;
goto v___jp_1431_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed(lean_object* v_expr_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(v_expr_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1(lean_object* v_val_1470_, lean_object* v_val_1471_, lean_object* v_text_1472_, lean_object* v_decl_1473_){
_start:
{
lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v_val_1470_);
lean_ctor_set(v___x_1474_, 1, v_val_1471_);
v___x_1475_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1472_, v___x_1474_);
v___x_1476_ = l_Lean_Name_getString_x21(v_decl_1473_);
v___x_1477_ = lean_box(0);
v___x_1478_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1475_);
lean_ctor_set(v___x_1478_, 1, v___x_1476_);
lean_ctor_set(v___x_1478_, 2, v___x_1477_);
lean_ctor_set(v___x_1478_, 3, v___x_1477_);
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_decl_1473_);
lean_ctor_set(v___x_1479_, 1, v___x_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(size_t v_sz_1480_, size_t v_i_1481_, lean_object* v_bs_1482_){
_start:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_usize_dec_lt(v_i_1481_, v_sz_1480_);
if (v___x_1483_ == 0)
{
return v_bs_1482_;
}
else
{
lean_object* v_v_1484_; lean_object* v___x_1485_; lean_object* v_bs_x27_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; size_t v___x_1489_; size_t v___x_1490_; lean_object* v___x_1491_; 
v_v_1484_ = lean_array_uget(v_bs_1482_, v_i_1481_);
v___x_1485_ = lean_unsigned_to_nat(0u);
v_bs_x27_1486_ = lean_array_uset(v_bs_1482_, v_i_1481_, v___x_1485_);
v___x_1487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___redArg___closed__0));
v___x_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_v_1484_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = ((size_t)1ULL);
v___x_1490_ = lean_usize_add(v_i_1481_, v___x_1489_);
v___x_1491_ = lean_array_uset(v_bs_x27_1486_, v_i_1481_, v___x_1488_);
v_i_1481_ = v___x_1490_;
v_bs_1482_ = v___x_1491_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1___boxed(lean_object* v_sz_1493_, lean_object* v_i_1494_, lean_object* v_bs_1495_){
_start:
{
size_t v_sz_boxed_1496_; size_t v_i_boxed_1497_; lean_object* v_res_1498_; 
v_sz_boxed_1496_ = lean_unbox_usize(v_sz_1493_);
lean_dec(v_sz_1493_);
v_i_boxed_1497_ = lean_unbox_usize(v_i_1494_);
lean_dec(v_i_1494_);
v_res_1498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_boxed_1496_, v_i_boxed_1497_, v_bs_1495_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object* v_doc_1499_, lean_object* v_ctx_1500_, lean_object* v_ti_1501_){
_start:
{
lean_object* v_toElabInfo_1503_; lean_object* v_lctx_1504_; lean_object* v_expr_1505_; lean_object* v_stx_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; 
v_toElabInfo_1503_ = lean_ctor_get(v_ti_1501_, 0);
lean_inc_ref(v_toElabInfo_1503_);
v_lctx_1504_ = lean_ctor_get(v_ti_1501_, 1);
lean_inc_ref(v_lctx_1504_);
v_expr_1505_ = lean_ctor_get(v_ti_1501_, 3);
lean_inc_ref(v_expr_1505_);
lean_dec_ref(v_ti_1501_);
v_stx_1506_ = lean_ctor_get(v_toElabInfo_1503_, 1);
lean_inc(v_stx_1506_);
lean_dec_ref(v_toElabInfo_1503_);
v___x_1507_ = 1;
v___x_1508_ = l_Lean_Syntax_getPos_x3f(v_stx_1506_, v___x_1507_);
if (lean_obj_tag(v___x_1508_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1574_; 
v_val_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1574_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_val_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1574_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1506_, v___x_1507_);
lean_dec(v_stx_1506_);
if (lean_obj_tag(v___x_1513_) == 1)
{
lean_object* v_val_1514_; lean_object* v___f_1515_; lean_object* v___x_1516_; 
lean_del_object(v___x_1511_);
v_val_1514_ = lean_ctor_get(v___x_1513_, 0);
lean_inc(v_val_1514_);
lean_dec_ref_known(v___x_1513_, 1);
v___f_1515_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1515_, 0, v_expr_1505_);
lean_inc_ref(v_ctx_1500_);
v___x_1516_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1500_, v_lctx_1504_, v___f_1515_);
if (lean_obj_tag(v___x_1516_) == 0)
{
lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1561_; 
v_a_1517_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1519_ = v___x_1516_;
v_isShared_1520_ = v_isSharedCheck_1561_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_dec(v___x_1516_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1561_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
if (lean_obj_tag(v_a_1517_) == 1)
{
lean_object* v_val_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1556_; 
v_val_1521_ = lean_ctor_get(v_a_1517_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_a_1517_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1523_ = v_a_1517_;
v_isShared_1524_ = v_isSharedCheck_1556_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_val_1521_);
lean_dec(v_a_1517_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1556_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; uint8_t v___x_1527_; 
v___x_1525_ = lean_array_get_size(v_val_1521_);
v___x_1526_ = lean_unsigned_to_nat(0u);
v___x_1527_ = lean_nat_dec_eq(v___x_1525_, v___x_1526_);
if (v___x_1527_ == 0)
{
lean_object* v_toEditableDocumentCore_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1550_; 
v_toEditableDocumentCore_1528_ = lean_ctor_get(v_doc_1499_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v_doc_1499_);
if (v_isSharedCheck_1550_ == 0)
{
lean_object* v_unused_1551_; 
v_unused_1551_ = lean_ctor_get(v_doc_1499_, 1);
lean_dec(v_unused_1551_);
v___x_1530_ = v_doc_1499_;
v_isShared_1531_ = v_isSharedCheck_1550_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_toEditableDocumentCore_1528_);
lean_dec(v_doc_1499_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1550_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_meta_1532_; lean_object* v_text_1533_; lean_object* v_source_1534_; lean_object* v___f_1535_; lean_object* v___x_1536_; size_t v_sz_1537_; size_t v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v_meta_1532_ = lean_ctor_get(v_toEditableDocumentCore_1528_, 0);
lean_inc_ref(v_meta_1532_);
lean_dec_ref(v_toEditableDocumentCore_1528_);
v_text_1533_ = lean_ctor_get(v_meta_1532_, 3);
lean_inc_ref(v_text_1533_);
lean_dec_ref(v_meta_1532_);
v_source_1534_ = lean_ctor_get(v_text_1533_, 0);
lean_inc_ref(v_source_1534_);
lean_inc(v_val_1514_);
lean_inc(v_val_1509_);
v___f_1535_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(v___f_1535_, 0, v_val_1509_);
lean_closure_set(v___f_1535_, 1, v_val_1514_);
lean_closure_set(v___f_1535_, 2, v_text_1533_);
v___x_1536_ = lean_string_utf8_extract(v_source_1534_, v_val_1509_, v_val_1514_);
lean_dec(v_val_1514_);
lean_dec(v_val_1509_);
lean_dec_ref(v_source_1534_);
v_sz_1537_ = lean_array_size(v_val_1521_);
v___x_1538_ = ((size_t)0ULL);
v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_1537_, v___x_1538_, v_val_1521_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v___x_1539_);
lean_ctor_set(v___x_1530_, 0, v___x_1536_);
v___x_1541_ = v___x_1530_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1549_, 1, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1542_; lean_object* v___x_1544_; 
v___x_1542_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v_ctx_1500_);
lean_ctor_set(v___x_1542_, 2, v___f_1535_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1542_);
v___x_1544_ = v___x_1523_;
goto v_reusejp_1543_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v___x_1542_);
v___x_1544_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1543_;
}
v_reusejp_1543_:
{
lean_object* v___x_1546_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1544_);
v___x_1546_ = v___x_1519_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
}
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_del_object(v___x_1523_);
lean_dec(v_val_1521_);
lean_dec(v_val_1514_);
lean_dec(v_val_1509_);
lean_dec_ref(v_ctx_1500_);
lean_dec_ref(v_doc_1499_);
v___x_1552_ = lean_box(0);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1552_);
v___x_1554_ = v___x_1519_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
lean_dec(v_a_1517_);
lean_dec(v_val_1514_);
lean_dec(v_val_1509_);
lean_dec_ref(v_ctx_1500_);
lean_dec_ref(v_doc_1499_);
v___x_1557_ = lean_box(0);
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 0, v___x_1557_);
v___x_1559_ = v___x_1519_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v___x_1557_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_dec(v_val_1514_);
lean_dec(v_val_1509_);
lean_dec_ref(v_ctx_1500_);
lean_dec_ref(v_doc_1499_);
v_a_1562_ = lean_ctor_get(v___x_1516_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1516_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1516_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1516_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
else
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
lean_dec(v___x_1513_);
lean_dec(v_val_1509_);
lean_dec_ref(v_expr_1505_);
lean_dec_ref(v_lctx_1504_);
lean_dec_ref(v_ctx_1500_);
lean_dec_ref(v_doc_1499_);
v___x_1570_ = lean_box(0);
if (v_isShared_1512_ == 0)
{
lean_ctor_set_tag(v___x_1511_, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1570_);
v___x_1572_ = v___x_1511_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
lean_dec(v___x_1508_);
lean_dec(v_stx_1506_);
lean_dec_ref(v_expr_1505_);
lean_dec_ref(v_lctx_1504_);
lean_dec_ref(v_ctx_1500_);
lean_dec_ref(v_doc_1499_);
v___x_1575_ = lean_box(0);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___boxed(lean_object* v_doc_1577_, lean_object* v_ctx_1578_, lean_object* v_ti_1579_, lean_object* v_a_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_Server_FileWorker_computeDotQuery_x3f(v_doc_1577_, v_ctx_1578_, v_ti_1579_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(lean_object* v_doc_1582_, lean_object* v_val_1583_, lean_object* v_val_1584_, lean_object* v_decl_1585_){
_start:
{
lean_object* v_toEditableDocumentCore_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1609_; 
v_toEditableDocumentCore_1586_ = lean_ctor_get(v_doc_1582_, 0);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_doc_1582_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; 
v_unused_1610_ = lean_ctor_get(v_doc_1582_, 1);
lean_dec(v_unused_1610_);
v___x_1588_ = v_doc_1582_;
v_isShared_1589_ = v_isSharedCheck_1609_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_toEditableDocumentCore_1586_);
lean_dec(v_doc_1582_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1609_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v_meta_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1605_; 
v_meta_1590_ = lean_ctor_get(v_toEditableDocumentCore_1586_, 0);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_toEditableDocumentCore_1586_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; lean_object* v_unused_1607_; lean_object* v_unused_1608_; 
v_unused_1606_ = lean_ctor_get(v_toEditableDocumentCore_1586_, 3);
lean_dec(v_unused_1606_);
v_unused_1607_ = lean_ctor_get(v_toEditableDocumentCore_1586_, 2);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_toEditableDocumentCore_1586_, 1);
lean_dec(v_unused_1608_);
v___x_1592_ = v_toEditableDocumentCore_1586_;
v_isShared_1593_ = v_isSharedCheck_1605_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_meta_1590_);
lean_dec(v_toEditableDocumentCore_1586_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1605_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v_text_1594_; lean_object* v___x_1596_; 
v_text_1594_ = lean_ctor_get(v_meta_1590_, 3);
lean_inc_ref(v_text_1594_);
lean_dec_ref(v_meta_1590_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v_val_1584_);
lean_ctor_set(v___x_1588_, 0, v_val_1583_);
v___x_1596_ = v___x_1588_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_val_1583_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_val_1584_);
v___x_1596_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1597_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1594_, v___x_1596_);
v___x_1598_ = l_Lean_Name_getString_x21(v_decl_1585_);
v___x_1599_ = lean_box(0);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 3, v___x_1599_);
lean_ctor_set(v___x_1592_, 2, v___x_1599_);
lean_ctor_set(v___x_1592_, 1, v___x_1598_);
lean_ctor_set(v___x_1592_, 0, v___x_1597_);
v___x_1601_ = v___x_1592_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1598_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; 
v___x_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1602_, 0, v_decl_1585_);
lean_ctor_set(v___x_1602_, 1, v___x_1601_);
return v___x_1602_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object* v_doc_1611_, lean_object* v_ctx_1612_, lean_object* v_stx_1613_, lean_object* v_id_1614_, lean_object* v_lctx_1615_, lean_object* v_expectedType_x3f_1616_){
_start:
{
uint8_t v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = 1;
v___x_1619_ = l_Lean_Syntax_getPos_x3f(v_stx_1613_, v___x_1618_);
if (lean_obj_tag(v___x_1619_) == 1)
{
lean_object* v_val_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1679_; 
v_val_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1679_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_val_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1679_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1613_, v___x_1618_);
if (lean_obj_tag(v___x_1624_) == 1)
{
lean_del_object(v___x_1622_);
if (lean_obj_tag(v_expectedType_x3f_1616_) == 1)
{
lean_object* v_val_1625_; lean_object* v_val_1626_; lean_object* v___x_1628_; uint8_t v_isShared_1629_; uint8_t v_isSharedCheck_1665_; 
v_val_1625_ = lean_ctor_get(v___x_1624_, 0);
lean_inc(v_val_1625_);
lean_dec_ref_known(v___x_1624_, 1);
v_val_1626_ = lean_ctor_get(v_expectedType_x3f_1616_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_expectedType_x3f_1616_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1628_ = v_expectedType_x3f_1616_;
v_isShared_1629_ = v_isSharedCheck_1665_;
goto v_resetjp_1627_;
}
else
{
lean_inc(v_val_1626_);
lean_dec(v_expectedType_x3f_1616_);
v___x_1628_ = lean_box(0);
v_isShared_1629_ = v_isSharedCheck_1665_;
goto v_resetjp_1627_;
}
v_resetjp_1627_:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1630_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getDotIdCompletionTypeNames___boxed), 6, 1);
lean_closure_set(v___x_1630_, 0, v_val_1626_);
lean_inc_ref(v_ctx_1612_);
v___x_1631_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1612_, v_lctx_1615_, v___x_1630_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1656_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1656_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1656_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1637_; uint8_t v___x_1638_; 
v___x_1636_ = lean_array_get_size(v_a_1632_);
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = lean_nat_dec_eq(v___x_1636_, v___x_1637_);
if (v___x_1638_ == 0)
{
lean_object* v___f_1639_; lean_object* v___x_1640_; size_t v_sz_1641_; size_t v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___f_1639_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0), 4, 3);
lean_closure_set(v___f_1639_, 0, v_doc_1611_);
lean_closure_set(v___f_1639_, 1, v_val_1620_);
lean_closure_set(v___f_1639_, 2, v_val_1625_);
v___x_1640_ = l_Lean_Name_toString(v_id_1614_, v___x_1618_);
v_sz_1641_ = lean_array_size(v_a_1632_);
v___x_1642_ = ((size_t)0ULL);
v___x_1643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_1641_, v___x_1642_, v_a_1632_);
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v___x_1640_);
lean_ctor_set(v___x_1644_, 1, v___x_1643_);
v___x_1645_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1645_, 0, v___x_1644_);
lean_ctor_set(v___x_1645_, 1, v_ctx_1612_);
lean_ctor_set(v___x_1645_, 2, v___f_1639_);
if (v_isShared_1629_ == 0)
{
lean_ctor_set(v___x_1628_, 0, v___x_1645_);
v___x_1647_ = v___x_1628_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
lean_object* v___x_1649_; 
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1647_);
v___x_1649_ = v___x_1634_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v___x_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
}
else
{
lean_object* v___x_1652_; lean_object* v___x_1654_; 
lean_dec(v_a_1632_);
lean_del_object(v___x_1628_);
lean_dec(v_val_1625_);
lean_dec(v_val_1620_);
lean_dec(v_id_1614_);
lean_dec_ref(v_ctx_1612_);
lean_dec_ref(v_doc_1611_);
v___x_1652_ = lean_box(0);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1652_);
v___x_1654_ = v___x_1634_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v___x_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_del_object(v___x_1628_);
lean_dec(v_val_1625_);
lean_dec(v_val_1620_);
lean_dec(v_id_1614_);
lean_dec_ref(v_ctx_1612_);
lean_dec_ref(v_doc_1611_);
v_a_1657_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1631_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1631_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
else
{
lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1673_; 
lean_dec(v_val_1620_);
lean_dec(v_expectedType_x3f_1616_);
lean_dec_ref(v_lctx_1615_);
lean_dec(v_id_1614_);
lean_dec_ref(v_ctx_1612_);
lean_dec_ref(v_doc_1611_);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1624_);
if (v_isSharedCheck_1673_ == 0)
{
lean_object* v_unused_1674_; 
v_unused_1674_ = lean_ctor_get(v___x_1624_, 0);
lean_dec(v_unused_1674_);
v___x_1667_ = v___x_1624_;
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
else
{
lean_dec(v___x_1624_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1673_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1669_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
if (v_isShared_1668_ == 0)
{
lean_ctor_set_tag(v___x_1667_, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1669_);
v___x_1671_ = v___x_1667_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
else
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
lean_dec(v___x_1624_);
lean_dec(v_val_1620_);
lean_dec(v_expectedType_x3f_1616_);
lean_dec_ref(v_lctx_1615_);
lean_dec(v_id_1614_);
lean_dec_ref(v_ctx_1612_);
lean_dec_ref(v_doc_1611_);
v___x_1675_ = lean_box(0);
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1675_);
v___x_1677_ = v___x_1622_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v___x_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v___x_1680_; lean_object* v___x_1681_; 
lean_dec(v___x_1619_);
lean_dec(v_expectedType_x3f_1616_);
lean_dec_ref(v_lctx_1615_);
lean_dec(v_id_1614_);
lean_dec_ref(v_ctx_1612_);
lean_dec_ref(v_doc_1611_);
v___x_1680_ = lean_box(0);
v___x_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1680_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object* v_doc_1682_, lean_object* v_ctx_1683_, lean_object* v_stx_1684_, lean_object* v_id_1685_, lean_object* v_lctx_1686_, lean_object* v_expectedType_x3f_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(v_doc_1682_, v_ctx_1683_, v_stx_1684_, v_id_1685_, v_lctx_1686_, v_expectedType_x3f_1687_);
lean_dec(v_stx_1684_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(lean_object* v_doc_1690_, lean_object* v_as_1691_, size_t v_sz_1692_, size_t v_i_1693_, lean_object* v_b_1694_){
_start:
{
lean_object* v_a_1697_; lean_object* v_query_x3f_1702_; uint8_t v___x_1705_; 
v___x_1705_ = lean_usize_dec_lt(v_i_1693_, v_sz_1692_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec_ref(v_doc_1690_);
v___x_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1706_, 0, v_b_1694_);
return v___x_1706_;
}
else
{
lean_object* v_a_1707_; lean_object* v_fst_1708_; lean_object* v_info_1709_; 
v_a_1707_ = lean_array_uget_borrowed(v_as_1691_, v_i_1693_);
v_fst_1708_ = lean_ctor_get(v_a_1707_, 0);
v_info_1709_ = lean_ctor_get(v_fst_1708_, 2);
switch(lean_obj_tag(v_info_1709_))
{
case 1:
{
lean_object* v_ctx_1710_; lean_object* v_stx_1711_; lean_object* v_id_1712_; lean_object* v___x_1713_; 
v_ctx_1710_ = lean_ctor_get(v_fst_1708_, 1);
v_stx_1711_ = lean_ctor_get(v_info_1709_, 0);
v_id_1712_ = lean_ctor_get(v_info_1709_, 1);
lean_inc(v_id_1712_);
lean_inc_ref(v_ctx_1710_);
lean_inc_ref(v_doc_1690_);
v___x_1713_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(v_doc_1690_, v_ctx_1710_, v_stx_1711_, v_id_1712_);
v_query_x3f_1702_ = v___x_1713_;
goto v___jp_1701_;
}
case 0:
{
lean_object* v_ctx_1714_; lean_object* v_termInfo_1715_; lean_object* v___x_1716_; 
v_ctx_1714_ = lean_ctor_get(v_fst_1708_, 1);
v_termInfo_1715_ = lean_ctor_get(v_info_1709_, 0);
lean_inc_ref(v_termInfo_1715_);
lean_inc_ref(v_ctx_1714_);
lean_inc_ref(v_doc_1690_);
v___x_1716_ = l_Lean_Server_FileWorker_computeDotQuery_x3f(v_doc_1690_, v_ctx_1714_, v_termInfo_1715_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; 
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
lean_inc(v_a_1717_);
lean_dec_ref_known(v___x_1716_, 1);
v_query_x3f_1702_ = v_a_1717_;
goto v___jp_1701_;
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref(v_b_1694_);
lean_dec_ref(v_doc_1690_);
v_a_1718_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1720_ = v___x_1716_;
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_a_1718_);
lean_dec(v___x_1716_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = l_Lean_Server_RequestError_ofIoError(v_a_1718_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 0, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
case 2:
{
lean_object* v_ctx_1727_; lean_object* v_stx_1728_; lean_object* v_id_1729_; lean_object* v_lctx_1730_; lean_object* v_expectedType_x3f_1731_; lean_object* v___x_1732_; 
v_ctx_1727_ = lean_ctor_get(v_fst_1708_, 1);
v_stx_1728_ = lean_ctor_get(v_info_1709_, 0);
v_id_1729_ = lean_ctor_get(v_info_1709_, 1);
v_lctx_1730_ = lean_ctor_get(v_info_1709_, 2);
v_expectedType_x3f_1731_ = lean_ctor_get(v_info_1709_, 3);
lean_inc(v_expectedType_x3f_1731_);
lean_inc_ref(v_lctx_1730_);
lean_inc(v_id_1729_);
lean_inc_ref(v_ctx_1727_);
lean_inc_ref(v_doc_1690_);
v___x_1732_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(v_doc_1690_, v_ctx_1727_, v_stx_1728_, v_id_1729_, v_lctx_1730_, v_expectedType_x3f_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v_a_1733_; 
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref_known(v___x_1732_, 1);
v_query_x3f_1702_ = v_a_1733_;
goto v___jp_1701_;
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
lean_dec_ref(v_b_1694_);
lean_dec_ref(v_doc_1690_);
v_a_1734_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1736_ = v___x_1732_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_a_1734_);
lean_dec(v___x_1732_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = l_Lean_Server_RequestError_ofIoError(v_a_1734_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 0, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
default: 
{
v_a_1697_ = v_b_1694_;
goto v___jp_1696_;
}
}
}
v___jp_1696_:
{
size_t v___x_1698_; size_t v___x_1699_; 
v___x_1698_ = ((size_t)1ULL);
v___x_1699_ = lean_usize_add(v_i_1693_, v___x_1698_);
v_i_1693_ = v___x_1699_;
v_b_1694_ = v_a_1697_;
goto _start;
}
v___jp_1701_:
{
if (lean_obj_tag(v_query_x3f_1702_) == 1)
{
lean_object* v_val_1703_; lean_object* v___x_1704_; 
v_val_1703_ = lean_ctor_get(v_query_x3f_1702_, 0);
lean_inc(v_val_1703_);
lean_dec_ref_known(v_query_x3f_1702_, 1);
v___x_1704_ = lean_array_push(v_b_1694_, v_val_1703_);
v_a_1697_ = v___x_1704_;
goto v___jp_1696_;
}
else
{
lean_dec(v_query_x3f_1702_);
v_a_1697_ = v_b_1694_;
goto v___jp_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg___boxed(lean_object* v_doc_1743_, lean_object* v_as_1744_, lean_object* v_sz_1745_, lean_object* v_i_1746_, lean_object* v_b_1747_, lean_object* v___y_1748_){
_start:
{
size_t v_sz_boxed_1749_; size_t v_i_boxed_1750_; lean_object* v_res_1751_; 
v_sz_boxed_1749_ = lean_unbox_usize(v_sz_1745_);
lean_dec(v_sz_1745_);
v_i_boxed_1750_ = lean_unbox_usize(v_i_1746_);
lean_dec(v_i_1746_);
v_res_1751_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_1743_, v_as_1744_, v_sz_boxed_1749_, v_i_boxed_1750_, v_b_1747_);
lean_dec_ref(v_as_1744_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(lean_object* v_doc_1752_, lean_object* v_as_1753_, size_t v_sz_1754_, size_t v_i_1755_, lean_object* v_b_1756_, lean_object* v___y_1757_){
_start:
{
uint8_t v___x_1759_; 
v___x_1759_ = lean_usize_dec_lt(v_i_1755_, v_sz_1754_);
if (v___x_1759_ == 0)
{
lean_object* v___x_1760_; 
lean_dec_ref(v_doc_1752_);
v___x_1760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1760_, 0, v_b_1756_);
return v___x_1760_;
}
else
{
lean_object* v_a_1761_; size_t v_sz_1762_; size_t v___x_1763_; lean_object* v___x_1764_; 
v_a_1761_ = lean_array_uget_borrowed(v_as_1753_, v_i_1755_);
v_sz_1762_ = lean_array_size(v_a_1761_);
v___x_1763_ = ((size_t)0ULL);
lean_inc_ref(v_doc_1752_);
v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_1752_, v_a_1761_, v_sz_1762_, v___x_1763_, v_b_1756_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
lean_inc(v_a_1765_);
v___x_1766_ = lean_array_get_size(v_a_1765_);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_nat_dec_eq(v___x_1766_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec(v_a_1765_);
lean_dec_ref(v_doc_1752_);
return v___x_1764_;
}
else
{
size_t v___x_1769_; size_t v___x_1770_; 
lean_dec_ref_known(v___x_1764_, 1);
v___x_1769_ = ((size_t)1ULL);
v___x_1770_ = lean_usize_add(v_i_1755_, v___x_1769_);
v_i_1755_ = v___x_1770_;
v_b_1756_ = v_a_1765_;
goto _start;
}
}
else
{
lean_dec_ref(v_doc_1752_);
return v___x_1764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1___boxed(lean_object* v_doc_1772_, lean_object* v_as_1773_, lean_object* v_sz_1774_, lean_object* v_i_1775_, lean_object* v_b_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_){
_start:
{
size_t v_sz_boxed_1779_; size_t v_i_boxed_1780_; lean_object* v_res_1781_; 
v_sz_boxed_1779_ = lean_unbox_usize(v_sz_1774_);
lean_dec(v_sz_1774_);
v_i_boxed_1780_ = lean_unbox_usize(v_i_1775_);
lean_dec(v_i_1775_);
v_res_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_1772_, v_as_1773_, v_sz_boxed_1779_, v_i_boxed_1780_, v_b_1776_, v___y_1777_);
lean_dec_ref(v___y_1777_);
lean_dec_ref(v_as_1773_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries(lean_object* v_doc_1784_, lean_object* v_requestedPos_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_toEditableDocumentCore_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v_toEditableDocumentCore_1788_ = lean_ctor_get(v_doc_1784_, 0);
v___x_1789_ = 1;
lean_inc(v_requestedPos_1785_);
lean_inc_ref(v_doc_1784_);
v___x_1790_ = l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_1784_, v_requestedPos_1785_, v___x_1789_);
v___x_1791_ = lean_task_get_own(v___x_1790_);
if (lean_obj_tag(v___x_1791_) == 1)
{
lean_object* v_val_1792_; lean_object* v_meta_1793_; lean_object* v_fst_1794_; lean_object* v_snd_1795_; lean_object* v_text_1796_; lean_object* v___x_1797_; lean_object* v_fst_1798_; lean_object* v_queries_1799_; size_t v_sz_1800_; size_t v___x_1801_; lean_object* v___x_1802_; 
v_val_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v_meta_1793_ = lean_ctor_get(v_toEditableDocumentCore_1788_, 0);
v_fst_1794_ = lean_ctor_get(v_val_1792_, 0);
lean_inc(v_fst_1794_);
v_snd_1795_ = lean_ctor_get(v_val_1792_, 1);
lean_inc(v_snd_1795_);
lean_dec(v_val_1792_);
v_text_1796_ = lean_ctor_get(v_meta_1793_, 3);
lean_inc_ref(v_text_1796_);
v___x_1797_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(v_text_1796_, v_requestedPos_1785_, v_fst_1794_, v_snd_1795_);
v_fst_1798_ = lean_ctor_get(v___x_1797_, 0);
lean_inc(v_fst_1798_);
lean_dec_ref(v___x_1797_);
v_queries_1799_ = ((lean_object*)(l_Lean_Server_FileWorker_computeQueries___closed__0));
v_sz_1800_ = lean_array_size(v_fst_1798_);
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_1784_, v_fst_1798_, v_sz_1800_, v___x_1801_, v_queries_1799_, v_a_1786_);
lean_dec(v_fst_1798_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
lean_dec(v___x_1791_);
lean_dec(v_requestedPos_1785_);
lean_dec_ref(v_doc_1784_);
v___x_1803_ = ((lean_object*)(l_Lean_Server_FileWorker_computeQueries___closed__0));
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries___boxed(lean_object* v_doc_1805_, lean_object* v_requestedPos_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_Server_FileWorker_computeQueries(v_doc_1805_, v_requestedPos_1806_, v_a_1807_);
lean_dec_ref(v_a_1807_);
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(lean_object* v_doc_1810_, lean_object* v_as_1811_, size_t v_sz_1812_, size_t v_i_1813_, lean_object* v_b_1814_, lean_object* v___y_1815_){
_start:
{
lean_object* v___x_1817_; 
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_1810_, v_as_1811_, v_sz_1812_, v_i_1813_, v_b_1814_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___boxed(lean_object* v_doc_1818_, lean_object* v_as_1819_, lean_object* v_sz_1820_, lean_object* v_i_1821_, lean_object* v_b_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
size_t v_sz_boxed_1825_; size_t v_i_boxed_1826_; lean_object* v_res_1827_; 
v_sz_boxed_1825_ = lean_unbox_usize(v_sz_1820_);
lean_dec(v_sz_1820_);
v_i_boxed_1826_ = lean_unbox_usize(v_i_1821_);
lean_dec(v_i_1821_);
v_res_1827_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(v_doc_1818_, v_as_1819_, v_sz_boxed_1825_, v_i_boxed_1826_, v_b_1822_, v___y_1823_);
lean_dec_ref(v___y_1823_);
lean_dec_ref(v_as_1819_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(lean_object* v_params_1836_, lean_object* v_name_1837_){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1839_, 0, v_params_1836_);
lean_ctor_set(v___x_1839_, 1, v_name_1837_);
lean_ctor_set(v___x_1839_, 2, v___x_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object* v_params_1841_, lean_object* v_kind_1842_){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1843_ = lean_box(0);
v___x_1844_ = ((lean_object*)(l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0));
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_kind_1842_);
v___x_1846_ = ((lean_object*)(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider));
v___x_1847_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_1841_, v___x_1846_);
v___x_1848_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_1847_);
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
v___x_1850_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1843_);
lean_ctor_set(v___x_1850_, 1, v___x_1843_);
lean_ctor_set(v___x_1850_, 2, v___x_1844_);
lean_ctor_set(v___x_1850_, 3, v___x_1845_);
lean_ctor_set(v___x_1850_, 4, v___x_1843_);
lean_ctor_set(v___x_1850_, 5, v___x_1843_);
lean_ctor_set(v___x_1850_, 6, v___x_1843_);
lean_ctor_set(v___x_1850_, 7, v___x_1843_);
lean_ctor_set(v___x_1850_, 8, v___x_1843_);
lean_ctor_set(v___x_1850_, 9, v___x_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(lean_object* v_ctx_1855_, lean_object* v_mod_1856_){
_start:
{
lean_object* v_toCommandContextInfo_1857_; lean_object* v_parentDecl_x3f_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v_text_1864_; 
v_toCommandContextInfo_1857_ = lean_ctor_get(v_ctx_1855_, 0);
lean_inc_ref(v_toCommandContextInfo_1857_);
v_parentDecl_x3f_1858_ = lean_ctor_get(v_ctx_1855_, 1);
lean_inc(v_parentDecl_x3f_1858_);
lean_dec_ref(v_ctx_1855_);
v___x_1859_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0));
v___x_1860_ = 1;
v___x_1861_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_1856_, v___x_1860_);
v___x_1862_ = lean_string_append(v___x_1859_, v___x_1861_);
lean_dec_ref(v___x_1861_);
v___x_1863_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1));
v_text_1864_ = lean_string_append(v___x_1862_, v___x_1863_);
if (lean_obj_tag(v_parentDecl_x3f_1858_) == 1)
{
lean_object* v_val_1865_; lean_object* v_env_1866_; uint8_t v___x_1867_; 
v_val_1865_ = lean_ctor_get(v_parentDecl_x3f_1858_, 0);
lean_inc_n(v_val_1865_, 2);
lean_dec_ref_known(v_parentDecl_x3f_1858_, 1);
v_env_1866_ = lean_ctor_get(v_toCommandContextInfo_1857_, 0);
lean_inc_ref_n(v_env_1866_, 2);
lean_dec_ref(v_toCommandContextInfo_1857_);
v___x_1867_ = l_Lean_isMarkedMeta(v_env_1866_, v_val_1865_);
if (v___x_1867_ == 0)
{
uint8_t v_isExporting_1868_; 
lean_dec(v_val_1865_);
v_isExporting_1868_ = lean_ctor_get_uint8(v_env_1866_, sizeof(void*)*8);
lean_dec_ref(v_env_1866_);
if (v_isExporting_1868_ == 0)
{
return v_text_1864_;
}
else
{
lean_object* v___x_1869_; lean_object* v_text_1870_; 
v___x_1869_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2));
v_text_1870_ = lean_string_append(v___x_1869_, v_text_1864_);
lean_dec_ref(v_text_1864_);
return v_text_1870_;
}
}
else
{
lean_object* v___x_1871_; lean_object* v_text_1872_; uint8_t v___x_1873_; 
lean_dec_ref(v_env_1866_);
v___x_1871_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3));
v_text_1872_ = lean_string_append(v___x_1871_, v_text_1864_);
lean_dec_ref(v_text_1864_);
v___x_1873_ = l_Lean_isPrivateName(v_val_1865_);
lean_dec(v_val_1865_);
if (v___x_1873_ == 0)
{
if (v___x_1867_ == 0)
{
return v_text_1872_;
}
else
{
lean_object* v___x_1874_; lean_object* v_text_1875_; 
v___x_1874_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2));
v_text_1875_ = lean_string_append(v___x_1874_, v_text_1872_);
lean_dec_ref(v_text_1872_);
return v_text_1875_;
}
}
else
{
return v_text_1872_;
}
}
}
else
{
lean_dec(v_parentDecl_x3f_1858_);
lean_dec_ref(v_toCommandContextInfo_1857_);
return v_text_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0(lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
lean_object* v_response_1878_; lean_object* v___x_1880_; uint8_t v_isShared_1881_; uint8_t v_isSharedCheck_1896_; 
v_response_1878_ = lean_ctor_get(v_x_1877_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v_x_1877_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1880_ = v_x_1877_;
v_isShared_1881_ = v_isSharedCheck_1896_;
goto v_resetjp_1879_;
}
else
{
lean_inc(v_response_1878_);
lean_dec(v_x_1877_);
v___x_1880_ = lean_box(0);
v_isShared_1881_ = v_isSharedCheck_1896_;
goto v_resetjp_1879_;
}
v_resetjp_1879_:
{
lean_object* v___x_1882_; 
lean_inc(v_response_1878_);
v___x_1882_ = l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(v_response_1878_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; uint8_t v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_del_object(v___x_1880_);
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v___x_1882_, 1);
v___x_1884_ = 0;
v___x_1885_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0));
v___x_1886_ = l_Lean_Json_compress(v_response_1878_);
v___x_1887_ = lean_string_append(v___x_1885_, v___x_1886_);
lean_dec_ref(v___x_1886_);
v___x_1888_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1));
v___x_1889_ = lean_string_append(v___x_1887_, v___x_1888_);
v___x_1890_ = lean_string_append(v___x_1889_, v_a_1883_);
lean_dec(v_a_1883_);
v___x_1891_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set_uint8(v___x_1891_, sizeof(void*)*1, v___x_1884_);
return v___x_1891_;
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; 
lean_dec(v_response_1878_);
v_a_1892_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1892_);
lean_dec_ref_known(v___x_1882_, 1);
if (v_isShared_1881_ == 0)
{
lean_ctor_set(v___x_1880_, 0, v_a_1892_);
v___x_1894_ = v___x_1880_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1892_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
else
{
uint8_t v_code_1897_; lean_object* v_message_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
v_code_1897_ = lean_ctor_get_uint8(v_x_1877_, sizeof(void*)*1);
v_message_1898_ = lean_ctor_get(v_x_1877_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v_x_1877_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v_x_1877_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_message_1898_);
lean_dec(v_x_1877_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_message_1898_);
lean_ctor_set_uint8(v_reuseFailAlloc_1904_, sizeof(void*)*1, v_code_1897_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(lean_object* v_method_1907_, lean_object* v_param_1908_, lean_object* v_a_1909_){
_start:
{
lean_object* v_serverRequestEmitter_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___f_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v_serverRequestEmitter_1911_ = lean_ctor_get(v_a_1909_, 5);
v___x_1912_ = l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(v_param_1908_);
lean_inc_ref(v_serverRequestEmitter_1911_);
v___x_1913_ = lean_apply_3(v_serverRequestEmitter_1911_, v_method_1907_, v___x_1912_, lean_box(0));
v___f_1914_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0));
v___x_1915_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1914_, v___x_1913_);
v___x_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___boxed(lean_object* v_method_1917_, lean_object* v_param_1918_, lean_object* v_a_1919_, lean_object* v_a_1920_){
_start:
{
lean_object* v_res_1921_; 
v_res_1921_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v_method_1917_, v_param_1918_, v_a_1919_);
lean_dec_ref(v_a_1919_);
return v_res_1921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(lean_object* v_val_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1923_, 0, v_val_1922_);
return v___x_1923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(lean_object* v_val_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_val_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(size_t v_sz_1926_, size_t v_i_1927_, lean_object* v_bs_1928_){
_start:
{
uint8_t v___x_1929_; 
v___x_1929_ = lean_usize_dec_lt(v_i_1927_, v_sz_1926_);
if (v___x_1929_ == 0)
{
return v_bs_1928_;
}
else
{
lean_object* v_v_1930_; lean_object* v_toLeanModuleQuery_1931_; lean_object* v___x_1932_; lean_object* v_bs_x27_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v___x_1936_; 
v_v_1930_ = lean_array_uget_borrowed(v_bs_1928_, v_i_1927_);
v_toLeanModuleQuery_1931_ = lean_ctor_get(v_v_1930_, 0);
lean_inc_ref(v_toLeanModuleQuery_1931_);
v___x_1932_ = lean_unsigned_to_nat(0u);
v_bs_x27_1933_ = lean_array_uset(v_bs_1928_, v_i_1927_, v___x_1932_);
v___x_1934_ = ((size_t)1ULL);
v___x_1935_ = lean_usize_add(v_i_1927_, v___x_1934_);
v___x_1936_ = lean_array_uset(v_bs_x27_1933_, v_i_1927_, v_toLeanModuleQuery_1931_);
v_i_1927_ = v___x_1935_;
v_bs_1928_ = v___x_1936_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0___boxed(lean_object* v_sz_1938_, lean_object* v_i_1939_, lean_object* v_bs_1940_){
_start:
{
size_t v_sz_boxed_1941_; size_t v_i_boxed_1942_; lean_object* v_res_1943_; 
v_sz_boxed_1941_ = lean_unbox_usize(v_sz_1938_);
lean_dec(v_sz_1938_);
v_i_boxed_1942_ = lean_unbox_usize(v_i_1939_);
lean_dec(v_i_1939_);
v_res_1943_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_boxed_1941_, v_i_boxed_1942_, v_bs_1940_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(lean_object* v_a_1947_, lean_object* v_kind_1948_, lean_object* v___x_1949_, lean_object* v_params_1950_, lean_object* v___x_1951_, lean_object* v___x_1952_, lean_object* v_as_1953_, size_t v_sz_1954_, size_t v_i_1955_, lean_object* v_b_1956_){
_start:
{
lean_object* v_a_1959_; uint8_t v___x_1963_; 
v___x_1963_ = lean_usize_dec_lt(v_i_1955_, v_sz_1954_);
if (v___x_1963_ == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v___x_1951_);
lean_dec_ref(v_params_1950_);
lean_dec_ref(v___x_1949_);
lean_dec_ref(v_kind_1948_);
lean_dec_ref(v_a_1947_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v_b_1956_);
return v___x_1964_;
}
else
{
lean_object* v_a_1965_; lean_object* v_module_1966_; lean_object* v_decl_1967_; uint8_t v_isExactMatch_1968_; lean_object* v_fst_1969_; lean_object* v_snd_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_2061_; 
v_a_1965_ = lean_array_uget_borrowed(v_as_1953_, v_i_1955_);
v_module_1966_ = lean_ctor_get(v_a_1965_, 0);
v_decl_1967_ = lean_ctor_get(v_a_1965_, 1);
v_isExactMatch_1968_ = lean_ctor_get_uint8(v_a_1965_, sizeof(void*)*2);
v_fst_1969_ = lean_ctor_get(v_b_1956_, 0);
v_snd_1970_ = lean_ctor_get(v_b_1956_, 1);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_b_1956_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_1972_ = v_b_1956_;
v_isShared_1973_ = v_isSharedCheck_2061_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_snd_1970_);
lean_inc(v_fst_1969_);
lean_dec(v_b_1956_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_2061_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v_ctx_1974_; lean_object* v_determineInsertion_1975_; uint8_t v___y_1977_; uint8_t v___y_1978_; lean_object* v_toCommandContextInfo_2052_; lean_object* v_env_2053_; lean_object* v___x_2054_; uint8_t v___x_2055_; uint8_t v___y_2057_; uint8_t v___x_2060_; 
v_ctx_1974_ = lean_ctor_get(v_a_1947_, 1);
v_determineInsertion_1975_ = lean_ctor_get(v_a_1947_, 2);
v_toCommandContextInfo_2052_ = lean_ctor_get(v_ctx_1974_, 0);
v_env_2053_ = lean_ctor_get(v_toCommandContextInfo_2052_, 0);
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = lean_nat_dec_eq(v___x_1952_, v___x_2054_);
lean_inc(v_decl_1967_);
lean_inc_ref(v_env_2053_);
v___x_2060_ = l_Lean_Environment_contains(v_env_2053_, v_decl_1967_, v___x_1963_);
if (v___x_2060_ == 0)
{
v___y_2057_ = v___x_1963_;
goto v___jp_2056_;
}
else
{
v___y_2057_ = v___x_2055_;
goto v___jp_2056_;
}
v___jp_1976_:
{
if (v___y_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_inc_ref(v_determineInsertion_1975_);
lean_inc(v_decl_1967_);
v___x_1979_ = lean_apply_1(v_determineInsertion_1975_, v_decl_1967_);
if (v___y_1977_ == 0)
{
lean_object* v_fullName_1980_; lean_object* v_edit_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2008_; 
v_fullName_1980_ = lean_ctor_get(v___x_1979_, 0);
v_edit_1981_ = lean_ctor_get(v___x_1979_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1983_ = v___x_1979_;
v_isShared_1984_ = v_isSharedCheck_2008_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_edit_1981_);
lean_inc(v_fullName_1980_);
lean_dec(v___x_1979_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2008_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0));
v___x_1987_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fullName_1980_, v___x_1963_);
v___x_1988_ = lean_string_append(v___x_1986_, v___x_1987_);
lean_dec_ref(v___x_1987_);
lean_inc_ref(v_kind_1948_);
v___x_1989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1989_, 0, v_kind_1948_);
lean_inc_ref(v___x_1949_);
v___x_1990_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_1949_);
v___x_1991_ = lean_unsigned_to_nat(1u);
v___x_1992_ = lean_mk_empty_array_with_capacity(v___x_1991_);
v___x_1993_ = lean_array_push(v___x_1992_, v_edit_1981_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v___x_1993_);
lean_ctor_set(v___x_1983_, 0, v___x_1990_);
v___x_1995_ = v___x_1983_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1990_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_2007_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2005_; 
v___x_1996_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_1995_);
v___x_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
v___x_1998_ = ((lean_object*)(l_Lean_Server_FileWorker_importUnknownIdentifiersProvider));
lean_inc_ref(v_params_1950_);
v___x_1999_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_1950_, v___x_1998_);
v___x_2000_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_1999_);
v___x_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2001_, 0, v___x_2000_);
v___x_2002_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2002_, 0, v___x_1985_);
lean_ctor_set(v___x_2002_, 1, v___x_1985_);
lean_ctor_set(v___x_2002_, 2, v___x_1988_);
lean_ctor_set(v___x_2002_, 3, v___x_1989_);
lean_ctor_set(v___x_2002_, 4, v___x_1985_);
lean_ctor_set(v___x_2002_, 5, v___x_1985_);
lean_ctor_set(v___x_2002_, 6, v___x_1985_);
lean_ctor_set(v___x_2002_, 7, v___x_1997_);
lean_ctor_set(v___x_2002_, 8, v___x_1985_);
lean_ctor_set(v___x_2002_, 9, v___x_2001_);
v___x_2003_ = lean_array_push(v_fst_1969_, v___x_2002_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_2003_);
v___x_2005_ = v___x_1972_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_2003_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v_snd_1970_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
v_a_1959_ = v___x_2005_;
goto v___jp_1958_;
}
}
}
}
else
{
lean_object* v_fullName_2009_; lean_object* v_edit_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2048_; 
v_fullName_2009_ = lean_ctor_get(v___x_1979_, 0);
v_edit_2010_ = lean_ctor_get(v___x_1979_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_1979_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2012_ = v___x_1979_;
v_isShared_2013_ = v_isSharedCheck_2048_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_edit_2010_);
lean_inc(v_fullName_2009_);
lean_dec(v___x_1979_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2048_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2014_ = lean_box(0);
v___x_2015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1));
v___x_2016_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fullName_2009_, v___y_1977_);
v___x_2017_ = lean_string_append(v___x_2015_, v___x_2016_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2));
v___x_2019_ = lean_string_append(v___x_2017_, v___x_2018_);
lean_inc_n(v_module_1966_, 2);
v___x_2020_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_1966_, v___y_1977_);
v___x_2021_ = lean_string_append(v___x_2019_, v___x_2020_);
lean_dec_ref(v___x_2020_);
lean_inc_ref(v_kind_1948_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_kind_1948_);
lean_inc_ref(v___x_1949_);
v___x_2023_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_1949_);
lean_inc_ref(v_ctx_1974_);
v___x_2024_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_1974_, v_module_1966_);
lean_inc_ref(v___x_1951_);
v___x_2025_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2025_, 0, v___x_1951_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
lean_ctor_set(v___x_2025_, 2, v___x_2014_);
lean_ctor_set(v___x_2025_, 3, v___x_2014_);
v___x_2026_ = lean_unsigned_to_nat(2u);
v___x_2027_ = lean_mk_empty_array_with_capacity(v___x_2026_);
v___x_2028_ = lean_array_push(v___x_2027_, v___x_2025_);
v___x_2029_ = lean_array_push(v___x_2028_, v_edit_2010_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v___x_2029_);
lean_ctor_set(v___x_2012_, 0, v___x_2023_);
v___x_2031_ = v___x_2012_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2032_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_2031_);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
v___x_2034_ = ((lean_object*)(l_Lean_Server_FileWorker_importUnknownIdentifiersProvider));
lean_inc_ref(v_params_1950_);
v___x_2035_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_1950_, v___x_2034_);
v___x_2036_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_2035_);
v___x_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
v___x_2038_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2014_);
lean_ctor_set(v___x_2038_, 1, v___x_2014_);
lean_ctor_set(v___x_2038_, 2, v___x_2021_);
lean_ctor_set(v___x_2038_, 3, v___x_2022_);
lean_ctor_set(v___x_2038_, 4, v___x_2014_);
lean_ctor_set(v___x_2038_, 5, v___x_2014_);
lean_ctor_set(v___x_2038_, 6, v___x_2014_);
lean_ctor_set(v___x_2038_, 7, v___x_2033_);
lean_ctor_set(v___x_2038_, 8, v___x_2014_);
lean_ctor_set(v___x_2038_, 9, v___x_2037_);
v___x_2039_ = lean_array_push(v_fst_1969_, v___x_2038_);
if (v_isExactMatch_1968_ == 0)
{
lean_object* v___x_2041_; 
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 0, v___x_2039_);
v___x_2041_ = v___x_1972_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_snd_1970_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
v_a_1959_ = v___x_2041_;
goto v___jp_1958_;
}
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
lean_dec(v_snd_1970_);
v___x_2043_ = lean_box(v___x_1963_);
if (v_isShared_1973_ == 0)
{
lean_ctor_set(v___x_1972_, 1, v___x_2043_);
lean_ctor_set(v___x_1972_, 0, v___x_2039_);
v___x_2045_ = v___x_1972_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
v_a_1959_ = v___x_2045_;
goto v___jp_1958_;
}
}
}
}
}
}
else
{
lean_object* v___x_2050_; 
if (v_isShared_1973_ == 0)
{
v___x_2050_ = v___x_1972_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_fst_1969_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_snd_1970_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
v_a_1959_ = v___x_2050_;
goto v___jp_1958_;
}
}
}
v___jp_2056_:
{
if (v___y_2057_ == 0)
{
v___y_1977_ = v___y_2057_;
v___y_1978_ = v___x_2055_;
goto v___jp_1976_;
}
else
{
lean_object* v___x_2058_; uint8_t v___x_2059_; 
v___x_2058_ = l_Lean_Environment_mainModule(v_env_2053_);
v___x_2059_ = lean_name_eq(v_module_1966_, v___x_2058_);
lean_dec(v___x_2058_);
v___y_1977_ = v___y_2057_;
v___y_1978_ = v___x_2059_;
goto v___jp_1976_;
}
}
}
}
v___jp_1958_:
{
size_t v___x_1960_; size_t v___x_1961_; 
v___x_1960_ = ((size_t)1ULL);
v___x_1961_ = lean_usize_add(v_i_1955_, v___x_1960_);
v_i_1955_ = v___x_1961_;
v_b_1956_ = v_a_1959_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___boxed(lean_object* v_a_2062_, lean_object* v_kind_2063_, lean_object* v___x_2064_, lean_object* v_params_2065_, lean_object* v___x_2066_, lean_object* v___x_2067_, lean_object* v_as_2068_, lean_object* v_sz_2069_, lean_object* v_i_2070_, lean_object* v_b_2071_, lean_object* v___y_2072_){
_start:
{
size_t v_sz_boxed_2073_; size_t v_i_boxed_2074_; lean_object* v_res_2075_; 
v_sz_boxed_2073_ = lean_unbox_usize(v_sz_2069_);
lean_dec(v_sz_2069_);
v_i_boxed_2074_ = lean_unbox_usize(v_i_2070_);
lean_dec(v_i_2070_);
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_2062_, v_kind_2063_, v___x_2064_, v_params_2065_, v___x_2066_, v___x_2067_, v_as_2068_, v_sz_boxed_2073_, v_i_boxed_2074_, v_b_2071_);
lean_dec_ref(v_as_2068_);
lean_dec(v___x_2067_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(lean_object* v_kind_2076_, lean_object* v___x_2077_, lean_object* v_params_2078_, lean_object* v___x_2079_, lean_object* v___x_2080_, lean_object* v_as_2081_, size_t v_sz_2082_, size_t v_i_2083_, lean_object* v_b_2084_, lean_object* v___y_2085_){
_start:
{
uint8_t v___x_2087_; 
v___x_2087_ = lean_usize_dec_lt(v_i_2083_, v_sz_2082_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2088_; 
lean_dec_ref(v___x_2079_);
lean_dec_ref(v_params_2078_);
lean_dec_ref(v___x_2077_);
lean_dec_ref(v_kind_2076_);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v_b_2084_);
return v___x_2088_;
}
else
{
lean_object* v_snd_2089_; lean_object* v_snd_2090_; lean_object* v_fst_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2156_; 
v_snd_2089_ = lean_ctor_get(v_b_2084_, 1);
lean_inc(v_snd_2089_);
v_snd_2090_ = lean_ctor_get(v_snd_2089_, 1);
lean_inc(v_snd_2090_);
v_fst_2091_ = lean_ctor_get(v_b_2084_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_b_2084_);
if (v_isSharedCheck_2156_ == 0)
{
lean_object* v_unused_2157_; 
v_unused_2157_ = lean_ctor_get(v_b_2084_, 1);
lean_dec(v_unused_2157_);
v___x_2093_ = v_b_2084_;
v_isShared_2094_ = v_isSharedCheck_2156_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_fst_2091_);
lean_dec(v_b_2084_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2156_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_fst_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2154_; 
v_fst_2095_ = lean_ctor_get(v_snd_2089_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_snd_2089_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; 
v_unused_2155_ = lean_ctor_get(v_snd_2089_, 1);
lean_dec(v_unused_2155_);
v___x_2097_ = v_snd_2089_;
v_isShared_2098_ = v_isSharedCheck_2154_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_fst_2095_);
lean_dec(v_snd_2089_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2154_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_array_2099_; lean_object* v_start_2100_; lean_object* v_stop_2101_; uint8_t v___x_2102_; 
v_array_2099_ = lean_ctor_get(v_snd_2090_, 0);
v_start_2100_ = lean_ctor_get(v_snd_2090_, 1);
v_stop_2101_ = lean_ctor_get(v_snd_2090_, 2);
v___x_2102_ = lean_nat_dec_lt(v_start_2100_, v_stop_2101_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2104_; 
lean_dec_ref(v___x_2079_);
lean_dec_ref(v_params_2078_);
lean_dec_ref(v___x_2077_);
lean_dec_ref(v_kind_2076_);
if (v_isShared_2098_ == 0)
{
v___x_2104_ = v___x_2097_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_fst_2095_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v_snd_2090_);
v___x_2104_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2106_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v___x_2104_);
v___x_2106_ = v___x_2093_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_fst_2091_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v___x_2104_);
v___x_2106_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
lean_object* v___x_2107_; 
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
return v___x_2107_;
}
}
}
else
{
lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2150_; 
lean_inc(v_stop_2101_);
lean_inc(v_start_2100_);
lean_inc_ref(v_array_2099_);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_snd_2090_);
if (v_isSharedCheck_2150_ == 0)
{
lean_object* v_unused_2151_; lean_object* v_unused_2152_; lean_object* v_unused_2153_; 
v_unused_2151_ = lean_ctor_get(v_snd_2090_, 2);
lean_dec(v_unused_2151_);
v_unused_2152_ = lean_ctor_get(v_snd_2090_, 1);
lean_dec(v_unused_2152_);
v_unused_2153_ = lean_ctor_get(v_snd_2090_, 0);
lean_dec(v_unused_2153_);
v___x_2111_ = v_snd_2090_;
v_isShared_2112_ = v_isSharedCheck_2150_;
goto v_resetjp_2110_;
}
else
{
lean_dec(v_snd_2090_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2150_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v_a_2113_; lean_object* v___x_2114_; lean_object* v___x_2116_; 
v_a_2113_ = lean_array_uget_borrowed(v_as_2081_, v_i_2083_);
v___x_2114_ = lean_array_fget_borrowed(v_array_2099_, v_start_2100_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v_fst_2095_);
lean_ctor_set(v___x_2097_, 0, v_fst_2091_);
v___x_2116_ = v___x_2097_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_fst_2091_);
lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_fst_2095_);
v___x_2116_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
size_t v_sz_2117_; size_t v___x_2118_; lean_object* v___x_2119_; 
v_sz_2117_ = lean_array_size(v___x_2114_);
v___x_2118_ = ((size_t)0ULL);
lean_inc_ref(v___x_2079_);
lean_inc_ref(v_params_2078_);
lean_inc_ref(v___x_2077_);
lean_inc_ref(v_kind_2076_);
lean_inc(v_a_2113_);
v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_2113_, v_kind_2076_, v___x_2077_, v_params_2078_, v___x_2079_, v___x_2080_, v___x_2114_, v_sz_2117_, v___x_2118_, v___x_2116_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v_a_2120_; lean_object* v_fst_2121_; lean_object* v_snd_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2140_; 
v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___x_2119_, 1);
v_fst_2121_ = lean_ctor_get(v_a_2120_, 0);
v_snd_2122_ = lean_ctor_get(v_a_2120_, 1);
v_isSharedCheck_2140_ = !lean_is_exclusive(v_a_2120_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2124_ = v_a_2120_;
v_isShared_2125_ = v_isSharedCheck_2140_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_snd_2122_);
lean_inc(v_fst_2121_);
lean_dec(v_a_2120_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2140_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2126_ = lean_unsigned_to_nat(1u);
v___x_2127_ = lean_nat_add(v_start_2100_, v___x_2126_);
lean_dec(v_start_2100_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 1, v___x_2127_);
v___x_2129_ = v___x_2111_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_array_2099_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2139_, 2, v_stop_2101_);
v___x_2129_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2131_; 
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v___x_2129_);
lean_ctor_set(v___x_2124_, 0, v_snd_2122_);
v___x_2131_ = v___x_2124_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_snd_2122_);
lean_ctor_set(v_reuseFailAlloc_2138_, 1, v___x_2129_);
v___x_2131_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
lean_object* v___x_2133_; 
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v___x_2131_);
lean_ctor_set(v___x_2093_, 0, v_fst_2121_);
v___x_2133_ = v___x_2093_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_fst_2121_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
size_t v___x_2134_; size_t v___x_2135_; 
v___x_2134_ = ((size_t)1ULL);
v___x_2135_ = lean_usize_add(v_i_2083_, v___x_2134_);
v_i_2083_ = v___x_2135_;
v_b_2084_ = v___x_2133_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2148_; 
lean_del_object(v___x_2111_);
lean_dec(v_stop_2101_);
lean_dec(v_start_2100_);
lean_dec_ref(v_array_2099_);
lean_del_object(v___x_2093_);
lean_dec_ref(v___x_2079_);
lean_dec_ref(v_params_2078_);
lean_dec_ref(v___x_2077_);
lean_dec_ref(v_kind_2076_);
v_a_2141_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2148_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2148_ == 0)
{
v___x_2143_ = v___x_2119_;
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_dec(v___x_2119_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2148_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2146_; 
if (v_isShared_2144_ == 0)
{
v___x_2146_ = v___x_2143_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___boxed(lean_object* v_kind_2158_, lean_object* v___x_2159_, lean_object* v_params_2160_, lean_object* v___x_2161_, lean_object* v___x_2162_, lean_object* v_as_2163_, lean_object* v_sz_2164_, lean_object* v_i_2165_, lean_object* v_b_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
size_t v_sz_boxed_2169_; size_t v_i_boxed_2170_; lean_object* v_res_2171_; 
v_sz_boxed_2169_ = lean_unbox_usize(v_sz_2164_);
lean_dec(v_sz_2164_);
v_i_boxed_2170_ = lean_unbox_usize(v_i_2165_);
lean_dec(v_i_2165_);
v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_2158_, v___x_2159_, v_params_2160_, v___x_2161_, v___x_2162_, v_as_2163_, v_sz_boxed_2169_, v_i_boxed_2170_, v_b_2166_, v___y_2167_);
lean_dec_ref(v___y_2167_);
lean_dec_ref(v_as_2163_);
lean_dec(v___x_2162_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object* v_id_2180_, lean_object* v_params_2181_, lean_object* v_requestedRange_2182_, lean_object* v_kind_2183_, lean_object* v_a_2184_){
_start:
{
lean_object* v_doc_2186_; lean_object* v_cancelTk_2187_; lean_object* v_toEditableDocumentCore_2188_; lean_object* v_stop_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2318_; 
v_doc_2186_ = lean_ctor_get(v_a_2184_, 1);
v_cancelTk_2187_ = lean_ctor_get(v_a_2184_, 4);
v_toEditableDocumentCore_2188_ = lean_ctor_get(v_doc_2186_, 0);
v_stop_2189_ = lean_ctor_get(v_requestedRange_2182_, 1);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_requestedRange_2182_);
if (v_isSharedCheck_2318_ == 0)
{
lean_object* v_unused_2319_; 
v_unused_2319_ = lean_ctor_get(v_requestedRange_2182_, 0);
lean_dec(v_unused_2319_);
v___x_2191_ = v_requestedRange_2182_;
v_isShared_2192_ = v_isSharedCheck_2318_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_stop_2189_);
lean_dec(v_requestedRange_2182_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2318_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; 
lean_inc_ref(v_doc_2186_);
v___x_2193_ = l_Lean_Server_FileWorker_computeQueries(v_doc_2186_, v_stop_2189_, v_a_2184_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2309_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2309_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2309_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; uint8_t v___x_2200_; 
v___x_2198_ = lean_array_get_size(v_a_2194_);
v___x_2199_ = lean_unsigned_to_nat(0u);
v___x_2200_ = lean_nat_dec_eq(v___x_2198_, v___x_2199_);
if (v___x_2200_ == 0)
{
lean_object* v___x_2201_; size_t v_sz_2202_; size_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
lean_del_object(v___x_2196_);
v___x_2201_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0));
v_sz_2202_ = lean_array_size(v_a_2194_);
v___x_2203_ = ((size_t)0ULL);
lean_inc(v_a_2194_);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_2202_, v___x_2203_, v_a_2194_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 1, v___x_2204_);
lean_ctor_set(v___x_2191_, 0, v_id_2180_);
v___x_2206_ = v___x_2191_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_id_2180_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v_a_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2303_; 
v___x_2207_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_2201_, v___x_2206_, v_a_2184_);
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2207_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2210_ = v___x_2207_;
v_isShared_2211_ = v_isSharedCheck_2303_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_a_2208_);
lean_dec(v___x_2207_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2303_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___f_2212_; lean_object* v___f_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___y_2222_; 
v___f_2212_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1));
v___f_2213_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2));
v___x_2214_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2212_, v_a_2208_);
v___x_2215_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_cancelTk_2187_);
v___x_2216_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2213_, v___x_2215_);
v___x_2217_ = lean_box(0);
v___x_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2216_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2214_);
lean_ctor_set(v___x_2219_, 1, v___x_2218_);
v___x_2220_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_2219_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_val_2241_; 
v_val_2241_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_val_2241_);
lean_dec_ref_known(v___x_2220_, 1);
if (lean_obj_tag(v_val_2241_) == 0)
{
lean_object* v_response_2242_; lean_object* v___y_2244_; lean_object* v_initSnap_2284_; lean_object* v_meta_2285_; lean_object* v_stx_2286_; lean_object* v___x_2287_; 
v_response_2242_ = lean_ctor_get(v_val_2241_, 0);
lean_inc(v_response_2242_);
lean_dec_ref_known(v_val_2241_, 1);
v_initSnap_2284_ = lean_ctor_get(v_toEditableDocumentCore_2188_, 1);
v_meta_2285_ = lean_ctor_get(v_toEditableDocumentCore_2188_, 0);
v_stx_2286_ = lean_ctor_get(v_initSnap_2284_, 3);
v___x_2287_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2286_, v___x_2200_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v___x_2288_; 
v___x_2288_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5));
v___y_2244_ = v___x_2288_;
goto v___jp_2243_;
}
else
{
lean_object* v_val_2289_; lean_object* v_text_2290_; lean_object* v___x_2291_; lean_object* v_line_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2301_; 
v_val_2289_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_val_2289_);
lean_dec_ref_known(v___x_2287_, 1);
v_text_2290_ = lean_ctor_get(v_meta_2285_, 3);
lean_inc_ref(v_text_2290_);
v___x_2291_ = l_Lean_FileMap_utf8PosToLspPos(v_text_2290_, v_val_2289_);
lean_dec(v_val_2289_);
v_line_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2301_ == 0)
{
lean_object* v_unused_2302_; 
v_unused_2302_ = lean_ctor_get(v___x_2291_, 1);
lean_dec(v_unused_2302_);
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2301_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_line_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2301_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2296_ = lean_unsigned_to_nat(1u);
v___x_2297_ = lean_nat_add(v_line_2292_, v___x_2296_);
lean_dec(v_line_2292_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 1, v___x_2199_);
lean_ctor_set(v___x_2294_, 0, v___x_2297_);
v___x_2299_ = v___x_2294_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
lean_ctor_set(v_reuseFailAlloc_2300_, 1, v___x_2199_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
v___y_2244_ = v___x_2299_;
goto v___jp_2243_;
}
}
}
v___jp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; uint8_t v___x_2248_; 
lean_inc_ref(v___y_2244_);
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___y_2244_);
lean_ctor_set(v___x_2245_, 1, v___y_2244_);
v___x_2246_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3));
v___x_2247_ = lean_array_get_size(v_response_2242_);
v___x_2248_ = lean_nat_dec_lt(v___x_2199_, v___x_2247_);
if (v___x_2248_ == 0)
{
lean_object* v___x_2250_; 
lean_dec_ref_known(v___x_2245_, 2);
lean_dec(v_response_2242_);
lean_dec(v_a_2194_);
lean_dec_ref(v_kind_2183_);
lean_dec_ref(v_params_2181_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v___x_2246_);
v___x_2250_ = v___x_2210_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2246_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
else
{
lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_del_object(v___x_2210_);
v___x_2252_ = l_Array_toSubarray___redArg(v_response_2242_, v___x_2199_, v___x_2247_);
v___x_2253_ = lean_box(v___x_2200_);
v___x_2254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
lean_ctor_set(v___x_2254_, 1, v___x_2252_);
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2246_);
lean_ctor_set(v___x_2255_, 1, v___x_2254_);
lean_inc_ref(v_params_2181_);
lean_inc_ref(v_doc_2186_);
v___x_2256_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_2183_, v_doc_2186_, v_params_2181_, v___x_2245_, v___x_2198_, v_a_2194_, v_sz_2202_, v___x_2203_, v___x_2255_, v_a_2184_);
lean_dec(v_a_2194_);
if (lean_obj_tag(v___x_2256_) == 0)
{
lean_object* v_a_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2275_; 
v_a_2257_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2259_ = v___x_2256_;
v_isShared_2260_ = v_isSharedCheck_2275_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_a_2257_);
lean_dec(v___x_2256_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2275_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_snd_2261_; lean_object* v_fst_2262_; uint8_t v___x_2263_; 
v_snd_2261_ = lean_ctor_get(v_a_2257_, 1);
v_fst_2262_ = lean_ctor_get(v_snd_2261_, 0);
v___x_2263_ = lean_unbox(v_fst_2262_);
if (v___x_2263_ == 0)
{
lean_object* v_fst_2264_; lean_object* v___x_2266_; 
lean_dec_ref(v_params_2181_);
v_fst_2264_ = lean_ctor_get(v_a_2257_, 0);
lean_inc(v_fst_2264_);
lean_dec(v_a_2257_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v_fst_2264_);
v___x_2266_ = v___x_2259_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_fst_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_object* v_fst_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2273_; 
v_fst_2268_ = lean_ctor_get(v_a_2257_, 0);
lean_inc(v_fst_2268_);
lean_dec(v_a_2257_);
v___x_2269_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4));
v___x_2270_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(v_params_2181_, v___x_2269_);
v___x_2271_ = lean_array_push(v_fst_2268_, v___x_2270_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 0, v___x_2271_);
v___x_2273_ = v___x_2259_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec_ref(v_params_2181_);
v_a_2276_ = lean_ctor_get(v___x_2256_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2256_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2256_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2256_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2241_);
lean_del_object(v___x_2210_);
lean_dec(v_a_2194_);
lean_dec_ref(v_kind_2183_);
lean_dec_ref(v_params_2181_);
v___y_2222_ = v_a_2184_;
goto v___jp_2221_;
}
}
else
{
lean_dec(v___x_2220_);
lean_del_object(v___x_2210_);
lean_dec(v_a_2194_);
lean_dec_ref(v_kind_2183_);
lean_dec_ref(v_params_2181_);
v___y_2222_ = v_a_2184_;
goto v___jp_2221_;
}
v___jp_2221_:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_Server_RequestM_checkCancelled(v___y_2222_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2231_; 
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2231_ == 0)
{
lean_object* v_unused_2232_; 
v_unused_2232_ = lean_ctor_get(v___x_2223_, 0);
lean_dec(v_unused_2232_);
v___x_2225_ = v___x_2223_;
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
else
{
lean_dec(v___x_2223_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2231_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2227_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3));
if (v_isShared_2226_ == 0)
{
lean_ctor_set(v___x_2225_, 0, v___x_2227_);
v___x_2229_ = v___x_2225_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
else
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2240_; 
v_a_2233_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2235_ = v___x_2223_;
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2223_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2240_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v___x_2238_; 
if (v_isShared_2236_ == 0)
{
v___x_2238_ = v___x_2235_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_a_2233_);
v___x_2238_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
return v___x_2238_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2307_; 
lean_dec(v_a_2194_);
lean_del_object(v___x_2191_);
lean_dec_ref(v_kind_2183_);
lean_dec_ref(v_params_2181_);
lean_dec(v_id_2180_);
v___x_2305_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3));
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 0, v___x_2305_);
v___x_2307_ = v___x_2196_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_del_object(v___x_2191_);
lean_dec_ref(v_kind_2183_);
lean_dec_ref(v_params_2181_);
lean_dec(v_id_2180_);
v_a_2310_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2193_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2193_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___boxed(lean_object* v_id_2320_, lean_object* v_params_2321_, lean_object* v_requestedRange_2322_, lean_object* v_kind_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(v_id_2320_, v_params_2321_, v_requestedRange_2322_, v_kind_2323_, v_a_2324_);
lean_dec_ref(v_a_2324_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(lean_object* v_a_2327_, lean_object* v_kind_2328_, lean_object* v___x_2329_, lean_object* v_params_2330_, lean_object* v___x_2331_, lean_object* v___x_2332_, lean_object* v_as_2333_, size_t v_sz_2334_, size_t v_i_2335_, lean_object* v_b_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_2327_, v_kind_2328_, v___x_2329_, v_params_2330_, v___x_2331_, v___x_2332_, v_as_2333_, v_sz_2334_, v_i_2335_, v_b_2336_);
return v___x_2339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(lean_object* v_a_2340_, lean_object* v_kind_2341_, lean_object* v___x_2342_, lean_object* v_params_2343_, lean_object* v___x_2344_, lean_object* v___x_2345_, lean_object* v_as_2346_, lean_object* v_sz_2347_, lean_object* v_i_2348_, lean_object* v_b_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2347_);
lean_dec(v_sz_2347_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2348_);
lean_dec(v_i_2348_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(v_a_2340_, v_kind_2341_, v___x_2342_, v_params_2343_, v___x_2344_, v___x_2345_, v_as_2346_, v_sz_boxed_2352_, v_i_boxed_2353_, v_b_2349_, v___y_2350_);
lean_dec_ref(v___y_2350_);
lean_dec_ref(v_as_2346_);
lean_dec(v___x_2345_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(lean_object* v_a_2358_, lean_object* v_as_2359_, size_t v_sz_2360_, size_t v_i_2361_, lean_object* v_b_2362_){
_start:
{
lean_object* v_a_2364_; uint8_t v___x_2368_; 
v___x_2368_ = lean_usize_dec_lt(v_i_2361_, v_sz_2360_);
if (v___x_2368_ == 0)
{
lean_dec_ref(v_a_2358_);
lean_inc_ref(v_b_2362_);
return v_b_2362_;
}
else
{
lean_object* v_a_2369_; lean_object* v_decl_2370_; uint8_t v_isExactMatch_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_a_2369_ = lean_array_uget_borrowed(v_as_2359_, v_i_2361_);
v_decl_2370_ = lean_ctor_get(v_a_2369_, 1);
v_isExactMatch_2371_ = lean_ctor_get_uint8(v_a_2369_, sizeof(void*)*2);
v___x_2372_ = lean_box(0);
v___x_2373_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0));
if (v_isExactMatch_2371_ == 0)
{
v_a_2364_ = v___x_2373_;
goto v___jp_2363_;
}
else
{
lean_object* v_ctx_2374_; lean_object* v_toCommandContextInfo_2375_; lean_object* v_env_2376_; uint8_t v___x_2377_; 
v_ctx_2374_ = lean_ctor_get(v_a_2358_, 1);
v_toCommandContextInfo_2375_ = lean_ctor_get(v_ctx_2374_, 0);
v_env_2376_ = lean_ctor_get(v_toCommandContextInfo_2375_, 0);
lean_inc(v_decl_2370_);
lean_inc_ref(v_env_2376_);
v___x_2377_ = l_Lean_Environment_contains(v_env_2376_, v_decl_2370_, v_isExactMatch_2371_);
if (v___x_2377_ == 0)
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; 
lean_dec_ref(v_a_2358_);
lean_inc(v_a_2369_);
v___x_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2378_, 0, v_a_2369_);
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v___x_2372_);
return v___x_2380_;
}
else
{
v_a_2364_ = v___x_2373_;
goto v___jp_2363_;
}
}
}
v___jp_2363_:
{
size_t v___x_2365_; size_t v___x_2366_; 
v___x_2365_ = ((size_t)1ULL);
v___x_2366_ = lean_usize_add(v_i_2361_, v___x_2365_);
v_i_2361_ = v___x_2366_;
v_b_2362_ = v_a_2364_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___boxed(lean_object* v_a_2381_, lean_object* v_as_2382_, lean_object* v_sz_2383_, lean_object* v_i_2384_, lean_object* v_b_2385_){
_start:
{
size_t v_sz_boxed_2386_; size_t v_i_boxed_2387_; lean_object* v_res_2388_; 
v_sz_boxed_2386_ = lean_unbox_usize(v_sz_2383_);
lean_dec(v_sz_2383_);
v_i_boxed_2387_ = lean_unbox_usize(v_i_2384_);
lean_dec(v_i_2384_);
v_res_2388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_2381_, v_as_2382_, v_sz_boxed_2386_, v_i_boxed_2387_, v_b_2385_);
lean_dec_ref(v_b_2385_);
lean_dec_ref(v_as_2382_);
return v_res_2388_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(lean_object* v_a_2389_, lean_object* v_x_2390_){
_start:
{
if (lean_obj_tag(v_x_2390_) == 0)
{
uint8_t v___x_2391_; 
v___x_2391_ = 0;
return v___x_2391_;
}
else
{
lean_object* v_key_2392_; lean_object* v_tail_2393_; uint8_t v___x_2394_; 
v_key_2392_ = lean_ctor_get(v_x_2390_, 0);
v_tail_2393_ = lean_ctor_get(v_x_2390_, 2);
v___x_2394_ = lean_name_eq(v_key_2392_, v_a_2389_);
if (v___x_2394_ == 0)
{
v_x_2390_ = v_tail_2393_;
goto _start;
}
else
{
return v___x_2394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_a_2396_, lean_object* v_x_2397_){
_start:
{
uint8_t v_res_2398_; lean_object* v_r_2399_; 
v_res_2398_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2396_, v_x_2397_);
lean_dec(v_x_2397_);
lean_dec(v_a_2396_);
v_r_2399_ = lean_box(v_res_2398_);
return v_r_2399_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2400_; uint64_t v___x_2401_; 
v___x_2400_ = lean_unsigned_to_nat(1723u);
v___x_2401_ = lean_uint64_of_nat(v___x_2400_);
return v___x_2401_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(lean_object* v_m_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_buckets_2404_; lean_object* v___x_2405_; uint64_t v___y_2407_; 
v_buckets_2404_ = lean_ctor_get(v_m_2402_, 1);
v___x_2405_ = lean_array_get_size(v_buckets_2404_);
if (lean_obj_tag(v_a_2403_) == 0)
{
uint64_t v___x_2421_; 
v___x_2421_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
v___y_2407_ = v___x_2421_;
goto v___jp_2406_;
}
else
{
uint64_t v_hash_2422_; 
v_hash_2422_ = lean_ctor_get_uint64(v_a_2403_, sizeof(void*)*2);
v___y_2407_ = v_hash_2422_;
goto v___jp_2406_;
}
v___jp_2406_:
{
uint64_t v___x_2408_; uint64_t v___x_2409_; uint64_t v_fold_2410_; uint64_t v___x_2411_; uint64_t v___x_2412_; uint64_t v___x_2413_; size_t v___x_2414_; size_t v___x_2415_; size_t v___x_2416_; size_t v___x_2417_; size_t v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; 
v___x_2408_ = 32ULL;
v___x_2409_ = lean_uint64_shift_right(v___y_2407_, v___x_2408_);
v_fold_2410_ = lean_uint64_xor(v___y_2407_, v___x_2409_);
v___x_2411_ = 16ULL;
v___x_2412_ = lean_uint64_shift_right(v_fold_2410_, v___x_2411_);
v___x_2413_ = lean_uint64_xor(v_fold_2410_, v___x_2412_);
v___x_2414_ = lean_uint64_to_usize(v___x_2413_);
v___x_2415_ = lean_usize_of_nat(v___x_2405_);
v___x_2416_ = ((size_t)1ULL);
v___x_2417_ = lean_usize_sub(v___x_2415_, v___x_2416_);
v___x_2418_ = lean_usize_land(v___x_2414_, v___x_2417_);
v___x_2419_ = lean_array_uget_borrowed(v_buckets_2404_, v___x_2418_);
v___x_2420_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2403_, v___x_2419_);
return v___x_2420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___boxed(lean_object* v_m_2423_, lean_object* v_a_2424_){
_start:
{
uint8_t v_res_2425_; lean_object* v_r_2426_; 
v_res_2425_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_2423_, v_a_2424_);
lean_dec(v_a_2424_);
lean_dec_ref(v_m_2423_);
v_r_2426_ = lean_box(v_res_2425_);
return v_r_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2427_, lean_object* v_x_2428_){
_start:
{
if (lean_obj_tag(v_x_2428_) == 0)
{
return v_x_2427_;
}
else
{
lean_object* v_key_2429_; lean_object* v_value_2430_; lean_object* v_tail_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2457_; 
v_key_2429_ = lean_ctor_get(v_x_2428_, 0);
v_value_2430_ = lean_ctor_get(v_x_2428_, 1);
v_tail_2431_ = lean_ctor_get(v_x_2428_, 2);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_x_2428_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2433_ = v_x_2428_;
v_isShared_2434_ = v_isSharedCheck_2457_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_tail_2431_);
lean_inc(v_value_2430_);
lean_inc(v_key_2429_);
lean_dec(v_x_2428_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2457_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___x_2435_; uint64_t v___y_2437_; 
v___x_2435_ = lean_array_get_size(v_x_2427_);
if (lean_obj_tag(v_key_2429_) == 0)
{
uint64_t v___x_2455_; 
v___x_2455_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
v___y_2437_ = v___x_2455_;
goto v___jp_2436_;
}
else
{
uint64_t v_hash_2456_; 
v_hash_2456_ = lean_ctor_get_uint64(v_key_2429_, sizeof(void*)*2);
v___y_2437_ = v_hash_2456_;
goto v___jp_2436_;
}
v___jp_2436_:
{
uint64_t v___x_2438_; uint64_t v___x_2439_; uint64_t v_fold_2440_; uint64_t v___x_2441_; uint64_t v___x_2442_; uint64_t v___x_2443_; size_t v___x_2444_; size_t v___x_2445_; size_t v___x_2446_; size_t v___x_2447_; size_t v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2438_ = 32ULL;
v___x_2439_ = lean_uint64_shift_right(v___y_2437_, v___x_2438_);
v_fold_2440_ = lean_uint64_xor(v___y_2437_, v___x_2439_);
v___x_2441_ = 16ULL;
v___x_2442_ = lean_uint64_shift_right(v_fold_2440_, v___x_2441_);
v___x_2443_ = lean_uint64_xor(v_fold_2440_, v___x_2442_);
v___x_2444_ = lean_uint64_to_usize(v___x_2443_);
v___x_2445_ = lean_usize_of_nat(v___x_2435_);
v___x_2446_ = ((size_t)1ULL);
v___x_2447_ = lean_usize_sub(v___x_2445_, v___x_2446_);
v___x_2448_ = lean_usize_land(v___x_2444_, v___x_2447_);
v___x_2449_ = lean_array_uget_borrowed(v_x_2427_, v___x_2448_);
lean_inc(v___x_2449_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 2, v___x_2449_);
v___x_2451_ = v___x_2433_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_key_2429_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_value_2430_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v___x_2449_);
v___x_2451_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2452_; 
v___x_2452_ = lean_array_uset(v_x_2427_, v___x_2448_, v___x_2451_);
v_x_2427_ = v___x_2452_;
v_x_2428_ = v_tail_2431_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2458_, lean_object* v_source_2459_, lean_object* v_target_2460_){
_start:
{
lean_object* v___x_2461_; uint8_t v___x_2462_; 
v___x_2461_ = lean_array_get_size(v_source_2459_);
v___x_2462_ = lean_nat_dec_lt(v_i_2458_, v___x_2461_);
if (v___x_2462_ == 0)
{
lean_dec_ref(v_source_2459_);
lean_dec(v_i_2458_);
return v_target_2460_;
}
else
{
lean_object* v_es_2463_; lean_object* v___x_2464_; lean_object* v_source_2465_; lean_object* v_target_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; 
v_es_2463_ = lean_array_fget(v_source_2459_, v_i_2458_);
v___x_2464_ = lean_box(0);
v_source_2465_ = lean_array_fset(v_source_2459_, v_i_2458_, v___x_2464_);
v_target_2466_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_target_2460_, v_es_2463_);
v___x_2467_ = lean_unsigned_to_nat(1u);
v___x_2468_ = lean_nat_add(v_i_2458_, v___x_2467_);
lean_dec(v_i_2458_);
v_i_2458_ = v___x_2468_;
v_source_2459_ = v_source_2465_;
v_target_2460_ = v_target_2466_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(lean_object* v_data_2470_){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v_nbuckets_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2471_ = lean_array_get_size(v_data_2470_);
v___x_2472_ = lean_unsigned_to_nat(2u);
v_nbuckets_2473_ = lean_nat_mul(v___x_2471_, v___x_2472_);
v___x_2474_ = lean_unsigned_to_nat(0u);
v___x_2475_ = lean_box(0);
v___x_2476_ = lean_mk_array(v_nbuckets_2473_, v___x_2475_);
v___x_2477_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v___x_2474_, v_data_2470_, v___x_2476_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(lean_object* v_m_2478_, lean_object* v_a_2479_, lean_object* v_b_2480_){
_start:
{
lean_object* v_size_2481_; lean_object* v_buckets_2482_; lean_object* v___x_2483_; uint64_t v___y_2485_; 
v_size_2481_ = lean_ctor_get(v_m_2478_, 0);
v_buckets_2482_ = lean_ctor_get(v_m_2478_, 1);
v___x_2483_ = lean_array_get_size(v_buckets_2482_);
if (lean_obj_tag(v_a_2479_) == 0)
{
uint64_t v___x_2522_; 
v___x_2522_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
v___y_2485_ = v___x_2522_;
goto v___jp_2484_;
}
else
{
uint64_t v_hash_2523_; 
v_hash_2523_ = lean_ctor_get_uint64(v_a_2479_, sizeof(void*)*2);
v___y_2485_ = v_hash_2523_;
goto v___jp_2484_;
}
v___jp_2484_:
{
uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v_fold_2488_; uint64_t v___x_2489_; uint64_t v___x_2490_; uint64_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; size_t v___x_2494_; size_t v___x_2495_; size_t v___x_2496_; lean_object* v_bkt_2497_; uint8_t v___x_2498_; 
v___x_2486_ = 32ULL;
v___x_2487_ = lean_uint64_shift_right(v___y_2485_, v___x_2486_);
v_fold_2488_ = lean_uint64_xor(v___y_2485_, v___x_2487_);
v___x_2489_ = 16ULL;
v___x_2490_ = lean_uint64_shift_right(v_fold_2488_, v___x_2489_);
v___x_2491_ = lean_uint64_xor(v_fold_2488_, v___x_2490_);
v___x_2492_ = lean_uint64_to_usize(v___x_2491_);
v___x_2493_ = lean_usize_of_nat(v___x_2483_);
v___x_2494_ = ((size_t)1ULL);
v___x_2495_ = lean_usize_sub(v___x_2493_, v___x_2494_);
v___x_2496_ = lean_usize_land(v___x_2492_, v___x_2495_);
v_bkt_2497_ = lean_array_uget_borrowed(v_buckets_2482_, v___x_2496_);
v___x_2498_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2479_, v_bkt_2497_);
if (v___x_2498_ == 0)
{
lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2519_; 
lean_inc_ref(v_buckets_2482_);
lean_inc(v_size_2481_);
v_isSharedCheck_2519_ = !lean_is_exclusive(v_m_2478_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; lean_object* v_unused_2521_; 
v_unused_2520_ = lean_ctor_get(v_m_2478_, 1);
lean_dec(v_unused_2520_);
v_unused_2521_ = lean_ctor_get(v_m_2478_, 0);
lean_dec(v_unused_2521_);
v___x_2500_ = v_m_2478_;
v_isShared_2501_ = v_isSharedCheck_2519_;
goto v_resetjp_2499_;
}
else
{
lean_dec(v_m_2478_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2519_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2502_; lean_object* v_size_x27_2503_; lean_object* v___x_2504_; lean_object* v_buckets_x27_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___x_2511_; 
v___x_2502_ = lean_unsigned_to_nat(1u);
v_size_x27_2503_ = lean_nat_add(v_size_2481_, v___x_2502_);
lean_dec(v_size_2481_);
lean_inc(v_bkt_2497_);
v___x_2504_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2504_, 0, v_a_2479_);
lean_ctor_set(v___x_2504_, 1, v_b_2480_);
lean_ctor_set(v___x_2504_, 2, v_bkt_2497_);
v_buckets_x27_2505_ = lean_array_uset(v_buckets_2482_, v___x_2496_, v___x_2504_);
v___x_2506_ = lean_unsigned_to_nat(4u);
v___x_2507_ = lean_nat_mul(v_size_x27_2503_, v___x_2506_);
v___x_2508_ = lean_unsigned_to_nat(3u);
v___x_2509_ = lean_nat_div(v___x_2507_, v___x_2508_);
lean_dec(v___x_2507_);
v___x_2510_ = lean_array_get_size(v_buckets_x27_2505_);
v___x_2511_ = lean_nat_dec_le(v___x_2509_, v___x_2510_);
lean_dec(v___x_2509_);
if (v___x_2511_ == 0)
{
lean_object* v_val_2512_; lean_object* v___x_2514_; 
v_val_2512_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_buckets_x27_2505_);
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v_val_2512_);
lean_ctor_set(v___x_2500_, 0, v_size_x27_2503_);
v___x_2514_ = v___x_2500_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_size_x27_2503_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_val_2512_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
else
{
lean_object* v___x_2517_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set(v___x_2500_, 1, v_buckets_x27_2505_);
lean_ctor_set(v___x_2500_, 0, v_size_x27_2503_);
v___x_2517_ = v___x_2500_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_size_x27_2503_);
lean_ctor_set(v_reuseFailAlloc_2518_, 1, v_buckets_x27_2505_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
else
{
lean_dec(v_b_2480_);
lean_dec(v_a_2479_);
return v_m_2478_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(lean_object* v___x_2524_, lean_object* v_as_2525_, size_t v_sz_2526_, size_t v_i_2527_, lean_object* v_b_2528_){
_start:
{
lean_object* v_a_2531_; uint8_t v___x_2535_; 
v___x_2535_ = lean_usize_dec_lt(v_i_2527_, v_sz_2526_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; 
lean_dec_ref(v___x_2524_);
v___x_2536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2536_, 0, v_b_2528_);
return v___x_2536_;
}
else
{
lean_object* v_snd_2537_; lean_object* v_snd_2538_; lean_object* v_fst_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2629_; 
v_snd_2537_ = lean_ctor_get(v_b_2528_, 1);
lean_inc(v_snd_2537_);
v_snd_2538_ = lean_ctor_get(v_snd_2537_, 1);
lean_inc(v_snd_2538_);
v_fst_2539_ = lean_ctor_get(v_b_2528_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v_b_2528_);
if (v_isSharedCheck_2629_ == 0)
{
lean_object* v_unused_2630_; 
v_unused_2630_ = lean_ctor_get(v_b_2528_, 1);
lean_dec(v_unused_2630_);
v___x_2541_ = v_b_2528_;
v_isShared_2542_ = v_isSharedCheck_2629_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_fst_2539_);
lean_dec(v_b_2528_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2629_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v_fst_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2627_; 
v_fst_2543_ = lean_ctor_get(v_snd_2537_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v_snd_2537_);
if (v_isSharedCheck_2627_ == 0)
{
lean_object* v_unused_2628_; 
v_unused_2628_ = lean_ctor_get(v_snd_2537_, 1);
lean_dec(v_unused_2628_);
v___x_2545_ = v_snd_2537_;
v_isShared_2546_ = v_isSharedCheck_2627_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_fst_2543_);
lean_dec(v_snd_2537_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2627_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v_array_2547_; lean_object* v_start_2548_; lean_object* v_stop_2549_; uint8_t v___x_2550_; 
v_array_2547_ = lean_ctor_get(v_snd_2538_, 0);
v_start_2548_ = lean_ctor_get(v_snd_2538_, 1);
v_stop_2549_ = lean_ctor_get(v_snd_2538_, 2);
v___x_2550_ = lean_nat_dec_lt(v_start_2548_, v_stop_2549_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2552_; 
lean_dec_ref(v___x_2524_);
if (v_isShared_2546_ == 0)
{
v___x_2552_ = v___x_2545_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_fst_2543_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v_snd_2538_);
v___x_2552_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
lean_object* v___x_2554_; 
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 1, v___x_2552_);
v___x_2554_ = v___x_2541_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_fst_2539_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2552_);
v___x_2554_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2555_; 
v___x_2555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2555_, 0, v___x_2554_);
return v___x_2555_;
}
}
}
else
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2623_; 
lean_inc(v_stop_2549_);
lean_inc(v_start_2548_);
lean_inc_ref(v_array_2547_);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_snd_2538_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; lean_object* v_unused_2625_; lean_object* v_unused_2626_; 
v_unused_2624_ = lean_ctor_get(v_snd_2538_, 2);
lean_dec(v_unused_2624_);
v_unused_2625_ = lean_ctor_get(v_snd_2538_, 1);
lean_dec(v_unused_2625_);
v_unused_2626_ = lean_ctor_get(v_snd_2538_, 0);
lean_dec(v_unused_2626_);
v___x_2559_ = v_snd_2538_;
v_isShared_2560_ = v_isSharedCheck_2623_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v_snd_2538_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2623_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v_a_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; size_t v_sz_2566_; size_t v___x_2567_; lean_object* v___x_2568_; lean_object* v_fst_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2621_; 
v_a_2561_ = lean_array_uget_borrowed(v_as_2525_, v_i_2527_);
v___x_2562_ = lean_array_fget_borrowed(v_array_2547_, v_start_2548_);
v___x_2563_ = lean_box(0);
v___x_2564_ = lean_box(0);
v___x_2565_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0));
v_sz_2566_ = lean_array_size(v___x_2562_);
v___x_2567_ = ((size_t)0ULL);
lean_inc(v_a_2561_);
v___x_2568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_2561_, v___x_2562_, v_sz_2566_, v___x_2567_, v___x_2565_);
v_fst_2569_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2621_ == 0)
{
lean_object* v_unused_2622_; 
v_unused_2622_ = lean_ctor_get(v___x_2568_, 1);
lean_dec(v_unused_2622_);
v___x_2571_ = v___x_2568_;
v_isShared_2572_ = v_isSharedCheck_2621_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_fst_2569_);
lean_dec(v___x_2568_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2621_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2576_; 
v___x_2573_ = lean_unsigned_to_nat(1u);
v___x_2574_ = lean_nat_add(v_start_2548_, v___x_2573_);
lean_dec(v_start_2548_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 1, v___x_2574_);
v___x_2576_ = v___x_2559_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_array_2547_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2574_);
lean_ctor_set(v_reuseFailAlloc_2620_, 2, v_stop_2549_);
v___x_2576_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
if (lean_obj_tag(v_fst_2569_) == 0)
{
lean_del_object(v___x_2541_);
goto v___jp_2577_;
}
else
{
lean_object* v_val_2584_; 
v_val_2584_ = lean_ctor_get(v_fst_2569_, 0);
lean_inc(v_val_2584_);
lean_dec_ref_known(v_fst_2569_, 1);
if (lean_obj_tag(v_val_2584_) == 1)
{
lean_object* v_val_2585_; lean_object* v_ctx_2586_; lean_object* v_toCommandContextInfo_2587_; lean_object* v_module_2588_; lean_object* v_decl_2589_; lean_object* v_determineInsertion_2590_; lean_object* v_env_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
lean_del_object(v___x_2571_);
lean_del_object(v___x_2545_);
v_val_2585_ = lean_ctor_get(v_val_2584_, 0);
lean_inc(v_val_2585_);
lean_dec_ref_known(v_val_2584_, 1);
v_ctx_2586_ = lean_ctor_get(v_a_2561_, 1);
v_toCommandContextInfo_2587_ = lean_ctor_get(v_ctx_2586_, 0);
v_module_2588_ = lean_ctor_get(v_val_2585_, 0);
lean_inc(v_module_2588_);
v_decl_2589_ = lean_ctor_get(v_val_2585_, 1);
lean_inc(v_decl_2589_);
lean_dec(v_val_2585_);
v_determineInsertion_2590_ = lean_ctor_get(v_a_2561_, 2);
v_env_2591_ = lean_ctor_get(v_toCommandContextInfo_2587_, 0);
v___x_2592_ = l_Lean_Environment_mainModule(v_env_2591_);
v___x_2593_ = lean_name_eq(v_module_2588_, v___x_2592_);
lean_dec(v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; lean_object* v_edits_2596_; uint8_t v___x_2615_; 
lean_inc_ref(v_determineInsertion_2590_);
v___x_2594_ = lean_apply_1(v_determineInsertion_2590_, v_decl_2589_);
v___x_2615_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_fst_2543_, v_module_2588_);
if (v___x_2615_ == 0)
{
goto v___jp_2611_;
}
else
{
if (v___x_2593_ == 0)
{
v_edits_2596_ = v_fst_2539_;
goto v___jp_2595_;
}
else
{
goto v___jp_2611_;
}
}
v___jp_2595_:
{
lean_object* v_edit_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2609_; 
v_edit_2597_ = lean_ctor_get(v___x_2594_, 1);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2594_);
if (v_isSharedCheck_2609_ == 0)
{
lean_object* v_unused_2610_; 
v_unused_2610_ = lean_ctor_get(v___x_2594_, 0);
lean_dec(v_unused_2610_);
v___x_2599_ = v___x_2594_;
v_isShared_2600_ = v_isSharedCheck_2609_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_edit_2597_);
lean_dec(v___x_2594_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2609_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v___x_2601_ = lean_array_push(v_edits_2596_, v_edit_2597_);
v___x_2602_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_fst_2543_, v_module_2588_, v___x_2564_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 1, v___x_2576_);
lean_ctor_set(v___x_2541_, 0, v___x_2602_);
v___x_2604_ = v___x_2541_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2608_, 1, v___x_2576_);
v___x_2604_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2606_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 1, v___x_2604_);
lean_ctor_set(v___x_2599_, 0, v___x_2601_);
v___x_2606_ = v___x_2599_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2607_, 1, v___x_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
v_a_2531_ = v___x_2606_;
goto v___jp_2530_;
}
}
}
}
v___jp_2611_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_inc(v_module_2588_);
lean_inc_ref(v_ctx_2586_);
v___x_2612_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_2586_, v_module_2588_);
lean_inc_ref(v___x_2524_);
v___x_2613_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2524_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
lean_ctor_set(v___x_2613_, 2, v___x_2563_);
lean_ctor_set(v___x_2613_, 3, v___x_2563_);
v___x_2614_ = lean_array_push(v_fst_2539_, v___x_2613_);
v_edits_2596_ = v___x_2614_;
goto v___jp_2595_;
}
}
else
{
lean_object* v___x_2617_; 
lean_dec(v_decl_2589_);
lean_dec(v_module_2588_);
if (v_isShared_2542_ == 0)
{
lean_ctor_set(v___x_2541_, 1, v___x_2576_);
lean_ctor_set(v___x_2541_, 0, v_fst_2543_);
v___x_2617_ = v___x_2541_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_fst_2543_);
lean_ctor_set(v_reuseFailAlloc_2619_, 1, v___x_2576_);
v___x_2617_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v_fst_2539_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v_a_2531_ = v___x_2618_;
goto v___jp_2530_;
}
}
}
else
{
lean_dec(v_val_2584_);
lean_del_object(v___x_2541_);
goto v___jp_2577_;
}
}
v___jp_2577_:
{
lean_object* v___x_2579_; 
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 1, v___x_2576_);
lean_ctor_set(v___x_2571_, 0, v_fst_2543_);
v___x_2579_ = v___x_2571_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_fst_2543_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v___x_2576_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2546_ == 0)
{
lean_ctor_set(v___x_2545_, 1, v___x_2579_);
lean_ctor_set(v___x_2545_, 0, v_fst_2539_);
v___x_2581_ = v___x_2545_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_fst_2539_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
v_a_2531_ = v___x_2581_;
goto v___jp_2530_;
}
}
}
}
}
}
}
}
}
}
v___jp_2530_:
{
size_t v___x_2532_; size_t v___x_2533_; 
v___x_2532_ = ((size_t)1ULL);
v___x_2533_ = lean_usize_add(v_i_2527_, v___x_2532_);
v_i_2527_ = v___x_2533_;
v_b_2528_ = v_a_2531_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg___boxed(lean_object* v___x_2631_, lean_object* v_as_2632_, lean_object* v_sz_2633_, lean_object* v_i_2634_, lean_object* v_b_2635_, lean_object* v___y_2636_){
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2633_);
lean_dec(v_sz_2633_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2634_);
lean_dec(v_i_2634_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_2631_, v_as_2632_, v_sz_boxed_2637_, v_i_boxed_2638_, v_b_2635_);
lean_dec_ref(v_as_2632_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(lean_object* v___x_2640_, lean_object* v_as_2641_, size_t v_i_2642_, size_t v_stop_2643_, lean_object* v_b_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_a_2648_; uint8_t v___x_2652_; 
v___x_2652_ = lean_usize_dec_eq(v_i_2642_, v_stop_2643_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v_stop_2654_; lean_object* v___x_2655_; 
v___x_2653_ = lean_array_uget_borrowed(v_as_2641_, v_i_2642_);
v_stop_2654_ = lean_ctor_get(v___x_2653_, 1);
lean_inc(v_stop_2654_);
lean_inc_ref(v___x_2640_);
v___x_2655_ = l_Lean_Server_FileWorker_computeQueries(v___x_2640_, v_stop_2654_, v___y_2645_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2657_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = l_Array_append___redArg(v_b_2644_, v_a_2656_);
lean_dec(v_a_2656_);
v_a_2648_ = v___x_2657_;
goto v___jp_2647_;
}
else
{
lean_dec_ref(v_b_2644_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2658_; 
v_a_2658_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2655_, 1);
v_a_2648_ = v_a_2658_;
goto v___jp_2647_;
}
else
{
lean_dec_ref(v___x_2640_);
return v___x_2655_;
}
}
}
else
{
lean_object* v___x_2659_; 
lean_dec_ref(v___x_2640_);
v___x_2659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2659_, 0, v_b_2644_);
return v___x_2659_;
}
v___jp_2647_:
{
size_t v___x_2649_; size_t v___x_2650_; 
v___x_2649_ = ((size_t)1ULL);
v___x_2650_ = lean_usize_add(v_i_2642_, v___x_2649_);
v_i_2642_ = v___x_2650_;
v_b_2644_ = v_a_2648_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4___boxed(lean_object* v___x_2660_, lean_object* v_as_2661_, lean_object* v_i_2662_, lean_object* v_stop_2663_, lean_object* v_b_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
size_t v_i_boxed_2667_; size_t v_stop_boxed_2668_; lean_object* v_res_2669_; 
v_i_boxed_2667_ = lean_unbox_usize(v_i_2662_);
lean_dec(v_i_2662_);
v_stop_boxed_2668_ = lean_unbox_usize(v_stop_2663_);
lean_dec(v_stop_2663_);
v_res_2669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v___x_2660_, v_as_2661_, v_i_boxed_2667_, v_stop_boxed_2668_, v_b_2664_, v___y_2665_);
lean_dec_ref(v___y_2665_);
lean_dec_ref(v_as_2661_);
return v_res_2669_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0(void){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = lean_box(0);
v___x_2671_ = lean_unsigned_to_nat(16u);
v___x_2672_ = lean_mk_array(v___x_2671_, v___x_2670_);
return v___x_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object* v_id_2675_, lean_object* v_action_2676_, lean_object* v_unknownIdentifierRanges_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_doc_2680_; size_t v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; size_t v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2687_; lean_object* v_toEditableDocumentCore_2743_; lean_object* v_meta_2744_; lean_object* v_initSnap_2745_; lean_object* v_text_2746_; lean_object* v_a_2748_; lean_object* v___y_2788_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v_doc_2680_ = lean_ctor_get(v_a_2678_, 1);
v_toEditableDocumentCore_2743_ = lean_ctor_get(v_doc_2680_, 0);
v_meta_2744_ = lean_ctor_get(v_toEditableDocumentCore_2743_, 0);
v_initSnap_2745_ = lean_ctor_get(v_toEditableDocumentCore_2743_, 1);
v_text_2746_ = lean_ctor_get(v_meta_2744_, 3);
v___x_2798_ = lean_unsigned_to_nat(0u);
v___x_2799_ = ((lean_object*)(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1));
v___x_2800_ = lean_array_get_size(v_unknownIdentifierRanges_2677_);
v___x_2801_ = lean_nat_dec_lt(v___x_2798_, v___x_2800_);
if (v___x_2801_ == 0)
{
v_a_2748_ = v___x_2799_;
goto v___jp_2747_;
}
else
{
uint8_t v___x_2802_; 
v___x_2802_ = lean_nat_dec_le(v___x_2800_, v___x_2800_);
if (v___x_2802_ == 0)
{
if (v___x_2801_ == 0)
{
v_a_2748_ = v___x_2799_;
goto v___jp_2747_;
}
else
{
size_t v___x_2803_; size_t v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = ((size_t)0ULL);
v___x_2804_ = lean_usize_of_nat(v___x_2800_);
lean_inc_ref(v_doc_2680_);
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_2680_, v_unknownIdentifierRanges_2677_, v___x_2803_, v___x_2804_, v___x_2799_, v_a_2678_);
v___y_2788_ = v___x_2805_;
goto v___jp_2787_;
}
}
else
{
size_t v___x_2806_; size_t v___x_2807_; lean_object* v___x_2808_; 
v___x_2806_ = ((size_t)0ULL);
v___x_2807_ = lean_usize_of_nat(v___x_2800_);
lean_inc_ref(v_doc_2680_);
v___x_2808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_2680_, v_unknownIdentifierRanges_2677_, v___x_2806_, v___x_2807_, v___x_2799_, v_a_2678_);
v___y_2788_ = v___x_2808_;
goto v___jp_2787_;
}
}
v___jp_2681_:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_inc_ref(v___y_2687_);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___y_2687_);
lean_ctor_set(v___x_2688_, 1, v___y_2687_);
v___x_2689_ = lean_mk_empty_array_with_capacity(v___y_2683_);
v___x_2690_ = lean_obj_once(&l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0, &l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once, _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0);
lean_inc(v___y_2683_);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___y_2683_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_array_get_size(v___y_2686_);
v___x_2693_ = l_Array_toSubarray___redArg(v___y_2686_, v___y_2683_, v___x_2692_);
v___x_2694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2691_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2689_);
lean_ctor_set(v___x_2695_, 1, v___x_2694_);
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_2688_, v___y_2684_, v___y_2682_, v___y_2685_, v___x_2695_);
lean_dec_ref(v___y_2684_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2734_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2734_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2734_ == 0)
{
v___x_2699_ = v___x_2696_;
v_isShared_2700_ = v_isSharedCheck_2734_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2696_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2734_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v_fst_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2732_; 
v_fst_2701_ = lean_ctor_get(v_a_2697_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v_a_2697_);
if (v_isSharedCheck_2732_ == 0)
{
lean_object* v_unused_2733_; 
v_unused_2733_ = lean_ctor_get(v_a_2697_, 1);
lean_dec(v_unused_2733_);
v___x_2703_ = v_a_2697_;
v_isShared_2704_ = v_isSharedCheck_2732_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_fst_2701_);
lean_dec(v_a_2697_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2732_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v_toWorkDoneProgressParams_2705_; lean_object* v_toPartialResultParams_2706_; lean_object* v_title_2707_; lean_object* v_kind_x3f_2708_; lean_object* v_diagnostics_x3f_2709_; lean_object* v_isPreferred_x3f_2710_; lean_object* v_disabled_x3f_2711_; lean_object* v_command_x3f_2712_; lean_object* v_data_x3f_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2730_; 
v_toWorkDoneProgressParams_2705_ = lean_ctor_get(v_action_2676_, 0);
v_toPartialResultParams_2706_ = lean_ctor_get(v_action_2676_, 1);
v_title_2707_ = lean_ctor_get(v_action_2676_, 2);
v_kind_x3f_2708_ = lean_ctor_get(v_action_2676_, 3);
v_diagnostics_x3f_2709_ = lean_ctor_get(v_action_2676_, 4);
v_isPreferred_x3f_2710_ = lean_ctor_get(v_action_2676_, 5);
v_disabled_x3f_2711_ = lean_ctor_get(v_action_2676_, 6);
v_command_x3f_2712_ = lean_ctor_get(v_action_2676_, 8);
v_data_x3f_2713_ = lean_ctor_get(v_action_2676_, 9);
v_isSharedCheck_2730_ = !lean_is_exclusive(v_action_2676_);
if (v_isSharedCheck_2730_ == 0)
{
lean_object* v_unused_2731_; 
v_unused_2731_ = lean_ctor_get(v_action_2676_, 7);
lean_dec(v_unused_2731_);
v___x_2715_ = v_action_2676_;
v_isShared_2716_ = v_isSharedCheck_2730_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_data_x3f_2713_);
lean_inc(v_command_x3f_2712_);
lean_inc(v_disabled_x3f_2711_);
lean_inc(v_isPreferred_x3f_2710_);
lean_inc(v_diagnostics_x3f_2709_);
lean_inc(v_kind_x3f_2708_);
lean_inc(v_title_2707_);
lean_inc(v_toPartialResultParams_2706_);
lean_inc(v_toWorkDoneProgressParams_2705_);
lean_dec(v_action_2676_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2730_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2717_; lean_object* v___x_2719_; 
lean_inc_ref(v_doc_2680_);
v___x_2717_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_doc_2680_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 1, v_fst_2701_);
lean_ctor_set(v___x_2703_, 0, v___x_2717_);
v___x_2719_ = v___x_2703_;
goto v_reusejp_2718_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v___x_2717_);
lean_ctor_set(v_reuseFailAlloc_2729_, 1, v_fst_2701_);
v___x_2719_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2718_;
}
v_reusejp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2720_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_2719_);
v___x_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 7, v___x_2721_);
v___x_2723_ = v___x_2715_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_toWorkDoneProgressParams_2705_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_toPartialResultParams_2706_);
lean_ctor_set(v_reuseFailAlloc_2728_, 2, v_title_2707_);
lean_ctor_set(v_reuseFailAlloc_2728_, 3, v_kind_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2728_, 4, v_diagnostics_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2728_, 5, v_isPreferred_x3f_2710_);
lean_ctor_set(v_reuseFailAlloc_2728_, 6, v_disabled_x3f_2711_);
lean_ctor_set(v_reuseFailAlloc_2728_, 7, v___x_2721_);
lean_ctor_set(v_reuseFailAlloc_2728_, 8, v_command_x3f_2712_);
lean_ctor_set(v_reuseFailAlloc_2728_, 9, v_data_x3f_2713_);
v___x_2723_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2723_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 0, v___x_2724_);
v___x_2726_ = v___x_2699_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2742_; 
lean_dec_ref(v_action_2676_);
v_a_2735_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2737_ = v___x_2696_;
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2696_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2742_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2740_; 
if (v_isShared_2738_ == 0)
{
v___x_2740_ = v___x_2737_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_a_2735_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
v___jp_2747_:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2749_ = lean_array_get_size(v_a_2748_);
v___x_2750_ = lean_unsigned_to_nat(0u);
v___x_2751_ = lean_nat_dec_eq(v___x_2749_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; size_t v_sz_2753_; size_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2784_; 
v___x_2752_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0));
v_sz_2753_ = lean_array_size(v_a_2748_);
v___x_2754_ = ((size_t)0ULL);
lean_inc_ref(v_a_2748_);
v___x_2755_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_2753_, v___x_2754_, v_a_2748_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_id_2675_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_2752_, v___x_2756_, v_a_2678_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2784_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2784_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_task_get_own(v_a_2758_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v_response_2763_; lean_object* v_stx_2764_; lean_object* v___x_2765_; 
lean_del_object(v___x_2760_);
v_response_2763_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_response_2763_);
lean_dec_ref_known(v___x_2762_, 1);
v_stx_2764_ = lean_ctor_get(v_initSnap_2745_, 3);
v___x_2765_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2764_, v___x_2751_);
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_object* v___x_2766_; 
v___x_2766_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5));
v___y_2682_ = v_sz_2753_;
v___y_2683_ = v___x_2750_;
v___y_2684_ = v_a_2748_;
v___y_2685_ = v___x_2754_;
v___y_2686_ = v_response_2763_;
v___y_2687_ = v___x_2766_;
goto v___jp_2681_;
}
else
{
lean_object* v_val_2767_; lean_object* v___x_2768_; lean_object* v_line_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2778_; 
v_val_2767_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_val_2767_);
lean_dec_ref_known(v___x_2765_, 1);
lean_inc_ref(v_text_2746_);
v___x_2768_ = l_Lean_FileMap_utf8PosToLspPos(v_text_2746_, v_val_2767_);
lean_dec(v_val_2767_);
v_line_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2778_ == 0)
{
lean_object* v_unused_2779_; 
v_unused_2779_ = lean_ctor_get(v___x_2768_, 1);
lean_dec(v_unused_2779_);
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2778_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_line_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2778_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2773_ = lean_unsigned_to_nat(1u);
v___x_2774_ = lean_nat_add(v_line_2769_, v___x_2773_);
lean_dec(v_line_2769_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 1, v___x_2750_);
lean_ctor_set(v___x_2771_, 0, v___x_2774_);
v___x_2776_ = v___x_2771_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2750_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
v___y_2682_ = v_sz_2753_;
v___y_2683_ = v___x_2750_;
v___y_2684_ = v_a_2748_;
v___y_2685_ = v___x_2754_;
v___y_2686_ = v_response_2763_;
v___y_2687_ = v___x_2776_;
goto v___jp_2681_;
}
}
}
}
else
{
lean_object* v___x_2780_; lean_object* v___x_2782_; 
lean_dec(v___x_2762_);
lean_dec_ref(v_a_2748_);
lean_dec_ref(v_action_2676_);
v___x_2780_ = lean_box(0);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2780_);
v___x_2782_ = v___x_2760_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2780_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
else
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
lean_dec_ref(v_a_2748_);
lean_dec_ref(v_action_2676_);
lean_dec(v_id_2675_);
v___x_2785_ = lean_box(0);
v___x_2786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2785_);
return v___x_2786_;
}
}
v___jp_2787_:
{
if (lean_obj_tag(v___y_2788_) == 0)
{
lean_object* v_a_2789_; 
v_a_2789_ = lean_ctor_get(v___y_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___y_2788_, 1);
v_a_2748_ = v_a_2789_;
goto v___jp_2747_;
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec_ref(v_action_2676_);
lean_dec(v_id_2675_);
v_a_2790_ = lean_ctor_get(v___y_2788_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___y_2788_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___y_2788_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___y_2788_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object* v_id_2809_, lean_object* v_action_2810_, lean_object* v_unknownIdentifierRanges_2811_, lean_object* v_a_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v_res_2814_; 
v_res_2814_ = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(v_id_2809_, v_action_2810_, v_unknownIdentifierRanges_2811_, v_a_2812_);
lean_dec_ref(v_a_2812_);
lean_dec_ref(v_unknownIdentifierRanges_2811_);
return v_res_2814_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(lean_object* v_00_u03b2_2815_, lean_object* v_m_2816_, lean_object* v_a_2817_, lean_object* v_b_2818_){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_m_2816_, v_a_2817_, v_b_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(lean_object* v_00_u03b2_2820_, lean_object* v_m_2821_, lean_object* v_a_2822_){
_start:
{
uint8_t v___x_2823_; 
v___x_2823_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_2821_, v_a_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___boxed(lean_object* v_00_u03b2_2824_, lean_object* v_m_2825_, lean_object* v_a_2826_){
_start:
{
uint8_t v_res_2827_; lean_object* v_r_2828_; 
v_res_2827_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(v_00_u03b2_2824_, v_m_2825_, v_a_2826_);
lean_dec(v_a_2826_);
lean_dec_ref(v_m_2825_);
v_r_2828_ = lean_box(v_res_2827_);
return v_r_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(lean_object* v___x_2829_, lean_object* v_as_2830_, size_t v_sz_2831_, size_t v_i_2832_, lean_object* v_b_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v___x_2836_; 
v___x_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_2829_, v_as_2830_, v_sz_2831_, v_i_2832_, v_b_2833_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(lean_object* v___x_2837_, lean_object* v_as_2838_, lean_object* v_sz_2839_, lean_object* v_i_2840_, lean_object* v_b_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
size_t v_sz_boxed_2844_; size_t v_i_boxed_2845_; lean_object* v_res_2846_; 
v_sz_boxed_2844_ = lean_unbox_usize(v_sz_2839_);
lean_dec(v_sz_2839_);
v_i_boxed_2845_ = lean_unbox_usize(v_i_2840_);
lean_dec(v_i_2840_);
v_res_2846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(v___x_2837_, v_as_2838_, v_sz_boxed_2844_, v_i_boxed_2845_, v_b_2841_, v___y_2842_);
lean_dec_ref(v___y_2842_);
lean_dec_ref(v_as_2838_);
return v_res_2846_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(lean_object* v_00_u03b2_2847_, lean_object* v_a_2848_, lean_object* v_x_2849_){
_start:
{
uint8_t v___x_2850_; 
v___x_2850_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2848_, v_x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2851_, lean_object* v_a_2852_, lean_object* v_x_2853_){
_start:
{
uint8_t v_res_2854_; lean_object* v_r_2855_; 
v_res_2854_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(v_00_u03b2_2851_, v_a_2852_, v_x_2853_);
lean_dec(v_x_2853_);
lean_dec(v_a_2852_);
v_r_2855_ = lean_box(v_res_2854_);
return v_r_2855_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2(lean_object* v_00_u03b2_2856_, lean_object* v_data_2857_){
_start:
{
lean_object* v___x_2858_; 
v___x_2858_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_data_2857_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2859_, lean_object* v_i_2860_, lean_object* v_source_2861_, lean_object* v_target_2862_){
_start:
{
lean_object* v___x_2863_; 
v___x_2863_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v_i_2860_, v_source_2861_, v_target_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_2864_, lean_object* v_x_2865_, lean_object* v_x_2866_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_x_2865_, v_x_2866_);
return v___x_2867_;
}
}
lean_object* runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_CodeActions_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_CodeActions_UnknownIdentifier(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_CodeActions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_CodeActions_UnknownIdentifier(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_Completion_CompletionInfoSelection(uint8_t builtin);
lean_object* initialize_Lean_Server_CodeActions_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_CodeActions_UnknownIdentifier(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_CodeActions_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_CodeActions_UnknownIdentifier(builtin);
}
#ifdef __cplusplus
}
#endif
