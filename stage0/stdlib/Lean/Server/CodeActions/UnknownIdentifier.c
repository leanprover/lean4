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
static const lean_array_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object*, lean_object*);
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
lean_dec_ref(v___x_363_);
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
lean_dec_ref(v_msgRange_413_);
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
lean_dec_ref(v_msgRange_460_);
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
lean_object* v_cs_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_497_; 
v_cs_482_ = lean_ctor_get(v_n_479_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v_n_479_);
if (v_isSharedCheck_497_ == 0)
{
v___x_484_ = v_n_479_;
v_isShared_485_ = v_isSharedCheck_497_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_cs_482_);
lean_dec(v_n_479_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_497_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_486_; lean_object* v___x_487_; size_t v_sz_488_; size_t v___x_489_; lean_object* v___x_490_; lean_object* v_fst_491_; 
v___x_486_ = lean_box(0);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
lean_ctor_set(v___x_487_, 1, v_b_480_);
v_sz_488_ = lean_array_size(v_cs_482_);
v___x_489_ = ((size_t)0ULL);
v___x_490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_476_, v_text_477_, v_requestedRange_478_, v_cs_482_, v_sz_488_, v___x_489_, v___x_487_);
lean_dec_ref(v_cs_482_);
v_fst_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_fst_491_);
if (lean_obj_tag(v_fst_491_) == 0)
{
lean_object* v_snd_492_; lean_object* v___x_494_; 
v_snd_492_ = lean_ctor_get(v___x_490_, 1);
lean_inc(v_snd_492_);
lean_dec_ref(v___x_490_);
if (v_isShared_485_ == 0)
{
lean_ctor_set_tag(v___x_484_, 1);
lean_ctor_set(v___x_484_, 0, v_snd_492_);
v___x_494_ = v___x_484_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_snd_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
lean_object* v_val_496_; 
lean_dec_ref(v___x_490_);
lean_del_object(v___x_484_);
v_val_496_ = lean_ctor_get(v_fst_491_, 0);
lean_inc(v_val_496_);
lean_dec_ref(v_fst_491_);
return v_val_496_;
}
}
}
else
{
lean_object* v_vs_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_513_; 
v_vs_498_ = lean_ctor_get(v_n_479_, 0);
v_isSharedCheck_513_ = !lean_is_exclusive(v_n_479_);
if (v_isSharedCheck_513_ == 0)
{
v___x_500_ = v_n_479_;
v_isShared_501_ = v_isSharedCheck_513_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_vs_498_);
lean_dec(v_n_479_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_513_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_502_; lean_object* v___x_503_; size_t v_sz_504_; size_t v___x_505_; lean_object* v___x_506_; lean_object* v_fst_507_; 
v___x_502_ = lean_box(0);
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
lean_ctor_set(v___x_503_, 1, v_b_480_);
v_sz_504_ = lean_array_size(v_vs_498_);
v___x_505_ = ((size_t)0ULL);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2(v_text_477_, v_requestedRange_478_, v_vs_498_, v_sz_504_, v___x_505_, v___x_503_);
lean_dec_ref(v_vs_498_);
v_fst_507_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_fst_507_);
if (lean_obj_tag(v_fst_507_) == 0)
{
lean_object* v_snd_508_; lean_object* v___x_510_; 
v_snd_508_ = lean_ctor_get(v___x_506_, 1);
lean_inc(v_snd_508_);
lean_dec_ref(v___x_506_);
if (v_isShared_501_ == 0)
{
lean_ctor_set(v___x_500_, 0, v_snd_508_);
v___x_510_ = v___x_500_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_snd_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
else
{
lean_object* v_val_512_; 
lean_dec_ref(v___x_506_);
lean_del_object(v___x_500_);
v_val_512_ = lean_ctor_get(v_fst_507_, 0);
lean_inc(v_val_512_);
lean_dec_ref(v_fst_507_);
return v_val_512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(lean_object* v_init_514_, lean_object* v_text_515_, lean_object* v_requestedRange_516_, lean_object* v_as_517_, size_t v_sz_518_, size_t v_i_519_, lean_object* v_b_520_){
_start:
{
uint8_t v___x_522_; 
v___x_522_ = lean_usize_dec_lt(v_i_519_, v_sz_518_);
if (v___x_522_ == 0)
{
return v_b_520_;
}
else
{
lean_object* v_snd_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_541_; 
v_snd_523_ = lean_ctor_get(v_b_520_, 1);
v_isSharedCheck_541_ = !lean_is_exclusive(v_b_520_);
if (v_isSharedCheck_541_ == 0)
{
lean_object* v_unused_542_; 
v_unused_542_ = lean_ctor_get(v_b_520_, 0);
lean_dec(v_unused_542_);
v___x_525_ = v_b_520_;
v_isShared_526_ = v_isSharedCheck_541_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_snd_523_);
lean_dec(v_b_520_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_541_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v_a_527_; lean_object* v___x_528_; 
v_a_527_ = lean_array_uget_borrowed(v_as_517_, v_i_519_);
lean_inc(v_snd_523_);
lean_inc(v_a_527_);
v___x_528_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_514_, v_text_515_, v_requestedRange_516_, v_a_527_, v_snd_523_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_529_, 0, v___x_528_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 0, v___x_529_);
v___x_531_ = v___x_525_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_snd_523_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
else
{
lean_object* v_a_533_; lean_object* v___x_534_; lean_object* v___x_536_; 
lean_dec(v_snd_523_);
v_a_533_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_533_);
lean_dec_ref(v___x_528_);
v___x_534_ = lean_box(0);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_a_533_);
lean_ctor_set(v___x_525_, 0, v___x_534_);
v___x_536_ = v___x_525_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_540_; 
v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_540_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_540_, 1, v_a_533_);
v___x_536_ = v_reuseFailAlloc_540_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
size_t v___x_537_; size_t v___x_538_; 
v___x_537_ = ((size_t)1ULL);
v___x_538_ = lean_usize_add(v_i_519_, v___x_537_);
v_i_519_ = v___x_538_;
v_b_520_ = v___x_536_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1___boxed(lean_object* v_init_543_, lean_object* v_text_544_, lean_object* v_requestedRange_545_, lean_object* v_as_546_, lean_object* v_sz_547_, lean_object* v_i_548_, lean_object* v_b_549_, lean_object* v___y_550_){
_start:
{
size_t v_sz_boxed_551_; size_t v_i_boxed_552_; lean_object* v_res_553_; 
v_sz_boxed_551_ = lean_unbox_usize(v_sz_547_);
lean_dec(v_sz_547_);
v_i_boxed_552_ = lean_unbox_usize(v_i_548_);
lean_dec(v_i_548_);
v_res_553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__1(v_init_543_, v_text_544_, v_requestedRange_545_, v_as_546_, v_sz_boxed_551_, v_i_boxed_552_, v_b_549_);
lean_dec_ref(v_as_546_);
lean_dec_ref(v_requestedRange_545_);
lean_dec_ref(v_text_544_);
lean_dec_ref(v_init_543_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0___boxed(lean_object* v_init_554_, lean_object* v_text_555_, lean_object* v_requestedRange_556_, lean_object* v_n_557_, lean_object* v_b_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_554_, v_text_555_, v_requestedRange_556_, v_n_557_, v_b_558_);
lean_dec_ref(v_requestedRange_556_);
lean_dec_ref(v_text_555_);
lean_dec_ref(v_init_554_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(lean_object* v_text_561_, lean_object* v_requestedRange_562_, lean_object* v_as_563_, size_t v_sz_564_, size_t v_i_565_, lean_object* v_b_566_){
_start:
{
uint8_t v___x_568_; 
v___x_568_ = lean_usize_dec_lt(v_i_565_, v_sz_564_);
if (v___x_568_ == 0)
{
return v_b_566_;
}
else
{
lean_object* v_snd_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_596_; 
v_snd_569_ = lean_ctor_get(v_b_566_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_b_566_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_b_566_, 0);
lean_dec(v_unused_597_);
v___x_571_ = v_b_566_;
v_isShared_572_ = v_isSharedCheck_596_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_snd_569_);
lean_dec(v_b_566_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_596_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v_a_573_; lean_object* v_pos_574_; lean_object* v_endPos_575_; lean_object* v_data_576_; lean_object* v___f_577_; lean_object* v___x_578_; lean_object* v_a_580_; uint8_t v___x_587_; 
v_a_573_ = lean_array_uget_borrowed(v_as_563_, v_i_565_);
v_pos_574_ = lean_ctor_get(v_a_573_, 1);
v_endPos_575_ = lean_ctor_get(v_a_573_, 2);
v_data_576_ = lean_ctor_get(v_a_573_, 4);
v___f_577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_578_ = lean_box(0);
lean_inc(v_data_576_);
v___x_587_ = l_Lean_MessageData_hasTag(v___f_577_, v_data_576_);
if (v___x_587_ == 0)
{
v_a_580_ = v_snd_569_;
goto v___jp_579_;
}
else
{
lean_object* v___x_588_; lean_object* v___y_590_; 
lean_inc_ref(v_pos_574_);
v___x_588_ = l_Lean_FileMap_ofPosition(v_text_561_, v_pos_574_);
if (lean_obj_tag(v_endPos_575_) == 0)
{
lean_inc_ref(v_pos_574_);
v___y_590_ = v_pos_574_;
goto v___jp_589_;
}
else
{
lean_object* v_val_595_; 
v_val_595_ = lean_ctor_get(v_endPos_575_, 0);
lean_inc(v_val_595_);
v___y_590_ = v_val_595_;
goto v___jp_589_;
}
v___jp_589_:
{
lean_object* v___x_591_; lean_object* v_msgRange_592_; uint8_t v___x_593_; 
v___x_591_ = l_Lean_FileMap_ofPosition(v_text_561_, v___y_590_);
v_msgRange_592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_592_, 0, v___x_588_);
lean_ctor_set(v_msgRange_592_, 1, v___x_591_);
v___x_593_ = l_Lean_Syntax_Range_overlaps(v_msgRange_592_, v_requestedRange_562_, v___x_587_, v___x_587_);
if (v___x_593_ == 0)
{
lean_dec_ref(v_msgRange_592_);
v_a_580_ = v_snd_569_;
goto v___jp_579_;
}
else
{
lean_object* v_ranges_594_; 
v_ranges_594_ = lean_array_push(v_snd_569_, v_msgRange_592_);
v_a_580_ = v_ranges_594_;
goto v___jp_579_;
}
}
}
v___jp_579_:
{
lean_object* v___x_582_; 
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 1, v_a_580_);
lean_ctor_set(v___x_571_, 0, v___x_578_);
v___x_582_ = v___x_571_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_578_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_a_580_);
v___x_582_ = v_reuseFailAlloc_586_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
size_t v___x_583_; size_t v___x_584_; 
v___x_583_ = ((size_t)1ULL);
v___x_584_ = lean_usize_add(v_i_565_, v___x_583_);
v_i_565_ = v___x_584_;
v_b_566_ = v___x_582_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4___boxed(lean_object* v_text_598_, lean_object* v_requestedRange_599_, lean_object* v_as_600_, lean_object* v_sz_601_, lean_object* v_i_602_, lean_object* v_b_603_, lean_object* v___y_604_){
_start:
{
size_t v_sz_boxed_605_; size_t v_i_boxed_606_; lean_object* v_res_607_; 
v_sz_boxed_605_ = lean_unbox_usize(v_sz_601_);
lean_dec(v_sz_601_);
v_i_boxed_606_ = lean_unbox_usize(v_i_602_);
lean_dec(v_i_602_);
v_res_607_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(v_text_598_, v_requestedRange_599_, v_as_600_, v_sz_boxed_605_, v_i_boxed_606_, v_b_603_);
lean_dec_ref(v_as_600_);
lean_dec_ref(v_requestedRange_599_);
lean_dec_ref(v_text_598_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(lean_object* v_text_608_, lean_object* v_requestedRange_609_, lean_object* v_as_610_, size_t v_sz_611_, size_t v_i_612_, lean_object* v_b_613_){
_start:
{
uint8_t v___x_615_; 
v___x_615_ = lean_usize_dec_lt(v_i_612_, v_sz_611_);
if (v___x_615_ == 0)
{
return v_b_613_;
}
else
{
lean_object* v_snd_616_; lean_object* v___x_618_; uint8_t v_isShared_619_; uint8_t v_isSharedCheck_643_; 
v_snd_616_ = lean_ctor_get(v_b_613_, 1);
v_isSharedCheck_643_ = !lean_is_exclusive(v_b_613_);
if (v_isSharedCheck_643_ == 0)
{
lean_object* v_unused_644_; 
v_unused_644_ = lean_ctor_get(v_b_613_, 0);
lean_dec(v_unused_644_);
v___x_618_ = v_b_613_;
v_isShared_619_ = v_isSharedCheck_643_;
goto v_resetjp_617_;
}
else
{
lean_inc(v_snd_616_);
lean_dec(v_b_613_);
v___x_618_ = lean_box(0);
v_isShared_619_ = v_isSharedCheck_643_;
goto v_resetjp_617_;
}
v_resetjp_617_:
{
lean_object* v_a_620_; lean_object* v_pos_621_; lean_object* v_endPos_622_; lean_object* v_data_623_; lean_object* v___f_624_; lean_object* v___x_625_; lean_object* v_a_627_; uint8_t v___x_634_; 
v_a_620_ = lean_array_uget_borrowed(v_as_610_, v_i_612_);
v_pos_621_ = lean_ctor_get(v_a_620_, 1);
v_endPos_622_ = lean_ctor_get(v_a_620_, 2);
v_data_623_ = lean_ctor_get(v_a_620_, 4);
v___f_624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_625_ = lean_box(0);
lean_inc(v_data_623_);
v___x_634_ = l_Lean_MessageData_hasTag(v___f_624_, v_data_623_);
if (v___x_634_ == 0)
{
v_a_627_ = v_snd_616_;
goto v___jp_626_;
}
else
{
lean_object* v___x_635_; lean_object* v___y_637_; 
lean_inc_ref(v_pos_621_);
v___x_635_ = l_Lean_FileMap_ofPosition(v_text_608_, v_pos_621_);
if (lean_obj_tag(v_endPos_622_) == 0)
{
lean_inc_ref(v_pos_621_);
v___y_637_ = v_pos_621_;
goto v___jp_636_;
}
else
{
lean_object* v_val_642_; 
v_val_642_ = lean_ctor_get(v_endPos_622_, 0);
lean_inc(v_val_642_);
v___y_637_ = v_val_642_;
goto v___jp_636_;
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v_msgRange_639_; uint8_t v___x_640_; 
v___x_638_ = l_Lean_FileMap_ofPosition(v_text_608_, v___y_637_);
v_msgRange_639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_639_, 0, v___x_635_);
lean_ctor_set(v_msgRange_639_, 1, v___x_638_);
v___x_640_ = l_Lean_Syntax_Range_overlaps(v_msgRange_639_, v_requestedRange_609_, v___x_634_, v___x_634_);
if (v___x_640_ == 0)
{
lean_dec_ref(v_msgRange_639_);
v_a_627_ = v_snd_616_;
goto v___jp_626_;
}
else
{
lean_object* v_ranges_641_; 
v_ranges_641_ = lean_array_push(v_snd_616_, v_msgRange_639_);
v_a_627_ = v_ranges_641_;
goto v___jp_626_;
}
}
}
v___jp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_619_ == 0)
{
lean_ctor_set(v___x_618_, 1, v_a_627_);
lean_ctor_set(v___x_618_, 0, v___x_625_);
v___x_629_ = v___x_618_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_a_627_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_add(v_i_612_, v___x_630_);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1_spec__4(v_text_608_, v_requestedRange_609_, v_as_610_, v_sz_611_, v___x_631_, v___x_629_);
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1___boxed(lean_object* v_text_645_, lean_object* v_requestedRange_646_, lean_object* v_as_647_, lean_object* v_sz_648_, lean_object* v_i_649_, lean_object* v_b_650_, lean_object* v___y_651_){
_start:
{
size_t v_sz_boxed_652_; size_t v_i_boxed_653_; lean_object* v_res_654_; 
v_sz_boxed_652_ = lean_unbox_usize(v_sz_648_);
lean_dec(v_sz_648_);
v_i_boxed_653_ = lean_unbox_usize(v_i_649_);
lean_dec(v_i_649_);
v_res_654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_645_, v_requestedRange_646_, v_as_647_, v_sz_boxed_652_, v_i_boxed_653_, v_b_650_);
lean_dec_ref(v_as_647_);
lean_dec_ref(v_requestedRange_646_);
lean_dec_ref(v_text_645_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(lean_object* v_text_655_, lean_object* v_requestedRange_656_, lean_object* v_t_657_, lean_object* v_init_658_){
_start:
{
lean_object* v_root_660_; lean_object* v_tail_661_; lean_object* v___x_662_; 
v_root_660_ = lean_ctor_get(v_t_657_, 0);
lean_inc_ref(v_root_660_);
v_tail_661_ = lean_ctor_get(v_t_657_, 1);
lean_inc_ref(v_tail_661_);
lean_dec_ref(v_t_657_);
lean_inc_ref(v_init_658_);
v___x_662_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0(v_init_658_, v_text_655_, v_requestedRange_656_, v_root_660_, v_init_658_);
lean_dec_ref(v_init_658_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; 
lean_dec_ref(v_tail_661_);
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref(v___x_662_);
return v_a_663_;
}
else
{
lean_object* v_a_664_; lean_object* v___x_665_; lean_object* v___x_666_; size_t v_sz_667_; size_t v___x_668_; lean_object* v___x_669_; lean_object* v_fst_670_; 
v_a_664_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_664_);
lean_dec_ref(v___x_662_);
v___x_665_ = lean_box(0);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v_a_664_);
v_sz_667_ = lean_array_size(v_tail_661_);
v___x_668_ = ((size_t)0ULL);
v___x_669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__1(v_text_655_, v_requestedRange_656_, v_tail_661_, v_sz_667_, v___x_668_, v___x_666_);
lean_dec_ref(v_tail_661_);
v_fst_670_ = lean_ctor_get(v___x_669_, 0);
lean_inc(v_fst_670_);
if (lean_obj_tag(v_fst_670_) == 0)
{
lean_object* v_snd_671_; 
v_snd_671_ = lean_ctor_get(v___x_669_, 1);
lean_inc(v_snd_671_);
lean_dec_ref(v___x_669_);
return v_snd_671_;
}
else
{
lean_object* v_val_672_; 
lean_dec_ref(v___x_669_);
v_val_672_ = lean_ctor_get(v_fst_670_, 0);
lean_inc(v_val_672_);
lean_dec_ref(v_fst_670_);
return v_val_672_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0___boxed(lean_object* v_text_673_, lean_object* v_requestedRange_674_, lean_object* v_t_675_, lean_object* v_init_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_673_, v_requestedRange_674_, v_t_675_, v_init_676_);
lean_dec_ref(v_requestedRange_674_);
lean_dec_ref(v_text_673_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(lean_object* v_init_679_, lean_object* v_x_680_){
_start:
{
if (lean_obj_tag(v_x_680_) == 0)
{
lean_object* v_k_681_; lean_object* v_l_682_; lean_object* v_r_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v_k_681_ = lean_ctor_get(v_x_680_, 1);
lean_inc(v_k_681_);
v_l_682_ = lean_ctor_get(v_x_680_, 3);
lean_inc(v_l_682_);
v_r_683_ = lean_ctor_get(v_x_680_, 4);
lean_inc(v_r_683_);
lean_dec_ref(v_x_680_);
v___x_684_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v_init_679_, v_l_682_);
v___x_685_ = lean_array_push(v___x_684_, v_k_681_);
v_init_679_ = v___x_685_;
v_x_680_ = v_r_683_;
goto _start;
}
else
{
return v_init_679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(lean_object* v_doc_694_, lean_object* v_requestedRange_695_){
_start:
{
lean_object* v_toEditableDocumentCore_697_; lean_object* v_start_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
v_toEditableDocumentCore_697_ = lean_ctor_get(v_doc_694_, 0);
lean_inc_ref(v_toEditableDocumentCore_697_);
v_start_698_ = lean_ctor_get(v_requestedRange_695_, 0);
lean_inc(v_start_698_);
v___x_699_ = l_Lean_Server_RequestM_findCmdParsedSnap(v_doc_694_, v_start_698_);
v___x_700_ = lean_task_get_own(v___x_699_);
if (lean_obj_tag(v___x_700_) == 1)
{
lean_object* v_meta_701_; lean_object* v_val_702_; lean_object* v_text_703_; lean_object* v_elabSnap_704_; lean_object* v_tree_705_; lean_object* v___x_706_; lean_object* v_msgLog_707_; lean_object* v_unreported_708_; lean_object* v___x_709_; lean_object* v_ranges_710_; lean_object* v___x_711_; uint8_t v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___f_721_; uint8_t v___y_723_; lean_object* v___x_728_; uint8_t v___x_729_; 
v_meta_701_ = lean_ctor_get(v_toEditableDocumentCore_697_, 0);
lean_inc_ref(v_meta_701_);
lean_dec_ref(v_toEditableDocumentCore_697_);
v_val_702_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_val_702_);
lean_dec_ref(v___x_700_);
v_text_703_ = lean_ctor_get(v_meta_701_, 3);
lean_inc_ref(v_text_703_);
lean_dec_ref(v_meta_701_);
v_elabSnap_704_ = lean_ctor_get(v_val_702_, 3);
lean_inc_ref(v_elabSnap_704_);
lean_dec(v_val_702_);
v_tree_705_ = l_Lean_Language_Lean_instToSnapshotTreeCommandElaboratingSnapshot_go(v_elabSnap_704_);
lean_inc_ref(v_requestedRange_695_);
lean_inc_ref(v_tree_705_);
v___x_706_ = l_Lean_Language_SnapshotTree_collectMessagesInRange(v_tree_705_, v_requestedRange_695_);
v_msgLog_707_ = lean_task_get_own(v___x_706_);
v_unreported_708_ = lean_ctor_get(v_msgLog_707_, 1);
lean_inc_ref(v_unreported_708_);
lean_dec(v_msgLog_707_);
v___x_709_ = lean_unsigned_to_nat(0u);
v_ranges_710_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0));
v___x_711_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0(v_text_703_, v_requestedRange_695_, v_unreported_708_, v_ranges_710_);
lean_dec_ref(v_text_703_);
v___f_721_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1));
v___x_728_ = lean_array_get_size(v___x_711_);
v___x_729_ = lean_nat_dec_eq(v___x_728_, v___x_709_);
if (v___x_729_ == 0)
{
uint8_t v___x_730_; 
v___x_730_ = 1;
v___y_723_ = v___x_730_;
goto v___jp_722_;
}
else
{
uint8_t v___x_731_; 
v___x_731_ = 0;
v___y_723_ = v___x_731_;
goto v___jp_722_;
}
v___jp_712_:
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_716_ = lean_mk_empty_array_with_capacity(v___y_715_);
lean_dec(v___y_715_);
v___x_717_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_716_, v___y_714_);
v___x_718_ = l_Array_append___redArg(v___x_711_, v___x_717_);
lean_dec_ref(v___x_717_);
v___x_719_ = lean_box(v___y_713_);
v___x_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_720_, 0, v___x_718_);
lean_ctor_set(v___x_720_, 1, v___x_719_);
return v___x_720_;
}
v___jp_722_:
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_724_ = lean_box(1);
v___x_725_ = l_Lean_Language_SnapshotTree_foldInfosInRange___redArg(v_tree_705_, v_requestedRange_695_, v___x_724_, v___f_721_);
v___x_726_ = lean_task_get_own(v___x_725_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v_size_727_; 
v_size_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc(v_size_727_);
v___y_713_ = v___y_723_;
v___y_714_ = v___x_726_;
v___y_715_ = v_size_727_;
goto v___jp_712_;
}
else
{
v___y_713_ = v___y_723_;
v___y_714_ = v___x_726_;
v___y_715_ = v___x_709_;
goto v___jp_712_;
}
}
}
else
{
lean_object* v___x_732_; 
lean_dec(v___x_700_);
lean_dec_ref(v_toEditableDocumentCore_697_);
lean_dec_ref(v_requestedRange_695_);
v___x_732_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__2));
return v___x_732_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___boxed(lean_object* v_doc_733_, lean_object* v_requestedRange_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_Lean_Server_FileWorker_waitUnknownIdentifierRanges(v_doc_733_, v_requestedRange_734_);
return v_res_736_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(lean_object* v_00_u03b2_737_, lean_object* v_k_738_, lean_object* v_t_739_){
_start:
{
uint8_t v___x_740_; 
v___x_740_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___redArg(v_k_738_, v_t_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2___boxed(lean_object* v_00_u03b2_741_, lean_object* v_k_742_, lean_object* v_t_743_){
_start:
{
uint8_t v_res_744_; lean_object* v_r_745_; 
v_res_744_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__2(v_00_u03b2_741_, v_k_742_, v_t_743_);
lean_dec(v_t_743_);
lean_dec_ref(v_k_742_);
v_r_745_ = lean_box(v_res_744_);
return v_r_745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3(lean_object* v_00_u03b2_746_, lean_object* v_k_747_, lean_object* v_v_748_, lean_object* v_t_749_, lean_object* v_hl_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__3___redArg(v_k_747_, v_v_748_, v_t_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4(lean_object* v_init_752_, lean_object* v_t_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v_init_752_, v_t_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0(lean_object* v_s_757_){
_start:
{
lean_object* v___x_758_; lean_object* v___x_759_; 
v___x_758_ = ((lean_object*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__0___closed__0));
v___x_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_759_, 0, v_s_757_);
lean_ctor_set(v___x_759_, 1, v___x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2(lean_object* v___f_761_, lean_object* v_s_762_){
_start:
{
lean_object* v_toSnapshot_763_; lean_object* v_metaSnap_764_; lean_object* v_result_x3f_765_; lean_object* v___y_767_; 
v_toSnapshot_763_ = lean_ctor_get(v_s_762_, 0);
lean_inc_ref(v_toSnapshot_763_);
v_metaSnap_764_ = lean_ctor_get(v_s_762_, 1);
lean_inc_ref(v_metaSnap_764_);
v_result_x3f_765_ = lean_ctor_get(v_s_762_, 2);
lean_inc(v_result_x3f_765_);
lean_dec_ref(v_s_762_);
if (lean_obj_tag(v_result_x3f_765_) == 0)
{
lean_object* v___x_777_; 
v___x_777_ = lean_box(0);
v___y_767_ = v___x_777_;
goto v___jp_766_;
}
else
{
lean_object* v_val_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_791_; 
v_val_778_ = lean_ctor_get(v_result_x3f_765_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v_result_x3f_765_);
if (v_isSharedCheck_791_ == 0)
{
v___x_780_ = v_result_x3f_765_;
v_isShared_781_ = v_isSharedCheck_791_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_val_778_);
lean_dec(v_result_x3f_765_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_791_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v_firstCmdSnap_782_; lean_object* v_stx_x3f_783_; lean_object* v_reportingRange_784_; lean_object* v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; lean_object* v___x_789_; 
v_firstCmdSnap_782_ = lean_ctor_get(v_val_778_, 1);
lean_inc_ref(v_firstCmdSnap_782_);
lean_dec(v_val_778_);
v_stx_x3f_783_ = lean_ctor_get(v_firstCmdSnap_782_, 0);
lean_inc(v_stx_x3f_783_);
v_reportingRange_784_ = lean_ctor_get(v_firstCmdSnap_782_, 1);
lean_inc(v_reportingRange_784_);
v___x_785_ = ((lean_object*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___lam__2___closed__0));
v___x_786_ = 1;
v___x_787_ = l_Lean_Language_SnapshotTask_map___redArg(v_firstCmdSnap_782_, v___x_785_, v_stx_x3f_783_, v_reportingRange_784_, v___x_786_);
if (v_isShared_781_ == 0)
{
lean_ctor_set(v___x_780_, 0, v___x_787_);
v___x_789_ = v___x_780_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v___x_787_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
v___y_767_ = v___x_789_;
goto v___jp_766_;
}
}
}
v___jp_766_:
{
lean_object* v_stx_x3f_768_; lean_object* v_reportingRange_769_; uint8_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v_stx_x3f_768_ = lean_ctor_get(v_metaSnap_764_, 0);
lean_inc(v_stx_x3f_768_);
v_reportingRange_769_ = lean_ctor_get(v_metaSnap_764_, 1);
lean_inc(v_reportingRange_769_);
v___x_770_ = 1;
v___x_771_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_764_, v___f_761_, v_stx_x3f_768_, v_reportingRange_769_, v___x_770_);
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_mk_empty_array_with_capacity(v___x_772_);
v___x_774_ = lean_array_push(v___x_773_, v___x_771_);
v___x_775_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_767_, v___x_774_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_toSnapshot_763_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(lean_object* v_as_792_, size_t v_i_793_, size_t v_stop_794_, lean_object* v_b_795_){
_start:
{
uint8_t v___x_796_; 
v___x_796_ = lean_usize_dec_eq(v_i_793_, v_stop_794_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; size_t v___x_799_; size_t v___x_800_; 
v___x_797_ = lean_array_uget_borrowed(v_as_792_, v_i_793_);
lean_inc(v___x_797_);
v___x_798_ = l_Lean_MessageLog_append(v_b_795_, v___x_797_);
v___x_799_ = ((size_t)1ULL);
v___x_800_ = lean_usize_add(v_i_793_, v___x_799_);
v_i_793_ = v___x_800_;
v_b_795_ = v___x_798_;
goto _start;
}
else
{
return v_b_795_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3___boxed(lean_object* v_as_802_, lean_object* v_i_803_, lean_object* v_stop_804_, lean_object* v_b_805_){
_start:
{
size_t v_i_boxed_806_; size_t v_stop_boxed_807_; lean_object* v_res_808_; 
v_i_boxed_806_ = lean_unbox_usize(v_i_803_);
lean_dec(v_i_803_);
v_stop_boxed_807_ = lean_unbox_usize(v_stop_804_);
lean_dec(v_stop_804_);
v_res_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v_as_802_, v_i_boxed_806_, v_stop_boxed_807_, v_b_805_);
lean_dec_ref(v_as_802_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(lean_object* v_as_x27_809_, lean_object* v_b_810_){
_start:
{
if (lean_obj_tag(v_as_x27_809_) == 0)
{
return v_b_810_;
}
else
{
lean_object* v_head_812_; lean_object* v_tail_813_; lean_object* v___f_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___y_819_; 
v_head_812_ = lean_ctor_get(v_as_x27_809_, 0);
lean_inc(v_head_812_);
v_tail_813_ = lean_ctor_get(v_as_x27_809_, 1);
lean_inc(v_tail_813_);
lean_dec_ref(v_as_x27_809_);
v___f_814_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1));
v___x_815_ = lean_box(1);
v___x_816_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_812_);
v___x_817_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_814_, v___x_815_, v___x_816_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_size_824_; 
v_size_824_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_size_824_);
v___y_819_ = v_size_824_;
goto v___jp_818_;
}
else
{
lean_object* v___x_825_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___y_819_ = v___x_825_;
goto v___jp_818_;
}
v___jp_818_:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_mk_empty_array_with_capacity(v___y_819_);
lean_dec(v___y_819_);
v___x_821_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_820_, v___x_817_);
v___x_822_ = l_Array_append___redArg(v_b_810_, v___x_821_);
lean_dec_ref(v___x_821_);
v_as_x27_809_ = v_tail_813_;
v_b_810_ = v___x_822_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg___boxed(lean_object* v_as_x27_826_, lean_object* v_b_827_, lean_object* v___y_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_826_, v_b_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(lean_object* v_as_830_, lean_object* v_as_x27_831_, lean_object* v_b_832_){
_start:
{
if (lean_obj_tag(v_as_x27_831_) == 0)
{
return v_b_832_;
}
else
{
lean_object* v_head_834_; lean_object* v_tail_835_; lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___y_841_; 
v_head_834_ = lean_ctor_get(v_as_x27_831_, 0);
lean_inc(v_head_834_);
v_tail_835_ = lean_ctor_get(v_as_x27_831_, 1);
lean_inc(v_tail_835_);
lean_dec_ref(v_as_x27_831_);
v___f_836_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__1));
v___x_837_ = lean_box(1);
v___x_838_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_head_834_);
v___x_839_ = l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_836_, v___x_837_, v___x_838_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_size_846_; 
v_size_846_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_size_846_);
v___y_841_ = v_size_846_;
goto v___jp_840_;
}
else
{
lean_object* v___x_847_; 
v___x_847_ = lean_unsigned_to_nat(0u);
v___y_841_ = v___x_847_;
goto v___jp_840_;
}
v___jp_840_:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_842_ = lean_mk_empty_array_with_capacity(v___y_841_);
lean_dec(v___y_841_);
v___x_843_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__4_spec__7(v___x_842_, v___x_839_);
v___x_844_ = l_Array_append___redArg(v_b_832_, v___x_843_);
lean_dec_ref(v___x_843_);
v___x_845_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_tail_835_, v___x_844_);
return v___x_845_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg___boxed(lean_object* v_as_848_, lean_object* v_as_x27_849_, lean_object* v_b_850_, lean_object* v___y_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_848_, v_as_x27_849_, v_b_850_);
lean_dec(v_as_848_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(lean_object* v_text_853_, lean_object* v_as_854_, size_t v_sz_855_, size_t v_i_856_, lean_object* v_b_857_){
_start:
{
uint8_t v___x_859_; 
v___x_859_ = lean_usize_dec_lt(v_i_856_, v_sz_855_);
if (v___x_859_ == 0)
{
return v_b_857_;
}
else
{
lean_object* v_snd_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_886_; 
v_snd_860_ = lean_ctor_get(v_b_857_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_b_857_);
if (v_isSharedCheck_886_ == 0)
{
lean_object* v_unused_887_; 
v_unused_887_ = lean_ctor_get(v_b_857_, 0);
lean_dec(v_unused_887_);
v___x_862_ = v_b_857_;
v_isShared_863_ = v_isSharedCheck_886_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_snd_860_);
lean_dec(v_b_857_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_886_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v_a_864_; lean_object* v_pos_865_; lean_object* v_endPos_866_; lean_object* v_data_867_; lean_object* v___f_868_; lean_object* v___x_869_; lean_object* v_a_871_; uint8_t v___x_878_; 
v_a_864_ = lean_array_uget_borrowed(v_as_854_, v_i_856_);
v_pos_865_ = lean_ctor_get(v_a_864_, 1);
v_endPos_866_ = lean_ctor_get(v_a_864_, 2);
v_data_867_ = lean_ctor_get(v_a_864_, 4);
v___f_868_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_869_ = lean_box(0);
lean_inc(v_data_867_);
v___x_878_ = l_Lean_MessageData_hasTag(v___f_868_, v_data_867_);
if (v___x_878_ == 0)
{
v_a_871_ = v_snd_860_;
goto v___jp_870_;
}
else
{
lean_object* v___x_879_; lean_object* v___y_881_; 
lean_inc_ref(v_pos_865_);
v___x_879_ = l_Lean_FileMap_ofPosition(v_text_853_, v_pos_865_);
if (lean_obj_tag(v_endPos_866_) == 0)
{
lean_inc_ref(v_pos_865_);
v___y_881_ = v_pos_865_;
goto v___jp_880_;
}
else
{
lean_object* v_val_885_; 
v_val_885_ = lean_ctor_get(v_endPos_866_, 0);
lean_inc(v_val_885_);
v___y_881_ = v_val_885_;
goto v___jp_880_;
}
v___jp_880_:
{
lean_object* v___x_882_; lean_object* v_msgRange_883_; lean_object* v_ranges_884_; 
v___x_882_ = l_Lean_FileMap_ofPosition(v_text_853_, v___y_881_);
v_msgRange_883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_883_, 0, v___x_879_);
lean_ctor_set(v_msgRange_883_, 1, v___x_882_);
v_ranges_884_ = lean_array_push(v_snd_860_, v_msgRange_883_);
v_a_871_ = v_ranges_884_;
goto v___jp_870_;
}
}
v___jp_870_:
{
lean_object* v___x_873_; 
if (v_isShared_863_ == 0)
{
lean_ctor_set(v___x_862_, 1, v_a_871_);
lean_ctor_set(v___x_862_, 0, v___x_869_);
v___x_873_ = v___x_862_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v___x_869_);
lean_ctor_set(v_reuseFailAlloc_877_, 1, v_a_871_);
v___x_873_ = v_reuseFailAlloc_877_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
size_t v___x_874_; size_t v___x_875_; 
v___x_874_ = ((size_t)1ULL);
v___x_875_ = lean_usize_add(v_i_856_, v___x_874_);
v_i_856_ = v___x_875_;
v_b_857_ = v___x_873_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4___boxed(lean_object* v_text_888_, lean_object* v_as_889_, lean_object* v_sz_890_, lean_object* v_i_891_, lean_object* v_b_892_, lean_object* v___y_893_){
_start:
{
size_t v_sz_boxed_894_; size_t v_i_boxed_895_; lean_object* v_res_896_; 
v_sz_boxed_894_ = lean_unbox_usize(v_sz_890_);
lean_dec(v_sz_890_);
v_i_boxed_895_ = lean_unbox_usize(v_i_891_);
lean_dec(v_i_891_);
v_res_896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(v_text_888_, v_as_889_, v_sz_boxed_894_, v_i_boxed_895_, v_b_892_);
lean_dec_ref(v_as_889_);
lean_dec_ref(v_text_888_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(lean_object* v_text_897_, lean_object* v_as_898_, size_t v_sz_899_, size_t v_i_900_, lean_object* v_b_901_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_usize_dec_lt(v_i_900_, v_sz_899_);
if (v___x_903_ == 0)
{
return v_b_901_;
}
else
{
lean_object* v_snd_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_930_; 
v_snd_904_ = lean_ctor_get(v_b_901_, 1);
v_isSharedCheck_930_ = !lean_is_exclusive(v_b_901_);
if (v_isSharedCheck_930_ == 0)
{
lean_object* v_unused_931_; 
v_unused_931_ = lean_ctor_get(v_b_901_, 0);
lean_dec(v_unused_931_);
v___x_906_ = v_b_901_;
v_isShared_907_ = v_isSharedCheck_930_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_snd_904_);
lean_dec(v_b_901_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_930_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v_a_908_; lean_object* v_pos_909_; lean_object* v_endPos_910_; lean_object* v_data_911_; lean_object* v___f_912_; lean_object* v___x_913_; lean_object* v_a_915_; uint8_t v___x_922_; 
v_a_908_ = lean_array_uget_borrowed(v_as_898_, v_i_900_);
v_pos_909_ = lean_ctor_get(v_a_908_, 1);
v_endPos_910_ = lean_ctor_get(v_a_908_, 2);
v_data_911_ = lean_ctor_get(v_a_908_, 4);
v___f_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_913_ = lean_box(0);
lean_inc(v_data_911_);
v___x_922_ = l_Lean_MessageData_hasTag(v___f_912_, v_data_911_);
if (v___x_922_ == 0)
{
v_a_915_ = v_snd_904_;
goto v___jp_914_;
}
else
{
lean_object* v___x_923_; lean_object* v___y_925_; 
lean_inc_ref(v_pos_909_);
v___x_923_ = l_Lean_FileMap_ofPosition(v_text_897_, v_pos_909_);
if (lean_obj_tag(v_endPos_910_) == 0)
{
lean_inc_ref(v_pos_909_);
v___y_925_ = v_pos_909_;
goto v___jp_924_;
}
else
{
lean_object* v_val_929_; 
v_val_929_ = lean_ctor_get(v_endPos_910_, 0);
lean_inc(v_val_929_);
v___y_925_ = v_val_929_;
goto v___jp_924_;
}
v___jp_924_:
{
lean_object* v___x_926_; lean_object* v_msgRange_927_; lean_object* v_ranges_928_; 
v___x_926_ = l_Lean_FileMap_ofPosition(v_text_897_, v___y_925_);
v_msgRange_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_927_, 0, v___x_923_);
lean_ctor_set(v_msgRange_927_, 1, v___x_926_);
v_ranges_928_ = lean_array_push(v_snd_904_, v_msgRange_927_);
v_a_915_ = v_ranges_928_;
goto v___jp_914_;
}
}
v___jp_914_:
{
lean_object* v___x_917_; 
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v_a_915_);
lean_ctor_set(v___x_906_, 0, v___x_913_);
v___x_917_ = v___x_906_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_913_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_a_915_);
v___x_917_ = v_reuseFailAlloc_921_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
v___x_918_ = ((size_t)1ULL);
v___x_919_ = lean_usize_add(v_i_900_, v___x_918_);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1_spec__4(v_text_897_, v_as_898_, v_sz_899_, v___x_919_, v___x_917_);
return v___x_920_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1___boxed(lean_object* v_text_932_, lean_object* v_as_933_, lean_object* v_sz_934_, lean_object* v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_){
_start:
{
size_t v_sz_boxed_938_; size_t v_i_boxed_939_; lean_object* v_res_940_; 
v_sz_boxed_938_ = lean_unbox_usize(v_sz_934_);
lean_dec(v_sz_934_);
v_i_boxed_939_ = lean_unbox_usize(v_i_935_);
lean_dec(v_i_935_);
v_res_940_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_932_, v_as_933_, v_sz_boxed_938_, v_i_boxed_939_, v_b_936_);
lean_dec_ref(v_as_933_);
lean_dec_ref(v_text_932_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(lean_object* v_text_941_, lean_object* v_as_942_, size_t v_sz_943_, size_t v_i_944_, lean_object* v_b_945_){
_start:
{
uint8_t v___x_947_; 
v___x_947_ = lean_usize_dec_lt(v_i_944_, v_sz_943_);
if (v___x_947_ == 0)
{
return v_b_945_;
}
else
{
lean_object* v_snd_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_974_; 
v_snd_948_ = lean_ctor_get(v_b_945_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_b_945_);
if (v_isSharedCheck_974_ == 0)
{
lean_object* v_unused_975_; 
v_unused_975_ = lean_ctor_get(v_b_945_, 0);
lean_dec(v_unused_975_);
v___x_950_ = v_b_945_;
v_isShared_951_ = v_isSharedCheck_974_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_snd_948_);
lean_dec(v_b_945_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_974_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_a_952_; lean_object* v_pos_953_; lean_object* v_endPos_954_; lean_object* v_data_955_; lean_object* v___f_956_; lean_object* v___x_957_; lean_object* v_a_959_; uint8_t v___x_966_; 
v_a_952_ = lean_array_uget_borrowed(v_as_942_, v_i_944_);
v_pos_953_ = lean_ctor_get(v_a_952_, 1);
v_endPos_954_ = lean_ctor_get(v_a_952_, 2);
v_data_955_ = lean_ctor_get(v_a_952_, 4);
v___f_956_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_957_ = lean_box(0);
lean_inc(v_data_955_);
v___x_966_ = l_Lean_MessageData_hasTag(v___f_956_, v_data_955_);
if (v___x_966_ == 0)
{
v_a_959_ = v_snd_948_;
goto v___jp_958_;
}
else
{
lean_object* v___x_967_; lean_object* v___y_969_; 
lean_inc_ref(v_pos_953_);
v___x_967_ = l_Lean_FileMap_ofPosition(v_text_941_, v_pos_953_);
if (lean_obj_tag(v_endPos_954_) == 0)
{
lean_inc_ref(v_pos_953_);
v___y_969_ = v_pos_953_;
goto v___jp_968_;
}
else
{
lean_object* v_val_973_; 
v_val_973_ = lean_ctor_get(v_endPos_954_, 0);
lean_inc(v_val_973_);
v___y_969_ = v_val_973_;
goto v___jp_968_;
}
v___jp_968_:
{
lean_object* v___x_970_; lean_object* v_msgRange_971_; lean_object* v_ranges_972_; 
v___x_970_ = l_Lean_FileMap_ofPosition(v_text_941_, v___y_969_);
v_msgRange_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_971_, 0, v___x_967_);
lean_ctor_set(v_msgRange_971_, 1, v___x_970_);
v_ranges_972_ = lean_array_push(v_snd_948_, v_msgRange_971_);
v_a_959_ = v_ranges_972_;
goto v___jp_958_;
}
}
v___jp_958_:
{
lean_object* v___x_961_; 
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 1, v_a_959_);
lean_ctor_set(v___x_950_, 0, v___x_957_);
v___x_961_ = v___x_950_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_957_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_a_959_);
v___x_961_ = v_reuseFailAlloc_965_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
size_t v___x_962_; size_t v___x_963_; 
v___x_962_ = ((size_t)1ULL);
v___x_963_ = lean_usize_add(v_i_944_, v___x_962_);
v_i_944_ = v___x_963_;
v_b_945_ = v___x_961_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6___boxed(lean_object* v_text_976_, lean_object* v_as_977_, lean_object* v_sz_978_, lean_object* v_i_979_, lean_object* v_b_980_, lean_object* v___y_981_){
_start:
{
size_t v_sz_boxed_982_; size_t v_i_boxed_983_; lean_object* v_res_984_; 
v_sz_boxed_982_ = lean_unbox_usize(v_sz_978_);
lean_dec(v_sz_978_);
v_i_boxed_983_ = lean_unbox_usize(v_i_979_);
lean_dec(v_i_979_);
v_res_984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(v_text_976_, v_as_977_, v_sz_boxed_982_, v_i_boxed_983_, v_b_980_);
lean_dec_ref(v_as_977_);
lean_dec_ref(v_text_976_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(lean_object* v_text_985_, lean_object* v_as_986_, size_t v_sz_987_, size_t v_i_988_, lean_object* v_b_989_){
_start:
{
uint8_t v___x_991_; 
v___x_991_ = lean_usize_dec_lt(v_i_988_, v_sz_987_);
if (v___x_991_ == 0)
{
return v_b_989_;
}
else
{
lean_object* v_snd_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1018_; 
v_snd_992_ = lean_ctor_get(v_b_989_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_b_989_);
if (v_isSharedCheck_1018_ == 0)
{
lean_object* v_unused_1019_; 
v_unused_1019_ = lean_ctor_get(v_b_989_, 0);
lean_dec(v_unused_1019_);
v___x_994_ = v_b_989_;
v_isShared_995_ = v_isSharedCheck_1018_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_snd_992_);
lean_dec(v_b_989_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1018_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v_a_996_; lean_object* v_pos_997_; lean_object* v_endPos_998_; lean_object* v_data_999_; lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v_a_1003_; uint8_t v___x_1010_; 
v_a_996_ = lean_array_uget_borrowed(v_as_986_, v_i_988_);
v_pos_997_ = lean_ctor_get(v_a_996_, 1);
v_endPos_998_ = lean_ctor_get(v_a_996_, 2);
v_data_999_ = lean_ctor_get(v_a_996_, 4);
v___f_1000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitUnknownIdentifierRanges_spec__0_spec__0_spec__2_spec__7___closed__0));
v___x_1001_ = lean_box(0);
lean_inc(v_data_999_);
v___x_1010_ = l_Lean_MessageData_hasTag(v___f_1000_, v_data_999_);
if (v___x_1010_ == 0)
{
v_a_1003_ = v_snd_992_;
goto v___jp_1002_;
}
else
{
lean_object* v___x_1011_; lean_object* v___y_1013_; 
lean_inc_ref(v_pos_997_);
v___x_1011_ = l_Lean_FileMap_ofPosition(v_text_985_, v_pos_997_);
if (lean_obj_tag(v_endPos_998_) == 0)
{
lean_inc_ref(v_pos_997_);
v___y_1013_ = v_pos_997_;
goto v___jp_1012_;
}
else
{
lean_object* v_val_1017_; 
v_val_1017_ = lean_ctor_get(v_endPos_998_, 0);
lean_inc(v_val_1017_);
v___y_1013_ = v_val_1017_;
goto v___jp_1012_;
}
v___jp_1012_:
{
lean_object* v___x_1014_; lean_object* v_msgRange_1015_; lean_object* v_ranges_1016_; 
v___x_1014_ = l_Lean_FileMap_ofPosition(v_text_985_, v___y_1013_);
v_msgRange_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_msgRange_1015_, 0, v___x_1011_);
lean_ctor_set(v_msgRange_1015_, 1, v___x_1014_);
v_ranges_1016_ = lean_array_push(v_snd_992_, v_msgRange_1015_);
v_a_1003_ = v_ranges_1016_;
goto v___jp_1002_;
}
}
v___jp_1002_:
{
lean_object* v___x_1005_; 
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v_a_1003_);
lean_ctor_set(v___x_994_, 0, v___x_1001_);
v___x_1005_ = v___x_994_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1001_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_a_1003_);
v___x_1005_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_add(v_i_988_, v___x_1006_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2_spec__6(v_text_985_, v_as_986_, v_sz_987_, v___x_1007_, v___x_1005_);
return v___x_1008_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2___boxed(lean_object* v_text_1020_, lean_object* v_as_1021_, lean_object* v_sz_1022_, lean_object* v_i_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_){
_start:
{
size_t v_sz_boxed_1026_; size_t v_i_boxed_1027_; lean_object* v_res_1028_; 
v_sz_boxed_1026_ = lean_unbox_usize(v_sz_1022_);
lean_dec(v_sz_1022_);
v_i_boxed_1027_ = lean_unbox_usize(v_i_1023_);
lean_dec(v_i_1023_);
v_res_1028_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_1020_, v_as_1021_, v_sz_boxed_1026_, v_i_boxed_1027_, v_b_1024_);
lean_dec_ref(v_as_1021_);
lean_dec_ref(v_text_1020_);
return v_res_1028_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(lean_object* v_init_1029_, lean_object* v_text_1030_, lean_object* v_n_1031_, lean_object* v_b_1032_){
_start:
{
if (lean_obj_tag(v_n_1031_) == 0)
{
lean_object* v_cs_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1049_; 
v_cs_1034_ = lean_ctor_get(v_n_1031_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_n_1031_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1036_ = v_n_1031_;
v_isShared_1037_ = v_isSharedCheck_1049_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_cs_1034_);
lean_dec(v_n_1031_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1049_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; size_t v_sz_1040_; size_t v___x_1041_; lean_object* v___x_1042_; lean_object* v_fst_1043_; 
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v_b_1032_);
v_sz_1040_ = lean_array_size(v_cs_1034_);
v___x_1041_ = ((size_t)0ULL);
v___x_1042_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_1029_, v_text_1030_, v_cs_1034_, v_sz_1040_, v___x_1041_, v___x_1039_);
lean_dec_ref(v_cs_1034_);
v_fst_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_fst_1043_);
if (lean_obj_tag(v_fst_1043_) == 0)
{
lean_object* v_snd_1044_; lean_object* v___x_1046_; 
v_snd_1044_ = lean_ctor_get(v___x_1042_, 1);
lean_inc(v_snd_1044_);
lean_dec_ref(v___x_1042_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set_tag(v___x_1036_, 1);
lean_ctor_set(v___x_1036_, 0, v_snd_1044_);
v___x_1046_ = v___x_1036_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_snd_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
else
{
lean_object* v_val_1048_; 
lean_dec_ref(v___x_1042_);
lean_del_object(v___x_1036_);
v_val_1048_ = lean_ctor_get(v_fst_1043_, 0);
lean_inc(v_val_1048_);
lean_dec_ref(v_fst_1043_);
return v_val_1048_;
}
}
}
else
{
lean_object* v_vs_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1065_; 
v_vs_1050_ = lean_ctor_get(v_n_1031_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v_n_1031_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1052_ = v_n_1031_;
v_isShared_1053_ = v_isSharedCheck_1065_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_vs_1050_);
lean_dec(v_n_1031_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1065_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; size_t v_sz_1056_; size_t v___x_1057_; lean_object* v___x_1058_; lean_object* v_fst_1059_; 
v___x_1054_ = lean_box(0);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v_b_1032_);
v_sz_1056_ = lean_array_size(v_vs_1050_);
v___x_1057_ = ((size_t)0ULL);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__2(v_text_1030_, v_vs_1050_, v_sz_1056_, v___x_1057_, v___x_1055_);
lean_dec_ref(v_vs_1050_);
v_fst_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_fst_1059_);
if (lean_obj_tag(v_fst_1059_) == 0)
{
lean_object* v_snd_1060_; lean_object* v___x_1062_; 
v_snd_1060_ = lean_ctor_get(v___x_1058_, 1);
lean_inc(v_snd_1060_);
lean_dec_ref(v___x_1058_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 0, v_snd_1060_);
v___x_1062_ = v___x_1052_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_snd_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
else
{
lean_object* v_val_1064_; 
lean_dec_ref(v___x_1058_);
lean_del_object(v___x_1052_);
v_val_1064_ = lean_ctor_get(v_fst_1059_, 0);
lean_inc(v_val_1064_);
lean_dec_ref(v_fst_1059_);
return v_val_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(lean_object* v_init_1066_, lean_object* v_text_1067_, lean_object* v_as_1068_, size_t v_sz_1069_, size_t v_i_1070_, lean_object* v_b_1071_){
_start:
{
uint8_t v___x_1073_; 
v___x_1073_ = lean_usize_dec_lt(v_i_1070_, v_sz_1069_);
if (v___x_1073_ == 0)
{
return v_b_1071_;
}
else
{
lean_object* v_snd_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1092_; 
v_snd_1074_ = lean_ctor_get(v_b_1071_, 1);
v_isSharedCheck_1092_ = !lean_is_exclusive(v_b_1071_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v_b_1071_, 0);
lean_dec(v_unused_1093_);
v___x_1076_ = v_b_1071_;
v_isShared_1077_ = v_isSharedCheck_1092_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_snd_1074_);
lean_dec(v_b_1071_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1092_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_a_1078_; lean_object* v___x_1079_; 
v_a_1078_ = lean_array_uget_borrowed(v_as_1068_, v_i_1070_);
lean_inc(v_snd_1074_);
lean_inc(v_a_1078_);
v___x_1079_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_1066_, v_text_1067_, v_a_1078_, v_snd_1074_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1080_);
v___x_1082_ = v___x_1076_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_snd_1074_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1085_; lean_object* v___x_1087_; 
lean_dec(v_snd_1074_);
v_a_1084_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1084_);
lean_dec_ref(v___x_1079_);
v___x_1085_ = lean_box(0);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v_a_1084_);
lean_ctor_set(v___x_1076_, 0, v___x_1085_);
v___x_1087_ = v___x_1076_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___x_1085_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_a_1084_);
v___x_1087_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
size_t v___x_1088_; size_t v___x_1089_; 
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_add(v_i_1070_, v___x_1088_);
v_i_1070_ = v___x_1089_;
v_b_1071_ = v___x_1087_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1094_, lean_object* v_text_1095_, lean_object* v_as_1096_, lean_object* v_sz_1097_, lean_object* v_i_1098_, lean_object* v_b_1099_, lean_object* v___y_1100_){
_start:
{
size_t v_sz_boxed_1101_; size_t v_i_boxed_1102_; lean_object* v_res_1103_; 
v_sz_boxed_1101_ = lean_unbox_usize(v_sz_1097_);
lean_dec(v_sz_1097_);
v_i_boxed_1102_ = lean_unbox_usize(v_i_1098_);
lean_dec(v_i_1098_);
v_res_1103_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0_spec__1(v_init_1094_, v_text_1095_, v_as_1096_, v_sz_boxed_1101_, v_i_boxed_1102_, v_b_1099_);
lean_dec_ref(v_as_1096_);
lean_dec_ref(v_text_1095_);
lean_dec_ref(v_init_1094_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0___boxed(lean_object* v_init_1104_, lean_object* v_text_1105_, lean_object* v_n_1106_, lean_object* v_b_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_1104_, v_text_1105_, v_n_1106_, v_b_1107_);
lean_dec_ref(v_text_1105_);
lean_dec_ref(v_init_1104_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(lean_object* v_text_1110_, lean_object* v_t_1111_, lean_object* v_init_1112_){
_start:
{
lean_object* v_root_1114_; lean_object* v_tail_1115_; lean_object* v___x_1116_; 
v_root_1114_ = lean_ctor_get(v_t_1111_, 0);
lean_inc_ref(v_root_1114_);
v_tail_1115_ = lean_ctor_get(v_t_1111_, 1);
lean_inc_ref(v_tail_1115_);
lean_dec_ref(v_t_1111_);
lean_inc_ref(v_init_1112_);
v___x_1116_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__0(v_init_1112_, v_text_1110_, v_root_1114_, v_init_1112_);
lean_dec_ref(v_init_1112_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; 
lean_dec_ref(v_tail_1115_);
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v___x_1116_);
return v_a_1117_;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; size_t v_sz_1121_; size_t v___x_1122_; lean_object* v___x_1123_; lean_object* v_fst_1124_; 
v_a_1118_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1118_);
lean_dec_ref(v___x_1116_);
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_a_1118_);
v_sz_1121_ = lean_array_size(v_tail_1115_);
v___x_1122_ = ((size_t)0ULL);
v___x_1123_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0_spec__1(v_text_1110_, v_tail_1115_, v_sz_1121_, v___x_1122_, v___x_1120_);
lean_dec_ref(v_tail_1115_);
v_fst_1124_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_fst_1124_);
if (lean_obj_tag(v_fst_1124_) == 0)
{
lean_object* v_snd_1125_; 
v_snd_1125_ = lean_ctor_get(v___x_1123_, 1);
lean_inc(v_snd_1125_);
lean_dec_ref(v___x_1123_);
return v_snd_1125_;
}
else
{
lean_object* v_val_1126_; 
lean_dec_ref(v___x_1123_);
v_val_1126_ = lean_ctor_get(v_fst_1124_, 0);
lean_inc(v_val_1126_);
lean_dec_ref(v_fst_1124_);
return v_val_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0___boxed(lean_object* v_text_1127_, lean_object* v_t_1128_, lean_object* v_init_1129_, lean_object* v___y_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_1127_, v_t_1128_, v_init_1129_);
lean_dec_ref(v_text_1127_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(size_t v_sz_1132_, size_t v_i_1133_, lean_object* v_bs_1134_){
_start:
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_usize_dec_lt(v_i_1133_, v_sz_1132_);
if (v___x_1135_ == 0)
{
return v_bs_1134_;
}
else
{
lean_object* v_v_1136_; lean_object* v_diagnostics_1137_; lean_object* v_msgLog_1138_; lean_object* v___x_1139_; lean_object* v_bs_x27_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v_v_1136_ = lean_array_uget_borrowed(v_bs_1134_, v_i_1133_);
v_diagnostics_1137_ = lean_ctor_get(v_v_1136_, 1);
v_msgLog_1138_ = lean_ctor_get(v_diagnostics_1137_, 0);
lean_inc_ref(v_msgLog_1138_);
v___x_1139_ = lean_unsigned_to_nat(0u);
v_bs_x27_1140_ = lean_array_uset(v_bs_1134_, v_i_1133_, v___x_1139_);
v___x_1141_ = ((size_t)1ULL);
v___x_1142_ = lean_usize_add(v_i_1133_, v___x_1141_);
v___x_1143_ = lean_array_uset(v_bs_x27_1140_, v_i_1133_, v_msgLog_1138_);
v_i_1133_ = v___x_1142_;
v_bs_1134_ = v___x_1143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2___boxed(lean_object* v_sz_1145_, lean_object* v_i_1146_, lean_object* v_bs_1147_){
_start:
{
size_t v_sz_boxed_1148_; size_t v_i_boxed_1149_; lean_object* v_res_1150_; 
v_sz_boxed_1148_ = lean_unbox_usize(v_sz_1145_);
lean_dec(v_sz_1145_);
v_i_boxed_1149_ = lean_unbox_usize(v_i_1146_);
lean_dec(v_i_1146_);
v_res_1150_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_boxed_1148_, v_i_boxed_1149_, v_bs_1147_);
return v_res_1150_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_unsigned_to_nat(32u);
v___x_1153_ = lean_mk_empty_array_with_capacity(v___x_1152_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2(void){
_start:
{
size_t v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v___x_1155_ = ((size_t)5ULL);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_unsigned_to_nat(32u);
v___x_1158_ = lean_mk_empty_array_with_capacity(v___x_1157_);
v___x_1159_ = lean_obj_once(&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1, &l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1_once, _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__1);
v___x_1160_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___x_1158_);
lean_ctor_set(v___x_1160_, 2, v___x_1156_);
lean_ctor_set(v___x_1160_, 3, v___x_1156_);
lean_ctor_set_usize(v___x_1160_, 4, v___x_1155_);
return v___x_1160_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_NameSet_empty;
v___x_1162_ = lean_obj_once(&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2, &l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once, _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2);
v___x_1163_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1163_, 0, v___x_1162_);
lean_ctor_set(v___x_1163_, 1, v___x_1162_);
lean_ctor_set(v___x_1163_, 2, v___x_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(lean_object* v_doc_1166_){
_start:
{
lean_object* v_toEditableDocumentCore_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1233_; 
v_toEditableDocumentCore_1168_ = lean_ctor_get(v_doc_1166_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v_doc_1166_);
if (v_isSharedCheck_1233_ == 0)
{
lean_object* v_unused_1234_; 
v_unused_1234_ = lean_ctor_get(v_doc_1166_, 1);
lean_dec(v_unused_1234_);
v___x_1170_ = v_doc_1166_;
v_isShared_1171_ = v_isSharedCheck_1233_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_toEditableDocumentCore_1168_);
lean_dec(v_doc_1166_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1233_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_meta_1172_; lean_object* v_initSnap_1173_; lean_object* v_cmdSnaps_1174_; lean_object* v_text_1175_; lean_object* v_unreported_1177_; lean_object* v___y_1185_; lean_object* v_toSnapshot_1187_; lean_object* v_metaSnap_1188_; lean_object* v_result_x3f_1189_; lean_object* v___f_1190_; lean_object* v___y_1192_; 
v_meta_1172_ = lean_ctor_get(v_toEditableDocumentCore_1168_, 0);
lean_inc_ref(v_meta_1172_);
v_initSnap_1173_ = lean_ctor_get(v_toEditableDocumentCore_1168_, 1);
lean_inc_ref(v_initSnap_1173_);
v_cmdSnaps_1174_ = lean_ctor_get(v_toEditableDocumentCore_1168_, 2);
lean_inc(v_cmdSnaps_1174_);
lean_dec_ref(v_toEditableDocumentCore_1168_);
v_text_1175_ = lean_ctor_get(v_meta_1172_, 3);
lean_inc_ref(v_text_1175_);
lean_dec_ref(v_meta_1172_);
v_toSnapshot_1187_ = lean_ctor_get(v_initSnap_1173_, 0);
lean_inc_ref(v_toSnapshot_1187_);
v_metaSnap_1188_ = lean_ctor_get(v_initSnap_1173_, 1);
lean_inc_ref(v_metaSnap_1188_);
v_result_x3f_1189_ = lean_ctor_get(v_initSnap_1173_, 4);
lean_inc(v_result_x3f_1189_);
lean_dec_ref(v_initSnap_1173_);
v___f_1190_ = ((lean_object*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__0));
if (lean_obj_tag(v_result_x3f_1189_) == 0)
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_box(0);
v___y_1192_ = v___x_1218_;
goto v___jp_1191_;
}
else
{
lean_object* v_val_1219_; lean_object* v___x_1221_; uint8_t v_isShared_1222_; uint8_t v_isSharedCheck_1232_; 
v_val_1219_ = lean_ctor_get(v_result_x3f_1189_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v_result_x3f_1189_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1221_ = v_result_x3f_1189_;
v_isShared_1222_ = v_isSharedCheck_1232_;
goto v_resetjp_1220_;
}
else
{
lean_inc(v_val_1219_);
lean_dec(v_result_x3f_1189_);
v___x_1221_ = lean_box(0);
v_isShared_1222_ = v_isSharedCheck_1232_;
goto v_resetjp_1220_;
}
v_resetjp_1220_:
{
lean_object* v_processedSnap_1223_; lean_object* v_stx_x3f_1224_; lean_object* v_reportingRange_1225_; lean_object* v___f_1226_; uint8_t v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1230_; 
v_processedSnap_1223_ = lean_ctor_get(v_val_1219_, 1);
lean_inc_ref(v_processedSnap_1223_);
lean_dec(v_val_1219_);
v_stx_x3f_1224_ = lean_ctor_get(v_processedSnap_1223_, 0);
lean_inc(v_stx_x3f_1224_);
v_reportingRange_1225_ = lean_ctor_get(v_processedSnap_1223_, 1);
lean_inc(v_reportingRange_1225_);
v___f_1226_ = ((lean_object*)(l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__4));
v___x_1227_ = 1;
v___x_1228_ = l_Lean_Language_SnapshotTask_map___redArg(v_processedSnap_1223_, v___f_1226_, v_stx_x3f_1224_, v_reportingRange_1225_, v___x_1227_);
if (v_isShared_1222_ == 0)
{
lean_ctor_set(v___x_1221_, 0, v___x_1228_);
v___x_1230_ = v___x_1221_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v___x_1228_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
v___y_1192_ = v___x_1230_;
goto v___jp_1191_;
}
}
}
v___jp_1176_:
{
lean_object* v_ranges_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v_fst_1182_; lean_object* v___x_1183_; 
v_ranges_1178_ = ((lean_object*)(l_Lean_Server_FileWorker_waitUnknownIdentifierRanges___closed__0));
v___x_1179_ = l_Lean_PersistentArray_forIn___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__0(v_text_1175_, v_unreported_1177_, v_ranges_1178_);
lean_dec_ref(v_text_1175_);
v___x_1180_ = l_IO_AsyncList_waitAll___redArg(v_cmdSnaps_1174_);
v___x_1181_ = lean_task_get_own(v___x_1180_);
v_fst_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc_n(v_fst_1182_, 2);
lean_dec(v___x_1181_);
v___x_1183_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_fst_1182_, v_fst_1182_, v___x_1179_);
lean_dec(v_fst_1182_);
return v___x_1183_;
}
v___jp_1184_:
{
lean_object* v_unreported_1186_; 
v_unreported_1186_ = lean_ctor_get(v___y_1185_, 1);
lean_inc_ref(v_unreported_1186_);
lean_dec_ref(v___y_1185_);
v_unreported_1177_ = v_unreported_1186_;
goto v___jp_1176_;
}
v___jp_1191_:
{
lean_object* v_stx_x3f_1193_; lean_object* v_reportingRange_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v_stx_x3f_1193_ = lean_ctor_get(v_metaSnap_1188_, 0);
lean_inc(v_stx_x3f_1193_);
v_reportingRange_1194_ = lean_ctor_get(v_metaSnap_1188_, 1);
lean_inc(v_reportingRange_1194_);
v___x_1195_ = 1;
v___x_1196_ = l_Lean_Language_SnapshotTask_map___redArg(v_metaSnap_1188_, v___f_1190_, v_stx_x3f_1193_, v_reportingRange_1194_, v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_mk_empty_array_with_capacity(v___x_1197_);
v___x_1199_ = lean_array_push(v___x_1198_, v___x_1196_);
v___x_1200_ = l_Lean_Language_Lean_pushOpt___redArg(v___y_1192_, v___x_1199_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1200_);
lean_ctor_set(v___x_1170_, 0, v_toSnapshot_1187_);
v___x_1202_ = v___x_1170_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v_toSnapshot_1187_);
lean_ctor_set(v_reuseFailAlloc_1217_, 1, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
lean_object* v_snaps_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; size_t v_sz_1207_; size_t v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_snaps_1203_ = l_Lean_Language_SnapshotTree_getAll(v___x_1202_);
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_obj_once(&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2, &l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2_once, _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__2);
v___x_1206_ = lean_obj_once(&l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3, &l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3_once, _init_l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___closed__3);
v_sz_1207_ = lean_array_size(v_snaps_1203_);
v___x_1208_ = ((size_t)0ULL);
v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__2(v_sz_1207_, v___x_1208_, v_snaps_1203_);
v___x_1210_ = lean_array_get_size(v___x_1209_);
v___x_1211_ = lean_nat_dec_lt(v___x_1204_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_dec_ref(v___x_1209_);
v_unreported_1177_ = v___x_1205_;
goto v___jp_1176_;
}
else
{
uint8_t v___x_1212_; 
v___x_1212_ = lean_nat_dec_le(v___x_1210_, v___x_1210_);
if (v___x_1212_ == 0)
{
if (v___x_1211_ == 0)
{
lean_dec_ref(v___x_1209_);
v_unreported_1177_ = v___x_1205_;
goto v___jp_1176_;
}
else
{
size_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1213_ = lean_usize_of_nat(v___x_1210_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_1209_, v___x_1208_, v___x_1213_, v___x_1206_);
lean_dec_ref(v___x_1209_);
v___y_1185_ = v___x_1214_;
goto v___jp_1184_;
}
}
else
{
size_t v___x_1215_; lean_object* v___x_1216_; 
v___x_1215_ = lean_usize_of_nat(v___x_1210_);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__3(v___x_1209_, v___x_1208_, v___x_1215_, v___x_1206_);
lean_dec_ref(v___x_1209_);
v___y_1185_ = v___x_1216_;
goto v___jp_1184_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges___boxed(lean_object* v_doc_1235_, lean_object* v_a_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l_Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges(v_doc_1235_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(lean_object* v_as_1238_, lean_object* v_as_x27_1239_, lean_object* v_b_1240_, lean_object* v_a_1241_){
_start:
{
lean_object* v___x_1243_; 
v___x_1243_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___redArg(v_as_1238_, v_as_x27_1239_, v_b_1240_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1___boxed(lean_object* v_as_1244_, lean_object* v_as_x27_1245_, lean_object* v_b_1246_, lean_object* v_a_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1(v_as_1244_, v_as_x27_1245_, v_b_1246_, v_a_1247_);
lean_dec(v_as_1244_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(lean_object* v_as_1250_, lean_object* v_as_x27_1251_, lean_object* v_b_1252_, lean_object* v_a_1253_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___redArg(v_as_x27_1251_, v_b_1252_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3___boxed(lean_object* v_as_1256_, lean_object* v_as_x27_1257_, lean_object* v_b_1258_, lean_object* v_a_1259_, lean_object* v___y_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean_Server_FileWorker_waitAllUnknownIdentifierMessageRanges_spec__1_spec__3(v_as_1256_, v_as_x27_1257_, v_b_1258_, v_a_1259_);
lean_dec(v_as_1256_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(lean_object* v_b_1264_){
_start:
{
lean_object* v_fst_1265_; lean_object* v_snd_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1282_; 
v_fst_1265_ = lean_ctor_get(v_b_1264_, 0);
v_snd_1266_ = lean_ctor_get(v_b_1264_, 1);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_b_1264_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1268_ = v_b_1264_;
v_isShared_1269_ = v_isSharedCheck_1282_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_snd_1266_);
lean_inc(v_fst_1265_);
lean_dec(v_b_1264_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1282_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
uint8_t v___x_1270_; 
v___x_1270_ = l_Lean_Name_isAnonymous(v_snd_1266_);
if (v___x_1270_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v_openNamespaces_1273_; lean_object* v_currentNamespace_1274_; lean_object* v___x_1276_; 
v___x_1271_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0));
lean_inc(v_snd_1266_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_snd_1266_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v_openNamespaces_1273_ = lean_array_push(v_fst_1265_, v___x_1272_);
v_currentNamespace_1274_ = l_Lean_Name_getPrefix(v_snd_1266_);
lean_dec(v_snd_1266_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 1, v_currentNamespace_1274_);
lean_ctor_set(v___x_1268_, 0, v_openNamespaces_1273_);
v___x_1276_ = v___x_1268_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_openNamespaces_1273_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_currentNamespace_1274_);
v___x_1276_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
v_b_1264_ = v___x_1276_;
goto _start;
}
}
else
{
lean_object* v___x_1280_; 
if (v_isShared_1269_ == 0)
{
v___x_1280_ = v___x_1268_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_fst_1265_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_snd_1266_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
if (lean_obj_tag(v_a_1283_) == 0)
{
lean_object* v___x_1285_; 
v___x_1285_ = l_List_reverse___redArg(v_a_1284_);
return v___x_1285_;
}
else
{
lean_object* v_head_1286_; lean_object* v_tail_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1316_; 
v_head_1286_ = lean_ctor_get(v_a_1283_, 0);
v_tail_1287_ = lean_ctor_get(v_a_1283_, 1);
v_isSharedCheck_1316_ = !lean_is_exclusive(v_a_1283_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1289_ = v_a_1283_;
v_isShared_1290_ = v_isSharedCheck_1316_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_tail_1287_);
lean_inc(v_head_1286_);
lean_dec(v_a_1283_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1316_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___y_1292_; 
if (lean_obj_tag(v_head_1286_) == 0)
{
lean_object* v_ns_1297_; lean_object* v_except_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1306_; 
v_ns_1297_ = lean_ctor_get(v_head_1286_, 0);
v_except_1298_ = lean_ctor_get(v_head_1286_, 1);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_head_1286_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1300_ = v_head_1286_;
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_except_1298_);
lean_inc(v_ns_1297_);
lean_dec(v_head_1286_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = lean_array_mk(v_except_1298_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v___x_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_ns_1297_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
v___y_1292_ = v___x_1304_;
goto v___jp_1291_;
}
}
}
else
{
lean_object* v_id_1307_; lean_object* v_declName_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
v_id_1307_ = lean_ctor_get(v_head_1286_, 0);
v_declName_1308_ = lean_ctor_get(v_head_1286_, 1);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_head_1286_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v_head_1286_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_declName_1308_);
lean_inc(v_id_1307_);
lean_dec(v_head_1286_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 1, v_id_1307_);
lean_ctor_set(v___x_1310_, 0, v_declName_1308_);
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_declName_1308_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_id_1307_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
v___y_1292_ = v___x_1313_;
goto v___jp_1291_;
}
}
}
v___jp_1291_:
{
lean_object* v___x_1294_; 
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 1, v_a_1284_);
lean_ctor_set(v___x_1289_, 0, v___y_1292_);
v___x_1294_ = v___x_1289_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v___y_1292_);
lean_ctor_set(v_reuseFailAlloc_1296_, 1, v_a_1284_);
v___x_1294_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
v_a_1283_ = v_tail_1287_;
v_a_1284_ = v___x_1294_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_collectOpenNamespaces(lean_object* v_currentNamespace_1319_, lean_object* v_openDecls_1320_){
_start:
{
lean_object* v_openNamespaces_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_fst_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v_openNamespaces_1321_ = ((lean_object*)(l_Lean_Server_FileWorker_collectOpenNamespaces___closed__0));
v___x_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_openNamespaces_1321_);
lean_ctor_set(v___x_1322_, 1, v_currentNamespace_1319_);
v___x_1323_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(v___x_1322_);
v_fst_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_fst_1324_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = lean_box(0);
v___x_1326_ = l_List_mapTR_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__1(v_openDecls_1320_, v___x_1325_);
v___x_1327_ = lean_array_mk(v___x_1326_);
v___x_1328_ = l_Array_append___redArg(v_fst_1324_, v___x_1327_);
lean_dec_ref(v___x_1327_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(lean_object* v_doc_1329_, lean_object* v_currNamespace_1330_, lean_object* v_openDecls_1331_, lean_object* v_val_1332_, lean_object* v_val_1333_, uint8_t v___x_1334_, lean_object* v_decl_1335_){
_start:
{
lean_object* v_toEditableDocumentCore_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1360_; 
v_toEditableDocumentCore_1336_ = lean_ctor_get(v_doc_1329_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v_doc_1329_);
if (v_isSharedCheck_1360_ == 0)
{
lean_object* v_unused_1361_; 
v_unused_1361_ = lean_ctor_get(v_doc_1329_, 1);
lean_dec(v_unused_1361_);
v___x_1338_ = v_doc_1329_;
v_isShared_1339_ = v_isSharedCheck_1360_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_toEditableDocumentCore_1336_);
lean_dec(v_doc_1329_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1360_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v_meta_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1356_; 
v_meta_1340_ = lean_ctor_get(v_toEditableDocumentCore_1336_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v_toEditableDocumentCore_1336_);
if (v_isSharedCheck_1356_ == 0)
{
lean_object* v_unused_1357_; lean_object* v_unused_1358_; lean_object* v_unused_1359_; 
v_unused_1357_ = lean_ctor_get(v_toEditableDocumentCore_1336_, 3);
lean_dec(v_unused_1357_);
v_unused_1358_ = lean_ctor_get(v_toEditableDocumentCore_1336_, 2);
lean_dec(v_unused_1358_);
v_unused_1359_ = lean_ctor_get(v_toEditableDocumentCore_1336_, 1);
lean_dec(v_unused_1359_);
v___x_1342_ = v_toEditableDocumentCore_1336_;
v_isShared_1343_ = v_isSharedCheck_1356_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_meta_1340_);
lean_dec(v_toEditableDocumentCore_1336_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1356_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_text_1344_; lean_object* v_minimizedId_1345_; lean_object* v___x_1347_; 
v_text_1344_ = lean_ctor_get(v_meta_1340_, 3);
lean_inc_ref(v_text_1344_);
lean_dec_ref(v_meta_1340_);
v_minimizedId_1345_ = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(v_currNamespace_1330_, v_openDecls_1331_, v_decl_1335_);
if (v_isShared_1339_ == 0)
{
lean_ctor_set(v___x_1338_, 1, v_val_1333_);
lean_ctor_set(v___x_1338_, 0, v_val_1332_);
v___x_1347_ = v___x_1338_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_val_1332_);
lean_ctor_set(v_reuseFailAlloc_1355_, 1, v_val_1333_);
v___x_1347_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1348_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1344_, v___x_1347_);
lean_inc(v_minimizedId_1345_);
v___x_1349_ = l_Lean_Name_toString(v_minimizedId_1345_, v___x_1334_);
v___x_1350_ = lean_box(0);
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 3, v___x_1350_);
lean_ctor_set(v___x_1342_, 2, v___x_1350_);
lean_ctor_set(v___x_1342_, 1, v___x_1349_);
lean_ctor_set(v___x_1342_, 0, v___x_1348_);
v___x_1352_ = v___x_1342_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1354_, 3, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; 
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_minimizedId_1345_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
return v___x_1353_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed(lean_object* v_doc_1362_, lean_object* v_currNamespace_1363_, lean_object* v_openDecls_1364_, lean_object* v_val_1365_, lean_object* v_val_1366_, lean_object* v___x_1367_, lean_object* v_decl_1368_){
_start:
{
uint8_t v___x_172__boxed_1369_; lean_object* v_res_1370_; 
v___x_172__boxed_1369_ = lean_unbox(v___x_1367_);
v_res_1370_ = l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(v_doc_1362_, v_currNamespace_1363_, v_openDecls_1364_, v_val_1365_, v_val_1366_, v___x_172__boxed_1369_, v_decl_1368_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object* v_doc_1371_, lean_object* v_ctx_1372_, lean_object* v_stx_1373_, lean_object* v_id_1374_){
_start:
{
uint8_t v___x_1375_; lean_object* v___x_1376_; 
v___x_1375_ = 1;
v___x_1376_ = l_Lean_Syntax_getPos_x3f(v_stx_1373_, v___x_1375_);
if (lean_obj_tag(v___x_1376_) == 1)
{
lean_object* v_val_1377_; lean_object* v___x_1378_; 
v_val_1377_ = lean_ctor_get(v___x_1376_, 0);
lean_inc(v_val_1377_);
lean_dec_ref(v___x_1376_);
v___x_1378_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1373_, v___x_1375_);
if (lean_obj_tag(v___x_1378_) == 1)
{
lean_object* v_toCommandContextInfo_1379_; lean_object* v_val_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1395_; 
v_toCommandContextInfo_1379_ = lean_ctor_get(v_ctx_1372_, 0);
v_val_1380_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1382_ = v___x_1378_;
v_isShared_1383_ = v_isSharedCheck_1395_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_val_1380_);
lean_dec(v___x_1378_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1395_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v_currNamespace_1384_; lean_object* v_openDecls_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___f_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v_currNamespace_1384_ = lean_ctor_get(v_toCommandContextInfo_1379_, 5);
v_openDecls_1385_ = lean_ctor_get(v_toCommandContextInfo_1379_, 6);
v___x_1386_ = l_Lean_Name_toString(v_id_1374_, v___x_1375_);
v___x_1387_ = lean_box(v___x_1375_);
lean_inc_n(v_openDecls_1385_, 2);
lean_inc_n(v_currNamespace_1384_, 2);
v___f_1388_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1388_, 0, v_doc_1371_);
lean_closure_set(v___f_1388_, 1, v_currNamespace_1384_);
lean_closure_set(v___f_1388_, 2, v_openDecls_1385_);
lean_closure_set(v___f_1388_, 3, v_val_1377_);
lean_closure_set(v___f_1388_, 4, v_val_1380_);
lean_closure_set(v___f_1388_, 5, v___x_1387_);
v___x_1389_ = l_Lean_Server_FileWorker_collectOpenNamespaces(v_currNamespace_1384_, v_openDecls_1385_);
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1386_);
lean_ctor_set(v___x_1390_, 1, v___x_1389_);
v___x_1391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
lean_ctor_set(v___x_1391_, 1, v_ctx_1372_);
lean_ctor_set(v___x_1391_, 2, v___f_1388_);
if (v_isShared_1383_ == 0)
{
lean_ctor_set(v___x_1382_, 0, v___x_1391_);
v___x_1393_ = v___x_1382_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1391_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
else
{
lean_object* v___x_1396_; 
lean_dec(v___x_1378_);
lean_dec(v_val_1377_);
lean_dec(v_id_1374_);
lean_dec_ref(v_ctx_1372_);
lean_dec_ref(v_doc_1371_);
v___x_1396_ = lean_box(0);
return v___x_1396_;
}
}
else
{
lean_object* v___x_1397_; 
lean_dec(v___x_1376_);
lean_dec(v_id_1374_);
lean_dec_ref(v_ctx_1372_);
lean_dec_ref(v_doc_1371_);
v___x_1397_ = lean_box(0);
return v___x_1397_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object* v_doc_1398_, lean_object* v_ctx_1399_, lean_object* v_stx_1400_, lean_object* v_id_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(v_doc_1398_, v_ctx_1399_, v_stx_1400_, v_id_1401_);
lean_dec(v_stx_1400_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(lean_object* v_e_1403_, lean_object* v___y_1404_){
_start:
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Lean_Expr_hasMVar(v_e_1403_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1407_, 0, v_e_1403_);
return v___x_1407_;
}
else
{
lean_object* v___x_1408_; lean_object* v_mctx_1409_; lean_object* v___x_1410_; lean_object* v_fst_1411_; lean_object* v_snd_1412_; lean_object* v___x_1413_; lean_object* v_cache_1414_; lean_object* v_zetaDeltaFVarIds_1415_; lean_object* v_postponed_1416_; lean_object* v_diag_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1426_; 
v___x_1408_ = lean_st_ref_get(v___y_1404_);
v_mctx_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc_ref(v_mctx_1409_);
lean_dec(v___x_1408_);
v___x_1410_ = l_Lean_instantiateMVarsCore(v_mctx_1409_, v_e_1403_);
v_fst_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_fst_1411_);
v_snd_1412_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_snd_1412_);
lean_dec_ref(v___x_1410_);
v___x_1413_ = lean_st_ref_take(v___y_1404_);
v_cache_1414_ = lean_ctor_get(v___x_1413_, 1);
v_zetaDeltaFVarIds_1415_ = lean_ctor_get(v___x_1413_, 2);
v_postponed_1416_ = lean_ctor_get(v___x_1413_, 3);
v_diag_1417_ = lean_ctor_get(v___x_1413_, 4);
v_isSharedCheck_1426_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1426_ == 0)
{
lean_object* v_unused_1427_; 
v_unused_1427_ = lean_ctor_get(v___x_1413_, 0);
lean_dec(v_unused_1427_);
v___x_1419_ = v___x_1413_;
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_diag_1417_);
lean_inc(v_postponed_1416_);
lean_inc(v_zetaDeltaFVarIds_1415_);
lean_inc(v_cache_1414_);
lean_dec(v___x_1413_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1426_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v_snd_1412_);
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v_snd_1412_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_cache_1414_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_zetaDeltaFVarIds_1415_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_postponed_1416_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v_diag_1417_);
v___x_1422_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; 
v___x_1423_ = lean_st_ref_set(v___y_1404_, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1424_, 0, v_fst_1411_);
return v___x_1424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg___boxed(lean_object* v_e_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_1428_, v___y_1429_);
lean_dec(v___y_1429_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(lean_object* v_e_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_1432_, v___y_1434_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(lean_object* v_e_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(v_e_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
lean_dec(v___y_1441_);
lean_dec_ref(v___y_1440_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(lean_object* v_expr_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v___y_1453_; uint8_t v___y_1454_; lean_object* v_a_1459_; lean_object* v___x_1462_; 
lean_inc(v___y_1450_);
lean_inc_ref(v___y_1449_);
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
v___x_1462_ = lean_infer_type(v_expr_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1482_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1462_);
v___x_1464_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_a_1463_, v___y_1448_);
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1467_ = v___x_1464_;
v_isShared_1468_ = v_isSharedCheck_1482_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1464_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1482_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_a_1465_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1480_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1472_ = v___x_1469_;
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1469_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1480_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1468_ == 0)
{
lean_ctor_set_tag(v___x_1467_, 1);
lean_ctor_set(v___x_1467_, 0, v_a_1470_);
v___x_1475_ = v___x_1467_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
lean_object* v___x_1477_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 0, v___x_1475_);
v___x_1477_ = v___x_1472_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v___x_1475_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1481_; 
lean_del_object(v___x_1467_);
v_a_1481_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1481_);
lean_dec_ref(v___x_1469_);
v_a_1459_ = v_a_1481_;
goto v___jp_1458_;
}
}
}
else
{
lean_object* v_a_1483_; 
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
v_a_1483_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v___x_1462_);
v_a_1459_ = v_a_1483_;
goto v___jp_1458_;
}
v___jp_1452_:
{
if (v___y_1454_ == 0)
{
lean_object* v___x_1455_; lean_object* v___x_1456_; 
lean_dec_ref(v___y_1453_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1455_);
return v___x_1456_;
}
else
{
lean_object* v___x_1457_; 
v___x_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___y_1453_);
return v___x_1457_;
}
}
v___jp_1458_:
{
uint8_t v___x_1460_; 
v___x_1460_ = l_Lean_Exception_isInterrupt(v_a_1459_);
if (v___x_1460_ == 0)
{
uint8_t v___x_1461_; 
lean_inc_ref(v_a_1459_);
v___x_1461_ = l_Lean_Exception_isRuntime(v_a_1459_);
v___y_1453_ = v_a_1459_;
v___y_1454_ = v___x_1461_;
goto v___jp_1452_;
}
else
{
v___y_1453_ = v_a_1459_;
v___y_1454_ = v___x_1460_;
goto v___jp_1452_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed(lean_object* v_expr_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(v_expr_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v_res_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1(lean_object* v_val_1491_, lean_object* v_val_1492_, lean_object* v_text_1493_, lean_object* v_decl_1494_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v_val_1491_);
lean_ctor_set(v___x_1495_, 1, v_val_1492_);
v___x_1496_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1493_, v___x_1495_);
v___x_1497_ = l_Lean_Name_getString_x21(v_decl_1494_);
v___x_1498_ = lean_box(0);
v___x_1499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1496_);
lean_ctor_set(v___x_1499_, 1, v___x_1497_);
lean_ctor_set(v___x_1499_, 2, v___x_1498_);
lean_ctor_set(v___x_1499_, 3, v___x_1498_);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_decl_1494_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(size_t v_sz_1501_, size_t v_i_1502_, lean_object* v_bs_1503_){
_start:
{
uint8_t v___x_1504_; 
v___x_1504_ = lean_usize_dec_lt(v_i_1502_, v_sz_1501_);
if (v___x_1504_ == 0)
{
return v_bs_1503_;
}
else
{
lean_object* v_v_1505_; lean_object* v___x_1506_; lean_object* v_bs_x27_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; size_t v___x_1510_; size_t v___x_1511_; lean_object* v___x_1512_; 
v_v_1505_ = lean_array_uget(v_bs_1503_, v_i_1502_);
v___x_1506_ = lean_unsigned_to_nat(0u);
v_bs_x27_1507_ = lean_array_uset(v_bs_1503_, v_i_1502_, v___x_1506_);
v___x_1508_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0));
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_v_1505_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1510_ = ((size_t)1ULL);
v___x_1511_ = lean_usize_add(v_i_1502_, v___x_1510_);
v___x_1512_ = lean_array_uset(v_bs_x27_1507_, v_i_1502_, v___x_1509_);
v_i_1502_ = v___x_1511_;
v_bs_1503_ = v___x_1512_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1___boxed(lean_object* v_sz_1514_, lean_object* v_i_1515_, lean_object* v_bs_1516_){
_start:
{
size_t v_sz_boxed_1517_; size_t v_i_boxed_1518_; lean_object* v_res_1519_; 
v_sz_boxed_1517_ = lean_unbox_usize(v_sz_1514_);
lean_dec(v_sz_1514_);
v_i_boxed_1518_ = lean_unbox_usize(v_i_1515_);
lean_dec(v_i_1515_);
v_res_1519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_boxed_1517_, v_i_boxed_1518_, v_bs_1516_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object* v_doc_1520_, lean_object* v_ctx_1521_, lean_object* v_ti_1522_){
_start:
{
lean_object* v_toElabInfo_1524_; lean_object* v_lctx_1525_; lean_object* v_expr_1526_; lean_object* v_stx_1527_; uint8_t v___x_1528_; lean_object* v___x_1529_; 
v_toElabInfo_1524_ = lean_ctor_get(v_ti_1522_, 0);
lean_inc_ref(v_toElabInfo_1524_);
v_lctx_1525_ = lean_ctor_get(v_ti_1522_, 1);
lean_inc_ref(v_lctx_1525_);
v_expr_1526_ = lean_ctor_get(v_ti_1522_, 3);
lean_inc_ref(v_expr_1526_);
lean_dec_ref(v_ti_1522_);
v_stx_1527_ = lean_ctor_get(v_toElabInfo_1524_, 1);
lean_inc(v_stx_1527_);
lean_dec_ref(v_toElabInfo_1524_);
v___x_1528_ = 1;
v___x_1529_ = l_Lean_Syntax_getPos_x3f(v_stx_1527_, v___x_1528_);
if (lean_obj_tag(v___x_1529_) == 1)
{
lean_object* v_val_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1595_; 
v_val_1530_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1532_ = v___x_1529_;
v_isShared_1533_ = v_isSharedCheck_1595_;
goto v_resetjp_1531_;
}
else
{
lean_inc(v_val_1530_);
lean_dec(v___x_1529_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1595_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1527_, v___x_1528_);
lean_dec(v_stx_1527_);
if (lean_obj_tag(v___x_1534_) == 1)
{
lean_object* v_val_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; 
lean_del_object(v___x_1532_);
v_val_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_val_1535_);
lean_dec_ref(v___x_1534_);
v___f_1536_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1536_, 0, v_expr_1526_);
lean_inc_ref(v_ctx_1521_);
v___x_1537_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1521_, v_lctx_1525_, v___f_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1582_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1540_ = v___x_1537_;
v_isShared_1541_ = v_isSharedCheck_1582_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1537_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1582_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
if (lean_obj_tag(v_a_1538_) == 1)
{
lean_object* v_val_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1577_; 
v_val_1542_ = lean_ctor_get(v_a_1538_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_a_1538_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1544_ = v_a_1538_;
v_isShared_1545_ = v_isSharedCheck_1577_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_val_1542_);
lean_dec(v_a_1538_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1577_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_array_get_size(v_val_1542_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = lean_nat_dec_eq(v___x_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v_toEditableDocumentCore_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1571_; 
v_toEditableDocumentCore_1549_ = lean_ctor_get(v_doc_1520_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v_doc_1520_);
if (v_isSharedCheck_1571_ == 0)
{
lean_object* v_unused_1572_; 
v_unused_1572_ = lean_ctor_get(v_doc_1520_, 1);
lean_dec(v_unused_1572_);
v___x_1551_ = v_doc_1520_;
v_isShared_1552_ = v_isSharedCheck_1571_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_toEditableDocumentCore_1549_);
lean_dec(v_doc_1520_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1571_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v_meta_1553_; lean_object* v_text_1554_; lean_object* v_source_1555_; lean_object* v___f_1556_; lean_object* v___x_1557_; size_t v_sz_1558_; size_t v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1562_; 
v_meta_1553_ = lean_ctor_get(v_toEditableDocumentCore_1549_, 0);
lean_inc_ref(v_meta_1553_);
lean_dec_ref(v_toEditableDocumentCore_1549_);
v_text_1554_ = lean_ctor_get(v_meta_1553_, 3);
lean_inc_ref(v_text_1554_);
lean_dec_ref(v_meta_1553_);
v_source_1555_ = lean_ctor_get(v_text_1554_, 0);
lean_inc_ref(v_source_1555_);
lean_inc(v_val_1535_);
lean_inc(v_val_1530_);
v___f_1556_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(v___f_1556_, 0, v_val_1530_);
lean_closure_set(v___f_1556_, 1, v_val_1535_);
lean_closure_set(v___f_1556_, 2, v_text_1554_);
v___x_1557_ = lean_string_utf8_extract(v_source_1555_, v_val_1530_, v_val_1535_);
lean_dec(v_val_1535_);
lean_dec(v_val_1530_);
lean_dec_ref(v_source_1555_);
v_sz_1558_ = lean_array_size(v_val_1542_);
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_1558_, v___x_1559_, v_val_1542_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 1, v___x_1560_);
lean_ctor_set(v___x_1551_, 0, v___x_1557_);
v___x_1562_ = v___x_1551_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v___x_1560_);
v___x_1562_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
lean_ctor_set(v___x_1563_, 1, v_ctx_1521_);
lean_ctor_set(v___x_1563_, 2, v___f_1556_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1563_);
v___x_1565_ = v___x_1544_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1569_; 
v_reuseFailAlloc_1569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1569_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1569_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1565_);
v___x_1567_ = v___x_1540_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v___x_1565_);
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
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_del_object(v___x_1544_);
lean_dec(v_val_1542_);
lean_dec(v_val_1535_);
lean_dec(v_val_1530_);
lean_dec_ref(v_ctx_1521_);
lean_dec_ref(v_doc_1520_);
v___x_1573_ = lean_box(0);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1573_);
v___x_1575_ = v___x_1540_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_a_1538_);
lean_dec(v_val_1535_);
lean_dec(v_val_1530_);
lean_dec_ref(v_ctx_1521_);
lean_dec_ref(v_doc_1520_);
v___x_1578_ = lean_box(0);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1578_);
v___x_1580_ = v___x_1540_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
else
{
lean_object* v_a_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1590_; 
lean_dec(v_val_1535_);
lean_dec(v_val_1530_);
lean_dec_ref(v_ctx_1521_);
lean_dec_ref(v_doc_1520_);
v_a_1583_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1590_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1585_ = v___x_1537_;
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_a_1583_);
lean_dec(v___x_1537_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1590_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v___x_1588_; 
if (v_isShared_1586_ == 0)
{
v___x_1588_ = v___x_1585_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_a_1583_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
lean_dec(v___x_1534_);
lean_dec(v_val_1530_);
lean_dec_ref(v_expr_1526_);
lean_dec_ref(v_lctx_1525_);
lean_dec_ref(v_ctx_1521_);
lean_dec_ref(v_doc_1520_);
v___x_1591_ = lean_box(0);
if (v_isShared_1533_ == 0)
{
lean_ctor_set_tag(v___x_1532_, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1591_);
v___x_1593_ = v___x_1532_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_dec(v___x_1529_);
lean_dec(v_stx_1527_);
lean_dec_ref(v_expr_1526_);
lean_dec_ref(v_lctx_1525_);
lean_dec_ref(v_ctx_1521_);
lean_dec_ref(v_doc_1520_);
v___x_1596_ = lean_box(0);
v___x_1597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
return v___x_1597_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___boxed(lean_object* v_doc_1598_, lean_object* v_ctx_1599_, lean_object* v_ti_1600_, lean_object* v_a_1601_){
_start:
{
lean_object* v_res_1602_; 
v_res_1602_ = l_Lean_Server_FileWorker_computeDotQuery_x3f(v_doc_1598_, v_ctx_1599_, v_ti_1600_);
return v_res_1602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(lean_object* v_doc_1603_, lean_object* v_val_1604_, lean_object* v_val_1605_, lean_object* v_decl_1606_){
_start:
{
lean_object* v_toEditableDocumentCore_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1630_; 
v_toEditableDocumentCore_1607_ = lean_ctor_get(v_doc_1603_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_doc_1603_);
if (v_isSharedCheck_1630_ == 0)
{
lean_object* v_unused_1631_; 
v_unused_1631_ = lean_ctor_get(v_doc_1603_, 1);
lean_dec(v_unused_1631_);
v___x_1609_ = v_doc_1603_;
v_isShared_1610_ = v_isSharedCheck_1630_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_toEditableDocumentCore_1607_);
lean_dec(v_doc_1603_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1630_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v_meta_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1626_; 
v_meta_1611_ = lean_ctor_get(v_toEditableDocumentCore_1607_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_toEditableDocumentCore_1607_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; lean_object* v_unused_1628_; lean_object* v_unused_1629_; 
v_unused_1627_ = lean_ctor_get(v_toEditableDocumentCore_1607_, 3);
lean_dec(v_unused_1627_);
v_unused_1628_ = lean_ctor_get(v_toEditableDocumentCore_1607_, 2);
lean_dec(v_unused_1628_);
v_unused_1629_ = lean_ctor_get(v_toEditableDocumentCore_1607_, 1);
lean_dec(v_unused_1629_);
v___x_1613_ = v_toEditableDocumentCore_1607_;
v_isShared_1614_ = v_isSharedCheck_1626_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_meta_1611_);
lean_dec(v_toEditableDocumentCore_1607_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1626_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_text_1615_; lean_object* v___x_1617_; 
v_text_1615_ = lean_ctor_get(v_meta_1611_, 3);
lean_inc_ref(v_text_1615_);
lean_dec_ref(v_meta_1611_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 1, v_val_1605_);
lean_ctor_set(v___x_1609_, 0, v_val_1604_);
v___x_1617_ = v___x_1609_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_val_1604_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_val_1605_);
v___x_1617_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1618_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1615_, v___x_1617_);
v___x_1619_ = l_Lean_Name_getString_x21(v_decl_1606_);
v___x_1620_ = lean_box(0);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 3, v___x_1620_);
lean_ctor_set(v___x_1613_, 2, v___x_1620_);
lean_ctor_set(v___x_1613_, 1, v___x_1619_);
lean_ctor_set(v___x_1613_, 0, v___x_1618_);
v___x_1622_ = v___x_1613_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1618_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v___x_1619_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v___x_1620_);
lean_ctor_set(v_reuseFailAlloc_1624_, 3, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1623_, 0, v_decl_1606_);
lean_ctor_set(v___x_1623_, 1, v___x_1622_);
return v___x_1623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object* v_doc_1632_, lean_object* v_ctx_1633_, lean_object* v_stx_1634_, lean_object* v_id_1635_, lean_object* v_lctx_1636_, lean_object* v_expectedType_x3f_1637_){
_start:
{
uint8_t v___x_1639_; lean_object* v___x_1640_; 
v___x_1639_ = 1;
v___x_1640_ = l_Lean_Syntax_getPos_x3f(v_stx_1634_, v___x_1639_);
if (lean_obj_tag(v___x_1640_) == 1)
{
lean_object* v_val_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1700_; 
v_val_1641_ = lean_ctor_get(v___x_1640_, 0);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1640_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1643_ = v___x_1640_;
v_isShared_1644_ = v_isSharedCheck_1700_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_val_1641_);
lean_dec(v___x_1640_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1700_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1634_, v___x_1639_);
if (lean_obj_tag(v___x_1645_) == 1)
{
lean_del_object(v___x_1643_);
if (lean_obj_tag(v_expectedType_x3f_1637_) == 1)
{
lean_object* v_val_1646_; lean_object* v_val_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1686_; 
v_val_1646_ = lean_ctor_get(v___x_1645_, 0);
lean_inc(v_val_1646_);
lean_dec_ref(v___x_1645_);
v_val_1647_ = lean_ctor_get(v_expectedType_x3f_1637_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_expectedType_x3f_1637_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1649_ = v_expectedType_x3f_1637_;
v_isShared_1650_ = v_isSharedCheck_1686_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_val_1647_);
lean_dec(v_expectedType_x3f_1637_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1686_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1651_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getDotIdCompletionTypeNames___boxed), 6, 1);
lean_closure_set(v___x_1651_, 0, v_val_1647_);
lean_inc_ref(v_ctx_1633_);
v___x_1652_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1633_, v_lctx_1636_, v___x_1651_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1677_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1677_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1677_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1657_ = lean_array_get_size(v_a_1653_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_nat_dec_eq(v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___f_1660_; lean_object* v___x_1661_; size_t v_sz_1662_; size_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___f_1660_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0), 4, 3);
lean_closure_set(v___f_1660_, 0, v_doc_1632_);
lean_closure_set(v___f_1660_, 1, v_val_1641_);
lean_closure_set(v___f_1660_, 2, v_val_1646_);
v___x_1661_ = l_Lean_Name_toString(v_id_1635_, v___x_1639_);
v_sz_1662_ = lean_array_size(v_a_1653_);
v___x_1663_ = ((size_t)0ULL);
v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_1662_, v___x_1663_, v_a_1653_);
v___x_1665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1661_);
lean_ctor_set(v___x_1665_, 1, v___x_1664_);
v___x_1666_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1666_, 0, v___x_1665_);
lean_ctor_set(v___x_1666_, 1, v_ctx_1633_);
lean_ctor_set(v___x_1666_, 2, v___f_1660_);
if (v_isShared_1650_ == 0)
{
lean_ctor_set(v___x_1649_, 0, v___x_1666_);
v___x_1668_ = v___x_1649_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
lean_object* v___x_1670_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1668_);
v___x_1670_ = v___x_1655_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1668_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1675_; 
lean_dec(v_a_1653_);
lean_del_object(v___x_1649_);
lean_dec(v_val_1646_);
lean_dec(v_val_1641_);
lean_dec(v_id_1635_);
lean_dec_ref(v_ctx_1633_);
lean_dec_ref(v_doc_1632_);
v___x_1673_ = lean_box(0);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1673_);
v___x_1675_ = v___x_1655_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v___x_1673_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_del_object(v___x_1649_);
lean_dec(v_val_1646_);
lean_dec(v_val_1641_);
lean_dec(v_id_1635_);
lean_dec_ref(v_ctx_1633_);
lean_dec_ref(v_doc_1632_);
v_a_1678_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1652_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1652_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
}
else
{
lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1694_; 
lean_dec(v_val_1641_);
lean_dec(v_expectedType_x3f_1637_);
lean_dec_ref(v_lctx_1636_);
lean_dec(v_id_1635_);
lean_dec_ref(v_ctx_1633_);
lean_dec_ref(v_doc_1632_);
v_isSharedCheck_1694_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1694_ == 0)
{
lean_object* v_unused_1695_; 
v_unused_1695_ = lean_ctor_get(v___x_1645_, 0);
lean_dec(v_unused_1695_);
v___x_1688_ = v___x_1645_;
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
else
{
lean_dec(v___x_1645_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1694_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = lean_box(0);
if (v_isShared_1689_ == 0)
{
lean_ctor_set_tag(v___x_1688_, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
lean_dec(v___x_1645_);
lean_dec(v_val_1641_);
lean_dec(v_expectedType_x3f_1637_);
lean_dec_ref(v_lctx_1636_);
lean_dec(v_id_1635_);
lean_dec_ref(v_ctx_1633_);
lean_dec_ref(v_doc_1632_);
v___x_1696_ = lean_box(0);
if (v_isShared_1644_ == 0)
{
lean_ctor_set_tag(v___x_1643_, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1696_);
v___x_1698_ = v___x_1643_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_dec(v___x_1640_);
lean_dec(v_expectedType_x3f_1637_);
lean_dec_ref(v_lctx_1636_);
lean_dec(v_id_1635_);
lean_dec_ref(v_ctx_1633_);
lean_dec_ref(v_doc_1632_);
v___x_1701_ = lean_box(0);
v___x_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1702_, 0, v___x_1701_);
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object* v_doc_1703_, lean_object* v_ctx_1704_, lean_object* v_stx_1705_, lean_object* v_id_1706_, lean_object* v_lctx_1707_, lean_object* v_expectedType_x3f_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(v_doc_1703_, v_ctx_1704_, v_stx_1705_, v_id_1706_, v_lctx_1707_, v_expectedType_x3f_1708_);
lean_dec(v_stx_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(lean_object* v_doc_1711_, lean_object* v_as_1712_, size_t v_sz_1713_, size_t v_i_1714_, lean_object* v_b_1715_){
_start:
{
lean_object* v_a_1718_; lean_object* v_query_x3f_1723_; uint8_t v___x_1726_; 
v___x_1726_ = lean_usize_dec_lt(v_i_1714_, v_sz_1713_);
if (v___x_1726_ == 0)
{
lean_object* v___x_1727_; 
lean_dec_ref(v_doc_1711_);
v___x_1727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1727_, 0, v_b_1715_);
return v___x_1727_;
}
else
{
lean_object* v_a_1728_; lean_object* v_fst_1729_; lean_object* v_info_1730_; 
v_a_1728_ = lean_array_uget_borrowed(v_as_1712_, v_i_1714_);
v_fst_1729_ = lean_ctor_get(v_a_1728_, 0);
v_info_1730_ = lean_ctor_get(v_fst_1729_, 2);
switch(lean_obj_tag(v_info_1730_))
{
case 1:
{
lean_object* v_ctx_1731_; lean_object* v_stx_1732_; lean_object* v_id_1733_; lean_object* v___x_1734_; 
v_ctx_1731_ = lean_ctor_get(v_fst_1729_, 1);
v_stx_1732_ = lean_ctor_get(v_info_1730_, 0);
v_id_1733_ = lean_ctor_get(v_info_1730_, 1);
lean_inc(v_id_1733_);
lean_inc_ref(v_ctx_1731_);
lean_inc_ref(v_doc_1711_);
v___x_1734_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(v_doc_1711_, v_ctx_1731_, v_stx_1732_, v_id_1733_);
v_query_x3f_1723_ = v___x_1734_;
goto v___jp_1722_;
}
case 0:
{
lean_object* v_ctx_1735_; lean_object* v_termInfo_1736_; lean_object* v___x_1737_; 
v_ctx_1735_ = lean_ctor_get(v_fst_1729_, 1);
v_termInfo_1736_ = lean_ctor_get(v_info_1730_, 0);
lean_inc_ref(v_termInfo_1736_);
lean_inc_ref(v_ctx_1735_);
lean_inc_ref(v_doc_1711_);
v___x_1737_ = l_Lean_Server_FileWorker_computeDotQuery_x3f(v_doc_1711_, v_ctx_1735_, v_termInfo_1736_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v___x_1737_);
v_query_x3f_1723_ = v_a_1738_;
goto v___jp_1722_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1747_; 
lean_dec_ref(v_b_1715_);
lean_dec_ref(v_doc_1711_);
v_a_1739_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1741_ = v___x_1737_;
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1737_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1747_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
v___x_1743_ = l_Lean_Server_RequestError_ofIoError(v_a_1739_);
if (v_isShared_1742_ == 0)
{
lean_ctor_set(v___x_1741_, 0, v___x_1743_);
v___x_1745_ = v___x_1741_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
case 2:
{
lean_object* v_ctx_1748_; lean_object* v_stx_1749_; lean_object* v_id_1750_; lean_object* v_lctx_1751_; lean_object* v_expectedType_x3f_1752_; lean_object* v___x_1753_; 
v_ctx_1748_ = lean_ctor_get(v_fst_1729_, 1);
v_stx_1749_ = lean_ctor_get(v_info_1730_, 0);
v_id_1750_ = lean_ctor_get(v_info_1730_, 1);
v_lctx_1751_ = lean_ctor_get(v_info_1730_, 2);
v_expectedType_x3f_1752_ = lean_ctor_get(v_info_1730_, 3);
lean_inc(v_expectedType_x3f_1752_);
lean_inc_ref(v_lctx_1751_);
lean_inc(v_id_1750_);
lean_inc_ref(v_ctx_1748_);
lean_inc_ref(v_doc_1711_);
v___x_1753_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(v_doc_1711_, v_ctx_1748_, v_stx_1749_, v_id_1750_, v_lctx_1751_, v_expectedType_x3f_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v_query_x3f_1723_ = v_a_1754_;
goto v___jp_1722_;
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1763_; 
lean_dec_ref(v_b_1715_);
lean_dec_ref(v_doc_1711_);
v_a_1755_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1757_ = v___x_1753_;
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1753_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = l_Lean_Server_RequestError_ofIoError(v_a_1755_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 0, v___x_1759_);
v___x_1761_ = v___x_1757_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
default: 
{
v_a_1718_ = v_b_1715_;
goto v___jp_1717_;
}
}
}
v___jp_1717_:
{
size_t v___x_1719_; size_t v___x_1720_; 
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1714_, v___x_1719_);
v_i_1714_ = v___x_1720_;
v_b_1715_ = v_a_1718_;
goto _start;
}
v___jp_1722_:
{
if (lean_obj_tag(v_query_x3f_1723_) == 1)
{
lean_object* v_val_1724_; lean_object* v___x_1725_; 
v_val_1724_ = lean_ctor_get(v_query_x3f_1723_, 0);
lean_inc(v_val_1724_);
lean_dec_ref(v_query_x3f_1723_);
v___x_1725_ = lean_array_push(v_b_1715_, v_val_1724_);
v_a_1718_ = v___x_1725_;
goto v___jp_1717_;
}
else
{
lean_dec(v_query_x3f_1723_);
v_a_1718_ = v_b_1715_;
goto v___jp_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg___boxed(lean_object* v_doc_1764_, lean_object* v_as_1765_, lean_object* v_sz_1766_, lean_object* v_i_1767_, lean_object* v_b_1768_, lean_object* v___y_1769_){
_start:
{
size_t v_sz_boxed_1770_; size_t v_i_boxed_1771_; lean_object* v_res_1772_; 
v_sz_boxed_1770_ = lean_unbox_usize(v_sz_1766_);
lean_dec(v_sz_1766_);
v_i_boxed_1771_ = lean_unbox_usize(v_i_1767_);
lean_dec(v_i_1767_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_1764_, v_as_1765_, v_sz_boxed_1770_, v_i_boxed_1771_, v_b_1768_);
lean_dec_ref(v_as_1765_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(lean_object* v_doc_1773_, lean_object* v_as_1774_, size_t v_sz_1775_, size_t v_i_1776_, lean_object* v_b_1777_, lean_object* v___y_1778_){
_start:
{
uint8_t v___x_1780_; 
v___x_1780_ = lean_usize_dec_lt(v_i_1776_, v_sz_1775_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; 
lean_dec_ref(v_doc_1773_);
v___x_1781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_b_1777_);
return v___x_1781_;
}
else
{
lean_object* v_a_1782_; size_t v_sz_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v_a_1782_ = lean_array_uget_borrowed(v_as_1774_, v_i_1776_);
v_sz_1783_ = lean_array_size(v_a_1782_);
v___x_1784_ = ((size_t)0ULL);
lean_inc_ref(v_doc_1773_);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_1773_, v_a_1782_, v_sz_1783_, v___x_1784_, v_b_1777_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_object* v_a_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_a_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_a_1786_);
v___x_1787_ = lean_array_get_size(v_a_1786_);
v___x_1788_ = lean_unsigned_to_nat(0u);
v___x_1789_ = lean_nat_dec_eq(v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_dec(v_a_1786_);
lean_dec_ref(v_doc_1773_);
return v___x_1785_;
}
else
{
size_t v___x_1790_; size_t v___x_1791_; 
lean_dec_ref(v___x_1785_);
v___x_1790_ = ((size_t)1ULL);
v___x_1791_ = lean_usize_add(v_i_1776_, v___x_1790_);
v_i_1776_ = v___x_1791_;
v_b_1777_ = v_a_1786_;
goto _start;
}
}
else
{
lean_dec_ref(v_doc_1773_);
return v___x_1785_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1___boxed(lean_object* v_doc_1793_, lean_object* v_as_1794_, lean_object* v_sz_1795_, lean_object* v_i_1796_, lean_object* v_b_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_){
_start:
{
size_t v_sz_boxed_1800_; size_t v_i_boxed_1801_; lean_object* v_res_1802_; 
v_sz_boxed_1800_ = lean_unbox_usize(v_sz_1795_);
lean_dec(v_sz_1795_);
v_i_boxed_1801_ = lean_unbox_usize(v_i_1796_);
lean_dec(v_i_1796_);
v_res_1802_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_1793_, v_as_1794_, v_sz_boxed_1800_, v_i_boxed_1801_, v_b_1797_, v___y_1798_);
lean_dec_ref(v___y_1798_);
lean_dec_ref(v_as_1794_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries(lean_object* v_doc_1805_, lean_object* v_requestedPos_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_toEditableDocumentCore_1809_; uint8_t v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; 
v_toEditableDocumentCore_1809_ = lean_ctor_get(v_doc_1805_, 0);
v___x_1810_ = 1;
lean_inc(v_requestedPos_1806_);
lean_inc_ref(v_doc_1805_);
v___x_1811_ = l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_1805_, v_requestedPos_1806_, v___x_1810_);
v___x_1812_ = lean_task_get_own(v___x_1811_);
if (lean_obj_tag(v___x_1812_) == 1)
{
lean_object* v_val_1813_; lean_object* v_meta_1814_; lean_object* v_fst_1815_; lean_object* v_snd_1816_; lean_object* v_text_1817_; lean_object* v___x_1818_; lean_object* v_fst_1819_; lean_object* v_queries_1820_; size_t v_sz_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v_val_1813_ = lean_ctor_get(v___x_1812_, 0);
lean_inc(v_val_1813_);
lean_dec_ref(v___x_1812_);
v_meta_1814_ = lean_ctor_get(v_toEditableDocumentCore_1809_, 0);
v_fst_1815_ = lean_ctor_get(v_val_1813_, 0);
lean_inc(v_fst_1815_);
v_snd_1816_ = lean_ctor_get(v_val_1813_, 1);
lean_inc(v_snd_1816_);
lean_dec(v_val_1813_);
v_text_1817_ = lean_ctor_get(v_meta_1814_, 3);
lean_inc_ref(v_text_1817_);
v___x_1818_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(v_text_1817_, v_requestedPos_1806_, v_fst_1815_, v_snd_1816_);
v_fst_1819_ = lean_ctor_get(v___x_1818_, 0);
lean_inc(v_fst_1819_);
lean_dec_ref(v___x_1818_);
v_queries_1820_ = ((lean_object*)(l_Lean_Server_FileWorker_computeQueries___closed__0));
v_sz_1821_ = lean_array_size(v_fst_1819_);
v___x_1822_ = ((size_t)0ULL);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_1805_, v_fst_1819_, v_sz_1821_, v___x_1822_, v_queries_1820_, v_a_1807_);
lean_dec(v_fst_1819_);
return v___x_1823_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; 
lean_dec(v___x_1812_);
lean_dec(v_requestedPos_1806_);
lean_dec_ref(v_doc_1805_);
v___x_1824_ = ((lean_object*)(l_Lean_Server_FileWorker_computeQueries___closed__0));
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries___boxed(lean_object* v_doc_1826_, lean_object* v_requestedPos_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_){
_start:
{
lean_object* v_res_1830_; 
v_res_1830_ = l_Lean_Server_FileWorker_computeQueries(v_doc_1826_, v_requestedPos_1827_, v_a_1828_);
lean_dec_ref(v_a_1828_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(lean_object* v_doc_1831_, lean_object* v_as_1832_, size_t v_sz_1833_, size_t v_i_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_1831_, v_as_1832_, v_sz_1833_, v_i_1834_, v_b_1835_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___boxed(lean_object* v_doc_1839_, lean_object* v_as_1840_, lean_object* v_sz_1841_, lean_object* v_i_1842_, lean_object* v_b_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
size_t v_sz_boxed_1846_; size_t v_i_boxed_1847_; lean_object* v_res_1848_; 
v_sz_boxed_1846_ = lean_unbox_usize(v_sz_1841_);
lean_dec(v_sz_1841_);
v_i_boxed_1847_ = lean_unbox_usize(v_i_1842_);
lean_dec(v_i_1842_);
v_res_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(v_doc_1839_, v_as_1840_, v_sz_boxed_1846_, v_i_boxed_1847_, v_b_1843_, v___y_1844_);
lean_dec_ref(v___y_1844_);
lean_dec_ref(v_as_1840_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(lean_object* v_params_1857_, lean_object* v_name_1858_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_unsigned_to_nat(0u);
v___x_1860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1860_, 0, v_params_1857_);
lean_ctor_set(v___x_1860_, 1, v_name_1858_);
lean_ctor_set(v___x_1860_, 2, v___x_1859_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object* v_params_1862_, lean_object* v_kind_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1864_ = lean_box(0);
v___x_1865_ = ((lean_object*)(l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0));
v___x_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1866_, 0, v_kind_1863_);
v___x_1867_ = ((lean_object*)(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider));
v___x_1868_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_1862_, v___x_1867_);
v___x_1869_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_1868_);
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
v___x_1871_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1864_);
lean_ctor_set(v___x_1871_, 1, v___x_1864_);
lean_ctor_set(v___x_1871_, 2, v___x_1865_);
lean_ctor_set(v___x_1871_, 3, v___x_1866_);
lean_ctor_set(v___x_1871_, 4, v___x_1864_);
lean_ctor_set(v___x_1871_, 5, v___x_1864_);
lean_ctor_set(v___x_1871_, 6, v___x_1864_);
lean_ctor_set(v___x_1871_, 7, v___x_1864_);
lean_ctor_set(v___x_1871_, 8, v___x_1864_);
lean_ctor_set(v___x_1871_, 9, v___x_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(lean_object* v_ctx_1876_, lean_object* v_mod_1877_){
_start:
{
lean_object* v_toCommandContextInfo_1878_; lean_object* v_parentDecl_x3f_1879_; lean_object* v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v_text_1885_; 
v_toCommandContextInfo_1878_ = lean_ctor_get(v_ctx_1876_, 0);
lean_inc_ref(v_toCommandContextInfo_1878_);
v_parentDecl_x3f_1879_ = lean_ctor_get(v_ctx_1876_, 1);
lean_inc(v_parentDecl_x3f_1879_);
lean_dec_ref(v_ctx_1876_);
v___x_1880_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0));
v___x_1881_ = 1;
v___x_1882_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_1877_, v___x_1881_);
v___x_1883_ = lean_string_append(v___x_1880_, v___x_1882_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1));
v_text_1885_ = lean_string_append(v___x_1883_, v___x_1884_);
if (lean_obj_tag(v_parentDecl_x3f_1879_) == 1)
{
lean_object* v_val_1886_; lean_object* v_env_1887_; uint8_t v___x_1888_; 
v_val_1886_ = lean_ctor_get(v_parentDecl_x3f_1879_, 0);
lean_inc_n(v_val_1886_, 2);
lean_dec_ref(v_parentDecl_x3f_1879_);
v_env_1887_ = lean_ctor_get(v_toCommandContextInfo_1878_, 0);
lean_inc_ref_n(v_env_1887_, 2);
lean_dec_ref(v_toCommandContextInfo_1878_);
v___x_1888_ = l_Lean_isMarkedMeta(v_env_1887_, v_val_1886_);
if (v___x_1888_ == 0)
{
uint8_t v_isExporting_1889_; 
lean_dec(v_val_1886_);
v_isExporting_1889_ = lean_ctor_get_uint8(v_env_1887_, sizeof(void*)*8);
lean_dec_ref(v_env_1887_);
if (v_isExporting_1889_ == 0)
{
return v_text_1885_;
}
else
{
lean_object* v___x_1890_; lean_object* v_text_1891_; 
v___x_1890_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2));
v_text_1891_ = lean_string_append(v___x_1890_, v_text_1885_);
lean_dec_ref(v_text_1885_);
return v_text_1891_;
}
}
else
{
lean_object* v___x_1892_; lean_object* v_text_1893_; uint8_t v___x_1894_; 
lean_dec_ref(v_env_1887_);
v___x_1892_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3));
v_text_1893_ = lean_string_append(v___x_1892_, v_text_1885_);
lean_dec_ref(v_text_1885_);
v___x_1894_ = l_Lean_isPrivateName(v_val_1886_);
lean_dec(v_val_1886_);
if (v___x_1894_ == 0)
{
if (v___x_1888_ == 0)
{
return v_text_1893_;
}
else
{
lean_object* v___x_1895_; lean_object* v_text_1896_; 
v___x_1895_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2));
v_text_1896_ = lean_string_append(v___x_1895_, v_text_1893_);
lean_dec_ref(v_text_1893_);
return v_text_1896_;
}
}
else
{
return v_text_1893_;
}
}
}
else
{
lean_dec(v_parentDecl_x3f_1879_);
lean_dec_ref(v_toCommandContextInfo_1878_);
return v_text_1885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0(lean_object* v_x_1898_){
_start:
{
if (lean_obj_tag(v_x_1898_) == 0)
{
lean_object* v_response_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1917_; 
v_response_1899_ = lean_ctor_get(v_x_1898_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_x_1898_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1901_ = v_x_1898_;
v_isShared_1902_ = v_isSharedCheck_1917_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_response_1899_);
lean_dec(v_x_1898_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1917_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; 
lean_inc(v_response_1899_);
v___x_1903_ = l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(v_response_1899_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_del_object(v___x_1901_);
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref(v___x_1903_);
v___x_1905_ = 0;
v___x_1906_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0));
v___x_1907_ = l_Lean_Json_compress(v_response_1899_);
v___x_1908_ = lean_string_append(v___x_1906_, v___x_1907_);
lean_dec_ref(v___x_1907_);
v___x_1909_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1));
v___x_1910_ = lean_string_append(v___x_1908_, v___x_1909_);
v___x_1911_ = lean_string_append(v___x_1910_, v_a_1904_);
lean_dec(v_a_1904_);
v___x_1912_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set_uint8(v___x_1912_, sizeof(void*)*1, v___x_1905_);
return v___x_1912_;
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; 
lean_dec(v_response_1899_);
v_a_1913_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1913_);
lean_dec_ref(v___x_1903_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v_a_1913_);
v___x_1915_ = v___x_1901_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1913_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
else
{
uint8_t v_code_1918_; lean_object* v_message_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
v_code_1918_ = lean_ctor_get_uint8(v_x_1898_, sizeof(void*)*1);
v_message_1919_ = lean_ctor_get(v_x_1898_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v_x_1898_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v_x_1898_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_message_1919_);
lean_dec(v_x_1898_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_message_1919_);
lean_ctor_set_uint8(v_reuseFailAlloc_1925_, sizeof(void*)*1, v_code_1918_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(lean_object* v_method_1928_, lean_object* v_param_1929_, lean_object* v_a_1930_){
_start:
{
lean_object* v_serverRequestEmitter_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___f_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v_serverRequestEmitter_1932_ = lean_ctor_get(v_a_1930_, 5);
v___x_1933_ = l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(v_param_1929_);
lean_inc_ref(v_serverRequestEmitter_1932_);
v___x_1934_ = lean_apply_3(v_serverRequestEmitter_1932_, v_method_1928_, v___x_1933_, lean_box(0));
v___f_1935_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0));
v___x_1936_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1935_, v___x_1934_);
v___x_1937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___boxed(lean_object* v_method_1938_, lean_object* v_param_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v_method_1938_, v_param_1939_, v_a_1940_);
lean_dec_ref(v_a_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(lean_object* v_val_1943_){
_start:
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v_val_1943_);
return v___x_1944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(lean_object* v_val_1945_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_val_1945_);
return v___x_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(size_t v_sz_1947_, size_t v_i_1948_, lean_object* v_bs_1949_){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_usize_dec_lt(v_i_1948_, v_sz_1947_);
if (v___x_1950_ == 0)
{
return v_bs_1949_;
}
else
{
lean_object* v_v_1951_; lean_object* v_toLeanModuleQuery_1952_; lean_object* v___x_1953_; lean_object* v_bs_x27_1954_; size_t v___x_1955_; size_t v___x_1956_; lean_object* v___x_1957_; 
v_v_1951_ = lean_array_uget_borrowed(v_bs_1949_, v_i_1948_);
v_toLeanModuleQuery_1952_ = lean_ctor_get(v_v_1951_, 0);
lean_inc_ref(v_toLeanModuleQuery_1952_);
v___x_1953_ = lean_unsigned_to_nat(0u);
v_bs_x27_1954_ = lean_array_uset(v_bs_1949_, v_i_1948_, v___x_1953_);
v___x_1955_ = ((size_t)1ULL);
v___x_1956_ = lean_usize_add(v_i_1948_, v___x_1955_);
v___x_1957_ = lean_array_uset(v_bs_x27_1954_, v_i_1948_, v_toLeanModuleQuery_1952_);
v_i_1948_ = v___x_1956_;
v_bs_1949_ = v___x_1957_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0___boxed(lean_object* v_sz_1959_, lean_object* v_i_1960_, lean_object* v_bs_1961_){
_start:
{
size_t v_sz_boxed_1962_; size_t v_i_boxed_1963_; lean_object* v_res_1964_; 
v_sz_boxed_1962_ = lean_unbox_usize(v_sz_1959_);
lean_dec(v_sz_1959_);
v_i_boxed_1963_ = lean_unbox_usize(v_i_1960_);
lean_dec(v_i_1960_);
v_res_1964_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_boxed_1962_, v_i_boxed_1963_, v_bs_1961_);
return v_res_1964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(lean_object* v_a_1968_, lean_object* v_kind_1969_, lean_object* v___x_1970_, lean_object* v_params_1971_, lean_object* v___x_1972_, lean_object* v___x_1973_, lean_object* v_as_1974_, size_t v_sz_1975_, size_t v_i_1976_, lean_object* v_b_1977_){
_start:
{
lean_object* v_a_1980_; uint8_t v___x_1984_; 
v___x_1984_ = lean_usize_dec_lt(v_i_1976_, v_sz_1975_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_dec_ref(v___x_1972_);
lean_dec_ref(v_params_1971_);
lean_dec_ref(v___x_1970_);
lean_dec_ref(v_kind_1969_);
lean_dec_ref(v_a_1968_);
v___x_1985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1985_, 0, v_b_1977_);
return v___x_1985_;
}
else
{
lean_object* v_a_1986_; lean_object* v_module_1987_; lean_object* v_decl_1988_; uint8_t v_isExactMatch_1989_; lean_object* v_fst_1990_; lean_object* v_snd_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_2082_; 
v_a_1986_ = lean_array_uget_borrowed(v_as_1974_, v_i_1976_);
v_module_1987_ = lean_ctor_get(v_a_1986_, 0);
v_decl_1988_ = lean_ctor_get(v_a_1986_, 1);
v_isExactMatch_1989_ = lean_ctor_get_uint8(v_a_1986_, sizeof(void*)*2);
v_fst_1990_ = lean_ctor_get(v_b_1977_, 0);
v_snd_1991_ = lean_ctor_get(v_b_1977_, 1);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_b_1977_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_1993_ = v_b_1977_;
v_isShared_1994_ = v_isSharedCheck_2082_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_snd_1991_);
lean_inc(v_fst_1990_);
lean_dec(v_b_1977_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_2082_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v_ctx_1995_; lean_object* v_determineInsertion_1996_; uint8_t v___y_1998_; uint8_t v___y_1999_; lean_object* v_toCommandContextInfo_2073_; lean_object* v_env_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; uint8_t v___y_2078_; uint8_t v___x_2081_; 
v_ctx_1995_ = lean_ctor_get(v_a_1968_, 1);
v_determineInsertion_1996_ = lean_ctor_get(v_a_1968_, 2);
v_toCommandContextInfo_2073_ = lean_ctor_get(v_ctx_1995_, 0);
v_env_2074_ = lean_ctor_get(v_toCommandContextInfo_2073_, 0);
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = lean_nat_dec_eq(v___x_1973_, v___x_2075_);
lean_inc(v_decl_1988_);
lean_inc_ref(v_env_2074_);
v___x_2081_ = l_Lean_Environment_contains(v_env_2074_, v_decl_1988_, v___x_1984_);
if (v___x_2081_ == 0)
{
v___y_2078_ = v___x_1984_;
goto v___jp_2077_;
}
else
{
v___y_2078_ = v___x_2076_;
goto v___jp_2077_;
}
v___jp_1997_:
{
if (v___y_1999_ == 0)
{
lean_object* v___x_2000_; 
lean_inc_ref(v_determineInsertion_1996_);
lean_inc(v_decl_1988_);
v___x_2000_ = lean_apply_1(v_determineInsertion_1996_, v_decl_1988_);
if (v___y_1998_ == 0)
{
lean_object* v_fullName_2001_; lean_object* v_edit_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2029_; 
v_fullName_2001_ = lean_ctor_get(v___x_2000_, 0);
v_edit_2002_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2004_ = v___x_2000_;
v_isShared_2005_ = v_isSharedCheck_2029_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_edit_2002_);
lean_inc(v_fullName_2001_);
lean_dec(v___x_2000_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2029_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2006_ = lean_box(0);
v___x_2007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0));
v___x_2008_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fullName_2001_, v___x_1984_);
v___x_2009_ = lean_string_append(v___x_2007_, v___x_2008_);
lean_dec_ref(v___x_2008_);
lean_inc_ref(v_kind_1969_);
v___x_2010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_kind_1969_);
lean_inc_ref(v___x_1970_);
v___x_2011_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_1970_);
v___x_2012_ = lean_unsigned_to_nat(1u);
v___x_2013_ = lean_mk_empty_array_with_capacity(v___x_2012_);
v___x_2014_ = lean_array_push(v___x_2013_, v_edit_2002_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v___x_2014_);
lean_ctor_set(v___x_2004_, 0, v___x_2011_);
v___x_2016_ = v___x_2004_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2011_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2014_);
v___x_2016_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2026_; 
v___x_2017_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_2016_);
v___x_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
v___x_2019_ = ((lean_object*)(l_Lean_Server_FileWorker_importUnknownIdentifiersProvider));
lean_inc_ref(v_params_1971_);
v___x_2020_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_1971_, v___x_2019_);
v___x_2021_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_2020_);
v___x_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
v___x_2023_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2006_);
lean_ctor_set(v___x_2023_, 1, v___x_2006_);
lean_ctor_set(v___x_2023_, 2, v___x_2009_);
lean_ctor_set(v___x_2023_, 3, v___x_2010_);
lean_ctor_set(v___x_2023_, 4, v___x_2006_);
lean_ctor_set(v___x_2023_, 5, v___x_2006_);
lean_ctor_set(v___x_2023_, 6, v___x_2006_);
lean_ctor_set(v___x_2023_, 7, v___x_2018_);
lean_ctor_set(v___x_2023_, 8, v___x_2006_);
lean_ctor_set(v___x_2023_, 9, v___x_2022_);
v___x_2024_ = lean_array_push(v_fst_1990_, v___x_2023_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2024_);
v___x_2026_ = v___x_1993_;
goto v_reusejp_2025_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2024_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v_snd_1991_);
v___x_2026_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2025_;
}
v_reusejp_2025_:
{
v_a_1980_ = v___x_2026_;
goto v___jp_1979_;
}
}
}
}
else
{
lean_object* v_fullName_2030_; lean_object* v_edit_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2069_; 
v_fullName_2030_ = lean_ctor_get(v___x_2000_, 0);
v_edit_2031_ = lean_ctor_get(v___x_2000_, 1);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2033_ = v___x_2000_;
v_isShared_2034_ = v_isSharedCheck_2069_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_edit_2031_);
lean_inc(v_fullName_2030_);
lean_dec(v___x_2000_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2069_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2052_; 
v___x_2035_ = lean_box(0);
v___x_2036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1));
v___x_2037_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fullName_2030_, v___y_1998_);
v___x_2038_ = lean_string_append(v___x_2036_, v___x_2037_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2));
v___x_2040_ = lean_string_append(v___x_2038_, v___x_2039_);
lean_inc_n(v_module_1987_, 2);
v___x_2041_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_1987_, v___y_1998_);
v___x_2042_ = lean_string_append(v___x_2040_, v___x_2041_);
lean_dec_ref(v___x_2041_);
lean_inc_ref(v_kind_1969_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v_kind_1969_);
lean_inc_ref(v___x_1970_);
v___x_2044_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_1970_);
lean_inc_ref(v_ctx_1995_);
v___x_2045_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_1995_, v_module_1987_);
lean_inc_ref(v___x_1972_);
v___x_2046_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2046_, 0, v___x_1972_);
lean_ctor_set(v___x_2046_, 1, v___x_2045_);
lean_ctor_set(v___x_2046_, 2, v___x_2035_);
lean_ctor_set(v___x_2046_, 3, v___x_2035_);
v___x_2047_ = lean_unsigned_to_nat(2u);
v___x_2048_ = lean_mk_empty_array_with_capacity(v___x_2047_);
v___x_2049_ = lean_array_push(v___x_2048_, v___x_2046_);
v___x_2050_ = lean_array_push(v___x_2049_, v_edit_2031_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v___x_2050_);
lean_ctor_set(v___x_2033_, 0, v___x_2044_);
v___x_2052_ = v___x_2033_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2044_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___x_2050_);
v___x_2052_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v___x_2053_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_2052_);
v___x_2054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
v___x_2055_ = ((lean_object*)(l_Lean_Server_FileWorker_importUnknownIdentifiersProvider));
lean_inc_ref(v_params_1971_);
v___x_2056_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_1971_, v___x_2055_);
v___x_2057_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_2056_);
v___x_2058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
v___x_2059_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2059_, 0, v___x_2035_);
lean_ctor_set(v___x_2059_, 1, v___x_2035_);
lean_ctor_set(v___x_2059_, 2, v___x_2042_);
lean_ctor_set(v___x_2059_, 3, v___x_2043_);
lean_ctor_set(v___x_2059_, 4, v___x_2035_);
lean_ctor_set(v___x_2059_, 5, v___x_2035_);
lean_ctor_set(v___x_2059_, 6, v___x_2035_);
lean_ctor_set(v___x_2059_, 7, v___x_2054_);
lean_ctor_set(v___x_2059_, 8, v___x_2035_);
lean_ctor_set(v___x_2059_, 9, v___x_2058_);
v___x_2060_ = lean_array_push(v_fst_1990_, v___x_2059_);
if (v_isExactMatch_1989_ == 0)
{
lean_object* v___x_2062_; 
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 0, v___x_2060_);
v___x_2062_ = v___x_1993_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2063_, 1, v_snd_1991_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
v_a_1980_ = v___x_2062_;
goto v___jp_1979_;
}
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2066_; 
lean_dec(v_snd_1991_);
v___x_2064_ = lean_box(v___x_1984_);
if (v_isShared_1994_ == 0)
{
lean_ctor_set(v___x_1993_, 1, v___x_2064_);
lean_ctor_set(v___x_1993_, 0, v___x_2060_);
v___x_2066_ = v___x_1993_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2064_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
v_a_1980_ = v___x_2066_;
goto v___jp_1979_;
}
}
}
}
}
}
else
{
lean_object* v___x_2071_; 
if (v_isShared_1994_ == 0)
{
v___x_2071_ = v___x_1993_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_fst_1990_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_snd_1991_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
v_a_1980_ = v___x_2071_;
goto v___jp_1979_;
}
}
}
v___jp_2077_:
{
if (v___y_2078_ == 0)
{
v___y_1998_ = v___y_2078_;
v___y_1999_ = v___x_2076_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2079_; uint8_t v___x_2080_; 
v___x_2079_ = l_Lean_Environment_mainModule(v_env_2074_);
v___x_2080_ = lean_name_eq(v_module_1987_, v___x_2079_);
lean_dec(v___x_2079_);
v___y_1998_ = v___y_2078_;
v___y_1999_ = v___x_2080_;
goto v___jp_1997_;
}
}
}
}
v___jp_1979_:
{
size_t v___x_1981_; size_t v___x_1982_; 
v___x_1981_ = ((size_t)1ULL);
v___x_1982_ = lean_usize_add(v_i_1976_, v___x_1981_);
v_i_1976_ = v___x_1982_;
v_b_1977_ = v_a_1980_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___boxed(lean_object* v_a_2083_, lean_object* v_kind_2084_, lean_object* v___x_2085_, lean_object* v_params_2086_, lean_object* v___x_2087_, lean_object* v___x_2088_, lean_object* v_as_2089_, lean_object* v_sz_2090_, lean_object* v_i_2091_, lean_object* v_b_2092_, lean_object* v___y_2093_){
_start:
{
size_t v_sz_boxed_2094_; size_t v_i_boxed_2095_; lean_object* v_res_2096_; 
v_sz_boxed_2094_ = lean_unbox_usize(v_sz_2090_);
lean_dec(v_sz_2090_);
v_i_boxed_2095_ = lean_unbox_usize(v_i_2091_);
lean_dec(v_i_2091_);
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_2083_, v_kind_2084_, v___x_2085_, v_params_2086_, v___x_2087_, v___x_2088_, v_as_2089_, v_sz_boxed_2094_, v_i_boxed_2095_, v_b_2092_);
lean_dec_ref(v_as_2089_);
lean_dec(v___x_2088_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(lean_object* v_kind_2097_, lean_object* v___x_2098_, lean_object* v_params_2099_, lean_object* v___x_2100_, lean_object* v___x_2101_, lean_object* v_as_2102_, size_t v_sz_2103_, size_t v_i_2104_, lean_object* v_b_2105_, lean_object* v___y_2106_){
_start:
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_usize_dec_lt(v_i_2104_, v_sz_2103_);
if (v___x_2108_ == 0)
{
lean_object* v___x_2109_; 
lean_dec_ref(v___x_2100_);
lean_dec_ref(v_params_2099_);
lean_dec_ref(v___x_2098_);
lean_dec_ref(v_kind_2097_);
v___x_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2109_, 0, v_b_2105_);
return v___x_2109_;
}
else
{
lean_object* v_snd_2110_; lean_object* v_snd_2111_; lean_object* v_fst_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2177_; 
v_snd_2110_ = lean_ctor_get(v_b_2105_, 1);
lean_inc(v_snd_2110_);
v_snd_2111_ = lean_ctor_get(v_snd_2110_, 1);
lean_inc(v_snd_2111_);
v_fst_2112_ = lean_ctor_get(v_b_2105_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_b_2105_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v_b_2105_, 1);
lean_dec(v_unused_2178_);
v___x_2114_ = v_b_2105_;
v_isShared_2115_ = v_isSharedCheck_2177_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_fst_2112_);
lean_dec(v_b_2105_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2177_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_fst_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2175_; 
v_fst_2116_ = lean_ctor_get(v_snd_2110_, 0);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_snd_2110_);
if (v_isSharedCheck_2175_ == 0)
{
lean_object* v_unused_2176_; 
v_unused_2176_ = lean_ctor_get(v_snd_2110_, 1);
lean_dec(v_unused_2176_);
v___x_2118_ = v_snd_2110_;
v_isShared_2119_ = v_isSharedCheck_2175_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_fst_2116_);
lean_dec(v_snd_2110_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2175_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v_array_2120_; lean_object* v_start_2121_; lean_object* v_stop_2122_; uint8_t v___x_2123_; 
v_array_2120_ = lean_ctor_get(v_snd_2111_, 0);
v_start_2121_ = lean_ctor_get(v_snd_2111_, 1);
v_stop_2122_ = lean_ctor_get(v_snd_2111_, 2);
v___x_2123_ = lean_nat_dec_lt(v_start_2121_, v_stop_2122_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2125_; 
lean_dec_ref(v___x_2100_);
lean_dec_ref(v_params_2099_);
lean_dec_ref(v___x_2098_);
lean_dec_ref(v_kind_2097_);
if (v_isShared_2119_ == 0)
{
v___x_2125_ = v___x_2118_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_fst_2116_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_snd_2111_);
v___x_2125_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
lean_object* v___x_2127_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v___x_2125_);
v___x_2127_ = v___x_2114_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_fst_2112_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
return v___x_2128_;
}
}
}
else
{
lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2171_; 
lean_inc(v_stop_2122_);
lean_inc(v_start_2121_);
lean_inc_ref(v_array_2120_);
v_isSharedCheck_2171_ = !lean_is_exclusive(v_snd_2111_);
if (v_isSharedCheck_2171_ == 0)
{
lean_object* v_unused_2172_; lean_object* v_unused_2173_; lean_object* v_unused_2174_; 
v_unused_2172_ = lean_ctor_get(v_snd_2111_, 2);
lean_dec(v_unused_2172_);
v_unused_2173_ = lean_ctor_get(v_snd_2111_, 1);
lean_dec(v_unused_2173_);
v_unused_2174_ = lean_ctor_get(v_snd_2111_, 0);
lean_dec(v_unused_2174_);
v___x_2132_ = v_snd_2111_;
v_isShared_2133_ = v_isSharedCheck_2171_;
goto v_resetjp_2131_;
}
else
{
lean_dec(v_snd_2111_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2171_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v_a_2134_; lean_object* v___x_2135_; lean_object* v___x_2137_; 
v_a_2134_ = lean_array_uget_borrowed(v_as_2102_, v_i_2104_);
v___x_2135_ = lean_array_fget_borrowed(v_array_2120_, v_start_2121_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 1, v_fst_2116_);
lean_ctor_set(v___x_2118_, 0, v_fst_2112_);
v___x_2137_ = v___x_2118_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_fst_2112_);
lean_ctor_set(v_reuseFailAlloc_2170_, 1, v_fst_2116_);
v___x_2137_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
size_t v_sz_2138_; size_t v___x_2139_; lean_object* v___x_2140_; 
v_sz_2138_ = lean_array_size(v___x_2135_);
v___x_2139_ = ((size_t)0ULL);
lean_inc_ref(v___x_2100_);
lean_inc_ref(v_params_2099_);
lean_inc_ref(v___x_2098_);
lean_inc_ref(v_kind_2097_);
lean_inc(v_a_2134_);
v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_2134_, v_kind_2097_, v___x_2098_, v_params_2099_, v___x_2100_, v___x_2101_, v___x_2135_, v_sz_2138_, v___x_2139_, v___x_2137_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v_fst_2142_; lean_object* v_snd_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2161_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref(v___x_2140_);
v_fst_2142_ = lean_ctor_get(v_a_2141_, 0);
v_snd_2143_ = lean_ctor_get(v_a_2141_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_a_2141_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2145_ = v_a_2141_;
v_isShared_2146_ = v_isSharedCheck_2161_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_snd_2143_);
lean_inc(v_fst_2142_);
lean_dec(v_a_2141_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2161_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2147_ = lean_unsigned_to_nat(1u);
v___x_2148_ = lean_nat_add(v_start_2121_, v___x_2147_);
lean_dec(v_start_2121_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v___x_2148_);
v___x_2150_ = v___x_2132_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_array_2120_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_stop_2122_);
v___x_2150_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v___x_2150_);
lean_ctor_set(v___x_2145_, 0, v_snd_2143_);
v___x_2152_ = v___x_2145_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_snd_2143_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2150_);
v___x_2152_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2154_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 1, v___x_2152_);
lean_ctor_set(v___x_2114_, 0, v_fst_2142_);
v___x_2154_ = v___x_2114_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_fst_2142_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
size_t v___x_2155_; size_t v___x_2156_; 
v___x_2155_ = ((size_t)1ULL);
v___x_2156_ = lean_usize_add(v_i_2104_, v___x_2155_);
v_i_2104_ = v___x_2156_;
v_b_2105_ = v___x_2154_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_del_object(v___x_2132_);
lean_dec(v_stop_2122_);
lean_dec(v_start_2121_);
lean_dec_ref(v_array_2120_);
lean_del_object(v___x_2114_);
lean_dec_ref(v___x_2100_);
lean_dec_ref(v_params_2099_);
lean_dec_ref(v___x_2098_);
lean_dec_ref(v_kind_2097_);
v_a_2162_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2140_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2140_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2167_; 
if (v_isShared_2165_ == 0)
{
v___x_2167_ = v___x_2164_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___boxed(lean_object* v_kind_2179_, lean_object* v___x_2180_, lean_object* v_params_2181_, lean_object* v___x_2182_, lean_object* v___x_2183_, lean_object* v_as_2184_, lean_object* v_sz_2185_, lean_object* v_i_2186_, lean_object* v_b_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
size_t v_sz_boxed_2190_; size_t v_i_boxed_2191_; lean_object* v_res_2192_; 
v_sz_boxed_2190_ = lean_unbox_usize(v_sz_2185_);
lean_dec(v_sz_2185_);
v_i_boxed_2191_ = lean_unbox_usize(v_i_2186_);
lean_dec(v_i_2186_);
v_res_2192_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_2179_, v___x_2180_, v_params_2181_, v___x_2182_, v___x_2183_, v_as_2184_, v_sz_boxed_2190_, v_i_boxed_2191_, v_b_2187_, v___y_2188_);
lean_dec_ref(v___y_2188_);
lean_dec_ref(v_as_2184_);
lean_dec(v___x_2183_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object* v_id_2201_, lean_object* v_params_2202_, lean_object* v_requestedRange_2203_, lean_object* v_kind_2204_, lean_object* v_a_2205_){
_start:
{
lean_object* v_doc_2207_; lean_object* v_cancelTk_2208_; lean_object* v_toEditableDocumentCore_2209_; lean_object* v_stop_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2339_; 
v_doc_2207_ = lean_ctor_get(v_a_2205_, 1);
v_cancelTk_2208_ = lean_ctor_get(v_a_2205_, 4);
v_toEditableDocumentCore_2209_ = lean_ctor_get(v_doc_2207_, 0);
v_stop_2210_ = lean_ctor_get(v_requestedRange_2203_, 1);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_requestedRange_2203_);
if (v_isSharedCheck_2339_ == 0)
{
lean_object* v_unused_2340_; 
v_unused_2340_ = lean_ctor_get(v_requestedRange_2203_, 0);
lean_dec(v_unused_2340_);
v___x_2212_ = v_requestedRange_2203_;
v_isShared_2213_ = v_isSharedCheck_2339_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_stop_2210_);
lean_dec(v_requestedRange_2203_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2339_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; 
lean_inc_ref(v_doc_2207_);
v___x_2214_ = l_Lean_Server_FileWorker_computeQueries(v_doc_2207_, v_stop_2210_, v_a_2205_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2330_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2330_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2330_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; 
v___x_2219_ = lean_array_get_size(v_a_2215_);
v___x_2220_ = lean_unsigned_to_nat(0u);
v___x_2221_ = lean_nat_dec_eq(v___x_2219_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; size_t v_sz_2223_; size_t v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
lean_del_object(v___x_2217_);
v___x_2222_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0));
v_sz_2223_ = lean_array_size(v_a_2215_);
v___x_2224_ = ((size_t)0ULL);
lean_inc(v_a_2215_);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_2223_, v___x_2224_, v_a_2215_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 1, v___x_2225_);
lean_ctor_set(v___x_2212_, 0, v_id_2201_);
v___x_2227_ = v___x_2212_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_id_2201_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
lean_object* v___x_2228_; lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2324_; 
v___x_2228_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_2222_, v___x_2227_, v_a_2205_);
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2324_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2324_ == 0)
{
v___x_2231_ = v___x_2228_;
v_isShared_2232_ = v_isSharedCheck_2324_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2228_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2324_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___f_2233_; lean_object* v___f_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___y_2243_; 
v___f_2233_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1));
v___f_2234_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2));
v___x_2235_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2233_, v_a_2229_);
v___x_2236_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_cancelTk_2208_);
v___x_2237_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2234_, v___x_2236_);
v___x_2238_ = lean_box(0);
v___x_2239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2239_, 0, v___x_2237_);
lean_ctor_set(v___x_2239_, 1, v___x_2238_);
v___x_2240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2240_, 0, v___x_2235_);
lean_ctor_set(v___x_2240_, 1, v___x_2239_);
v___x_2241_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_2240_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_val_2262_; 
v_val_2262_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_val_2262_);
lean_dec_ref(v___x_2241_);
if (lean_obj_tag(v_val_2262_) == 0)
{
lean_object* v_response_2263_; lean_object* v___y_2265_; lean_object* v_initSnap_2305_; lean_object* v_meta_2306_; lean_object* v_stx_2307_; lean_object* v___x_2308_; 
v_response_2263_ = lean_ctor_get(v_val_2262_, 0);
lean_inc(v_response_2263_);
lean_dec_ref(v_val_2262_);
v_initSnap_2305_ = lean_ctor_get(v_toEditableDocumentCore_2209_, 1);
v_meta_2306_ = lean_ctor_get(v_toEditableDocumentCore_2209_, 0);
v_stx_2307_ = lean_ctor_get(v_initSnap_2305_, 3);
v___x_2308_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2307_, v___x_2221_);
if (lean_obj_tag(v___x_2308_) == 0)
{
lean_object* v___x_2309_; 
v___x_2309_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5));
v___y_2265_ = v___x_2309_;
goto v___jp_2264_;
}
else
{
lean_object* v_val_2310_; lean_object* v_text_2311_; lean_object* v___x_2312_; lean_object* v_line_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2322_; 
v_val_2310_ = lean_ctor_get(v___x_2308_, 0);
lean_inc(v_val_2310_);
lean_dec_ref(v___x_2308_);
v_text_2311_ = lean_ctor_get(v_meta_2306_, 3);
lean_inc_ref(v_text_2311_);
v___x_2312_ = l_Lean_FileMap_utf8PosToLspPos(v_text_2311_, v_val_2310_);
lean_dec(v_val_2310_);
v_line_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2322_ == 0)
{
lean_object* v_unused_2323_; 
v_unused_2323_ = lean_ctor_get(v___x_2312_, 1);
lean_dec(v_unused_2323_);
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_line_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_nat_add(v_line_2313_, v___x_2317_);
lean_dec(v_line_2313_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v___x_2220_);
lean_ctor_set(v___x_2315_, 0, v___x_2318_);
v___x_2320_ = v___x_2315_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2318_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v___x_2220_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
v___y_2265_ = v___x_2320_;
goto v___jp_2264_;
}
}
}
v___jp_2264_:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
lean_inc_ref(v___y_2265_);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___y_2265_);
lean_ctor_set(v___x_2266_, 1, v___y_2265_);
v___x_2267_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3));
v___x_2268_ = lean_array_get_size(v_response_2263_);
v___x_2269_ = lean_nat_dec_lt(v___x_2220_, v___x_2268_);
if (v___x_2269_ == 0)
{
lean_object* v___x_2271_; 
lean_dec_ref(v___x_2266_);
lean_dec(v_response_2263_);
lean_dec(v_a_2215_);
lean_dec_ref(v_kind_2204_);
lean_dec_ref(v_params_2202_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 0, v___x_2267_);
v___x_2271_ = v___x_2231_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v___x_2267_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
else
{
lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_del_object(v___x_2231_);
v___x_2273_ = l_Array_toSubarray___redArg(v_response_2263_, v___x_2220_, v___x_2268_);
v___x_2274_ = lean_box(v___x_2221_);
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_2273_);
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2267_);
lean_ctor_set(v___x_2276_, 1, v___x_2275_);
lean_inc_ref(v_params_2202_);
lean_inc_ref(v_doc_2207_);
v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_2204_, v_doc_2207_, v_params_2202_, v___x_2266_, v___x_2219_, v_a_2215_, v_sz_2223_, v___x_2224_, v___x_2276_, v_a_2205_);
lean_dec(v_a_2215_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2296_; 
v_a_2278_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2280_ = v___x_2277_;
v_isShared_2281_ = v_isSharedCheck_2296_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2277_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2296_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v_snd_2282_; lean_object* v_fst_2283_; uint8_t v___x_2284_; 
v_snd_2282_ = lean_ctor_get(v_a_2278_, 1);
v_fst_2283_ = lean_ctor_get(v_snd_2282_, 0);
v___x_2284_ = lean_unbox(v_fst_2283_);
if (v___x_2284_ == 0)
{
lean_object* v_fst_2285_; lean_object* v___x_2287_; 
lean_dec_ref(v_params_2202_);
v_fst_2285_ = lean_ctor_get(v_a_2278_, 0);
lean_inc(v_fst_2285_);
lean_dec(v_a_2278_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v_fst_2285_);
v___x_2287_ = v___x_2280_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_fst_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
else
{
lean_object* v_fst_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v_fst_2289_ = lean_ctor_get(v_a_2278_, 0);
lean_inc(v_fst_2289_);
lean_dec(v_a_2278_);
v___x_2290_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4));
v___x_2291_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(v_params_2202_, v___x_2290_);
v___x_2292_ = lean_array_push(v_fst_2289_, v___x_2291_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2292_);
v___x_2294_ = v___x_2280_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_dec_ref(v_params_2202_);
v_a_2297_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2277_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2277_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2262_);
lean_del_object(v___x_2231_);
lean_dec(v_a_2215_);
lean_dec_ref(v_kind_2204_);
lean_dec_ref(v_params_2202_);
v___y_2243_ = v_a_2205_;
goto v___jp_2242_;
}
}
else
{
lean_dec(v___x_2241_);
lean_del_object(v___x_2231_);
lean_dec(v_a_2215_);
lean_dec_ref(v_kind_2204_);
lean_dec_ref(v_params_2202_);
v___y_2243_ = v_a_2205_;
goto v___jp_2242_;
}
v___jp_2242_:
{
lean_object* v___x_2244_; 
v___x_2244_ = l_Lean_Server_RequestM_checkCancelled(v___y_2243_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2252_; 
v_isSharedCheck_2252_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; 
v_unused_2253_ = lean_ctor_get(v___x_2244_, 0);
lean_dec(v_unused_2253_);
v___x_2246_ = v___x_2244_;
v_isShared_2247_ = v_isSharedCheck_2252_;
goto v_resetjp_2245_;
}
else
{
lean_dec(v___x_2244_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2252_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3));
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 0, v___x_2248_);
v___x_2250_ = v___x_2246_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v___x_2248_);
v___x_2250_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
return v___x_2250_;
}
}
}
else
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2261_; 
v_a_2254_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2256_ = v___x_2244_;
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2244_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2261_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2259_; 
if (v_isShared_2257_ == 0)
{
v___x_2259_ = v___x_2256_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2254_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
lean_dec(v_a_2215_);
lean_del_object(v___x_2212_);
lean_dec_ref(v_kind_2204_);
lean_dec_ref(v_params_2202_);
lean_dec(v_id_2201_);
v___x_2326_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3));
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v___x_2326_);
v___x_2328_ = v___x_2217_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
return v___x_2328_;
}
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_del_object(v___x_2212_);
lean_dec_ref(v_kind_2204_);
lean_dec_ref(v_params_2202_);
lean_dec(v_id_2201_);
v_a_2331_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2214_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2214_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___boxed(lean_object* v_id_2341_, lean_object* v_params_2342_, lean_object* v_requestedRange_2343_, lean_object* v_kind_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v_res_2347_; 
v_res_2347_ = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(v_id_2341_, v_params_2342_, v_requestedRange_2343_, v_kind_2344_, v_a_2345_);
lean_dec_ref(v_a_2345_);
return v_res_2347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(lean_object* v_a_2348_, lean_object* v_kind_2349_, lean_object* v___x_2350_, lean_object* v_params_2351_, lean_object* v___x_2352_, lean_object* v___x_2353_, lean_object* v_as_2354_, size_t v_sz_2355_, size_t v_i_2356_, lean_object* v_b_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; 
v___x_2360_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_2348_, v_kind_2349_, v___x_2350_, v_params_2351_, v___x_2352_, v___x_2353_, v_as_2354_, v_sz_2355_, v_i_2356_, v_b_2357_);
return v___x_2360_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(lean_object* v_a_2361_, lean_object* v_kind_2362_, lean_object* v___x_2363_, lean_object* v_params_2364_, lean_object* v___x_2365_, lean_object* v___x_2366_, lean_object* v_as_2367_, lean_object* v_sz_2368_, lean_object* v_i_2369_, lean_object* v_b_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
size_t v_sz_boxed_2373_; size_t v_i_boxed_2374_; lean_object* v_res_2375_; 
v_sz_boxed_2373_ = lean_unbox_usize(v_sz_2368_);
lean_dec(v_sz_2368_);
v_i_boxed_2374_ = lean_unbox_usize(v_i_2369_);
lean_dec(v_i_2369_);
v_res_2375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(v_a_2361_, v_kind_2362_, v___x_2363_, v_params_2364_, v___x_2365_, v___x_2366_, v_as_2367_, v_sz_boxed_2373_, v_i_boxed_2374_, v_b_2370_, v___y_2371_);
lean_dec_ref(v___y_2371_);
lean_dec_ref(v_as_2367_);
lean_dec(v___x_2366_);
return v_res_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(lean_object* v_a_2379_, lean_object* v_as_2380_, size_t v_sz_2381_, size_t v_i_2382_, lean_object* v_b_2383_){
_start:
{
lean_object* v_a_2385_; uint8_t v___x_2389_; 
v___x_2389_ = lean_usize_dec_lt(v_i_2382_, v_sz_2381_);
if (v___x_2389_ == 0)
{
lean_dec_ref(v_a_2379_);
lean_inc_ref(v_b_2383_);
return v_b_2383_;
}
else
{
lean_object* v_a_2390_; lean_object* v_decl_2391_; uint8_t v_isExactMatch_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; 
v_a_2390_ = lean_array_uget_borrowed(v_as_2380_, v_i_2382_);
v_decl_2391_ = lean_ctor_get(v_a_2390_, 1);
v_isExactMatch_2392_ = lean_ctor_get_uint8(v_a_2390_, sizeof(void*)*2);
v___x_2393_ = lean_box(0);
v___x_2394_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0));
if (v_isExactMatch_2392_ == 0)
{
v_a_2385_ = v___x_2394_;
goto v___jp_2384_;
}
else
{
lean_object* v_ctx_2395_; lean_object* v_toCommandContextInfo_2396_; lean_object* v_env_2397_; uint8_t v___x_2398_; 
v_ctx_2395_ = lean_ctor_get(v_a_2379_, 1);
v_toCommandContextInfo_2396_ = lean_ctor_get(v_ctx_2395_, 0);
v_env_2397_ = lean_ctor_get(v_toCommandContextInfo_2396_, 0);
lean_inc(v_decl_2391_);
lean_inc_ref(v_env_2397_);
v___x_2398_ = l_Lean_Environment_contains(v_env_2397_, v_decl_2391_, v_isExactMatch_2392_);
if (v___x_2398_ == 0)
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
lean_dec_ref(v_a_2379_);
lean_inc(v_a_2390_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v_a_2390_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
v___x_2401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2400_);
lean_ctor_set(v___x_2401_, 1, v___x_2393_);
return v___x_2401_;
}
else
{
v_a_2385_ = v___x_2394_;
goto v___jp_2384_;
}
}
}
v___jp_2384_:
{
size_t v___x_2386_; size_t v___x_2387_; 
v___x_2386_ = ((size_t)1ULL);
v___x_2387_ = lean_usize_add(v_i_2382_, v___x_2386_);
v_i_2382_ = v___x_2387_;
v_b_2383_ = v_a_2385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___boxed(lean_object* v_a_2402_, lean_object* v_as_2403_, lean_object* v_sz_2404_, lean_object* v_i_2405_, lean_object* v_b_2406_){
_start:
{
size_t v_sz_boxed_2407_; size_t v_i_boxed_2408_; lean_object* v_res_2409_; 
v_sz_boxed_2407_ = lean_unbox_usize(v_sz_2404_);
lean_dec(v_sz_2404_);
v_i_boxed_2408_ = lean_unbox_usize(v_i_2405_);
lean_dec(v_i_2405_);
v_res_2409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_2402_, v_as_2403_, v_sz_boxed_2407_, v_i_boxed_2408_, v_b_2406_);
lean_dec_ref(v_b_2406_);
lean_dec_ref(v_as_2403_);
return v_res_2409_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(lean_object* v_a_2410_, lean_object* v_x_2411_){
_start:
{
if (lean_obj_tag(v_x_2411_) == 0)
{
uint8_t v___x_2412_; 
v___x_2412_ = 0;
return v___x_2412_;
}
else
{
lean_object* v_key_2413_; lean_object* v_tail_2414_; uint8_t v___x_2415_; 
v_key_2413_ = lean_ctor_get(v_x_2411_, 0);
v_tail_2414_ = lean_ctor_get(v_x_2411_, 2);
v___x_2415_ = lean_name_eq(v_key_2413_, v_a_2410_);
if (v___x_2415_ == 0)
{
v_x_2411_ = v_tail_2414_;
goto _start;
}
else
{
return v___x_2415_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_a_2417_, lean_object* v_x_2418_){
_start:
{
uint8_t v_res_2419_; lean_object* v_r_2420_; 
v_res_2419_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2417_, v_x_2418_);
lean_dec(v_x_2418_);
lean_dec(v_a_2417_);
v_r_2420_ = lean_box(v_res_2419_);
return v_r_2420_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2421_; uint64_t v___x_2422_; 
v___x_2421_ = lean_unsigned_to_nat(1723u);
v___x_2422_ = lean_uint64_of_nat(v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(lean_object* v_m_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v_buckets_2425_; lean_object* v___x_2426_; uint64_t v___y_2428_; 
v_buckets_2425_ = lean_ctor_get(v_m_2423_, 1);
v___x_2426_ = lean_array_get_size(v_buckets_2425_);
if (lean_obj_tag(v_a_2424_) == 0)
{
uint64_t v___x_2442_; 
v___x_2442_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
v___y_2428_ = v___x_2442_;
goto v___jp_2427_;
}
else
{
uint64_t v_hash_2443_; 
v_hash_2443_ = lean_ctor_get_uint64(v_a_2424_, sizeof(void*)*2);
v___y_2428_ = v_hash_2443_;
goto v___jp_2427_;
}
v___jp_2427_:
{
uint64_t v___x_2429_; uint64_t v___x_2430_; uint64_t v_fold_2431_; uint64_t v___x_2432_; uint64_t v___x_2433_; uint64_t v___x_2434_; size_t v___x_2435_; size_t v___x_2436_; size_t v___x_2437_; size_t v___x_2438_; size_t v___x_2439_; lean_object* v___x_2440_; uint8_t v___x_2441_; 
v___x_2429_ = 32ULL;
v___x_2430_ = lean_uint64_shift_right(v___y_2428_, v___x_2429_);
v_fold_2431_ = lean_uint64_xor(v___y_2428_, v___x_2430_);
v___x_2432_ = 16ULL;
v___x_2433_ = lean_uint64_shift_right(v_fold_2431_, v___x_2432_);
v___x_2434_ = lean_uint64_xor(v_fold_2431_, v___x_2433_);
v___x_2435_ = lean_uint64_to_usize(v___x_2434_);
v___x_2436_ = lean_usize_of_nat(v___x_2426_);
v___x_2437_ = ((size_t)1ULL);
v___x_2438_ = lean_usize_sub(v___x_2436_, v___x_2437_);
v___x_2439_ = lean_usize_land(v___x_2435_, v___x_2438_);
v___x_2440_ = lean_array_uget_borrowed(v_buckets_2425_, v___x_2439_);
v___x_2441_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2424_, v___x_2440_);
return v___x_2441_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___boxed(lean_object* v_m_2444_, lean_object* v_a_2445_){
_start:
{
uint8_t v_res_2446_; lean_object* v_r_2447_; 
v_res_2446_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_2444_, v_a_2445_);
lean_dec(v_a_2445_);
lean_dec_ref(v_m_2444_);
v_r_2447_ = lean_box(v_res_2446_);
return v_r_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2448_, lean_object* v_x_2449_){
_start:
{
if (lean_obj_tag(v_x_2449_) == 0)
{
return v_x_2448_;
}
else
{
lean_object* v_key_2450_; lean_object* v_value_2451_; lean_object* v_tail_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2478_; 
v_key_2450_ = lean_ctor_get(v_x_2449_, 0);
v_value_2451_ = lean_ctor_get(v_x_2449_, 1);
v_tail_2452_ = lean_ctor_get(v_x_2449_, 2);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_x_2449_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2454_ = v_x_2449_;
v_isShared_2455_ = v_isSharedCheck_2478_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_tail_2452_);
lean_inc(v_value_2451_);
lean_inc(v_key_2450_);
lean_dec(v_x_2449_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2478_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; uint64_t v___y_2458_; 
v___x_2456_ = lean_array_get_size(v_x_2448_);
if (lean_obj_tag(v_key_2450_) == 0)
{
uint64_t v___x_2476_; 
v___x_2476_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
v___y_2458_ = v___x_2476_;
goto v___jp_2457_;
}
else
{
uint64_t v_hash_2477_; 
v_hash_2477_ = lean_ctor_get_uint64(v_key_2450_, sizeof(void*)*2);
v___y_2458_ = v_hash_2477_;
goto v___jp_2457_;
}
v___jp_2457_:
{
uint64_t v___x_2459_; uint64_t v___x_2460_; uint64_t v_fold_2461_; uint64_t v___x_2462_; uint64_t v___x_2463_; uint64_t v___x_2464_; size_t v___x_2465_; size_t v___x_2466_; size_t v___x_2467_; size_t v___x_2468_; size_t v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2472_; 
v___x_2459_ = 32ULL;
v___x_2460_ = lean_uint64_shift_right(v___y_2458_, v___x_2459_);
v_fold_2461_ = lean_uint64_xor(v___y_2458_, v___x_2460_);
v___x_2462_ = 16ULL;
v___x_2463_ = lean_uint64_shift_right(v_fold_2461_, v___x_2462_);
v___x_2464_ = lean_uint64_xor(v_fold_2461_, v___x_2463_);
v___x_2465_ = lean_uint64_to_usize(v___x_2464_);
v___x_2466_ = lean_usize_of_nat(v___x_2456_);
v___x_2467_ = ((size_t)1ULL);
v___x_2468_ = lean_usize_sub(v___x_2466_, v___x_2467_);
v___x_2469_ = lean_usize_land(v___x_2465_, v___x_2468_);
v___x_2470_ = lean_array_uget_borrowed(v_x_2448_, v___x_2469_);
lean_inc(v___x_2470_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 2, v___x_2470_);
v___x_2472_ = v___x_2454_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_key_2450_);
lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_value_2451_);
lean_ctor_set(v_reuseFailAlloc_2475_, 2, v___x_2470_);
v___x_2472_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_array_uset(v_x_2448_, v___x_2469_, v___x_2472_);
v_x_2448_ = v___x_2473_;
v_x_2449_ = v_tail_2452_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2479_, lean_object* v_source_2480_, lean_object* v_target_2481_){
_start:
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = lean_array_get_size(v_source_2480_);
v___x_2483_ = lean_nat_dec_lt(v_i_2479_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_dec_ref(v_source_2480_);
lean_dec(v_i_2479_);
return v_target_2481_;
}
else
{
lean_object* v_es_2484_; lean_object* v___x_2485_; lean_object* v_source_2486_; lean_object* v_target_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v_es_2484_ = lean_array_fget(v_source_2480_, v_i_2479_);
v___x_2485_ = lean_box(0);
v_source_2486_ = lean_array_fset(v_source_2480_, v_i_2479_, v___x_2485_);
v_target_2487_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_target_2481_, v_es_2484_);
v___x_2488_ = lean_unsigned_to_nat(1u);
v___x_2489_ = lean_nat_add(v_i_2479_, v___x_2488_);
lean_dec(v_i_2479_);
v_i_2479_ = v___x_2489_;
v_source_2480_ = v_source_2486_;
v_target_2481_ = v_target_2487_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(lean_object* v_data_2491_){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v_nbuckets_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2492_ = lean_array_get_size(v_data_2491_);
v___x_2493_ = lean_unsigned_to_nat(2u);
v_nbuckets_2494_ = lean_nat_mul(v___x_2492_, v___x_2493_);
v___x_2495_ = lean_unsigned_to_nat(0u);
v___x_2496_ = lean_box(0);
v___x_2497_ = lean_mk_array(v_nbuckets_2494_, v___x_2496_);
v___x_2498_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v___x_2495_, v_data_2491_, v___x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(lean_object* v_m_2499_, lean_object* v_a_2500_, lean_object* v_b_2501_){
_start:
{
lean_object* v_size_2502_; lean_object* v_buckets_2503_; lean_object* v___x_2504_; uint64_t v___y_2506_; 
v_size_2502_ = lean_ctor_get(v_m_2499_, 0);
v_buckets_2503_ = lean_ctor_get(v_m_2499_, 1);
v___x_2504_ = lean_array_get_size(v_buckets_2503_);
if (lean_obj_tag(v_a_2500_) == 0)
{
uint64_t v___x_2543_; 
v___x_2543_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
v___y_2506_ = v___x_2543_;
goto v___jp_2505_;
}
else
{
uint64_t v_hash_2544_; 
v_hash_2544_ = lean_ctor_get_uint64(v_a_2500_, sizeof(void*)*2);
v___y_2506_ = v_hash_2544_;
goto v___jp_2505_;
}
v___jp_2505_:
{
uint64_t v___x_2507_; uint64_t v___x_2508_; uint64_t v_fold_2509_; uint64_t v___x_2510_; uint64_t v___x_2511_; uint64_t v___x_2512_; size_t v___x_2513_; size_t v___x_2514_; size_t v___x_2515_; size_t v___x_2516_; size_t v___x_2517_; lean_object* v_bkt_2518_; uint8_t v___x_2519_; 
v___x_2507_ = 32ULL;
v___x_2508_ = lean_uint64_shift_right(v___y_2506_, v___x_2507_);
v_fold_2509_ = lean_uint64_xor(v___y_2506_, v___x_2508_);
v___x_2510_ = 16ULL;
v___x_2511_ = lean_uint64_shift_right(v_fold_2509_, v___x_2510_);
v___x_2512_ = lean_uint64_xor(v_fold_2509_, v___x_2511_);
v___x_2513_ = lean_uint64_to_usize(v___x_2512_);
v___x_2514_ = lean_usize_of_nat(v___x_2504_);
v___x_2515_ = ((size_t)1ULL);
v___x_2516_ = lean_usize_sub(v___x_2514_, v___x_2515_);
v___x_2517_ = lean_usize_land(v___x_2513_, v___x_2516_);
v_bkt_2518_ = lean_array_uget_borrowed(v_buckets_2503_, v___x_2517_);
v___x_2519_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2500_, v_bkt_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2540_; 
lean_inc_ref(v_buckets_2503_);
lean_inc(v_size_2502_);
v_isSharedCheck_2540_ = !lean_is_exclusive(v_m_2499_);
if (v_isSharedCheck_2540_ == 0)
{
lean_object* v_unused_2541_; lean_object* v_unused_2542_; 
v_unused_2541_ = lean_ctor_get(v_m_2499_, 1);
lean_dec(v_unused_2541_);
v_unused_2542_ = lean_ctor_get(v_m_2499_, 0);
lean_dec(v_unused_2542_);
v___x_2521_ = v_m_2499_;
v_isShared_2522_ = v_isSharedCheck_2540_;
goto v_resetjp_2520_;
}
else
{
lean_dec(v_m_2499_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2540_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v_size_x27_2524_; lean_object* v___x_2525_; lean_object* v_buckets_x27_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; uint8_t v___x_2532_; 
v___x_2523_ = lean_unsigned_to_nat(1u);
v_size_x27_2524_ = lean_nat_add(v_size_2502_, v___x_2523_);
lean_dec(v_size_2502_);
lean_inc(v_bkt_2518_);
v___x_2525_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2525_, 0, v_a_2500_);
lean_ctor_set(v___x_2525_, 1, v_b_2501_);
lean_ctor_set(v___x_2525_, 2, v_bkt_2518_);
v_buckets_x27_2526_ = lean_array_uset(v_buckets_2503_, v___x_2517_, v___x_2525_);
v___x_2527_ = lean_unsigned_to_nat(4u);
v___x_2528_ = lean_nat_mul(v_size_x27_2524_, v___x_2527_);
v___x_2529_ = lean_unsigned_to_nat(3u);
v___x_2530_ = lean_nat_div(v___x_2528_, v___x_2529_);
lean_dec(v___x_2528_);
v___x_2531_ = lean_array_get_size(v_buckets_x27_2526_);
v___x_2532_ = lean_nat_dec_le(v___x_2530_, v___x_2531_);
lean_dec(v___x_2530_);
if (v___x_2532_ == 0)
{
lean_object* v_val_2533_; lean_object* v___x_2535_; 
v_val_2533_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_buckets_x27_2526_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v_val_2533_);
lean_ctor_set(v___x_2521_, 0, v_size_x27_2524_);
v___x_2535_ = v___x_2521_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_size_x27_2524_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v_val_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
else
{
lean_object* v___x_2538_; 
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v_buckets_x27_2526_);
lean_ctor_set(v___x_2521_, 0, v_size_x27_2524_);
v___x_2538_ = v___x_2521_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_size_x27_2524_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_buckets_x27_2526_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
else
{
lean_dec(v_b_2501_);
lean_dec(v_a_2500_);
return v_m_2499_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(lean_object* v___x_2545_, lean_object* v_as_2546_, size_t v_sz_2547_, size_t v_i_2548_, lean_object* v_b_2549_){
_start:
{
lean_object* v_a_2552_; uint8_t v___x_2556_; 
v___x_2556_ = lean_usize_dec_lt(v_i_2548_, v_sz_2547_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; 
lean_dec_ref(v___x_2545_);
v___x_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2557_, 0, v_b_2549_);
return v___x_2557_;
}
else
{
lean_object* v_snd_2558_; lean_object* v_snd_2559_; lean_object* v_fst_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2650_; 
v_snd_2558_ = lean_ctor_get(v_b_2549_, 1);
lean_inc(v_snd_2558_);
v_snd_2559_ = lean_ctor_get(v_snd_2558_, 1);
lean_inc(v_snd_2559_);
v_fst_2560_ = lean_ctor_get(v_b_2549_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_b_2549_);
if (v_isSharedCheck_2650_ == 0)
{
lean_object* v_unused_2651_; 
v_unused_2651_ = lean_ctor_get(v_b_2549_, 1);
lean_dec(v_unused_2651_);
v___x_2562_ = v_b_2549_;
v_isShared_2563_ = v_isSharedCheck_2650_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_fst_2560_);
lean_dec(v_b_2549_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2650_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v_fst_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2648_; 
v_fst_2564_ = lean_ctor_get(v_snd_2558_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_snd_2558_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v_snd_2558_, 1);
lean_dec(v_unused_2649_);
v___x_2566_ = v_snd_2558_;
v_isShared_2567_ = v_isSharedCheck_2648_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_fst_2564_);
lean_dec(v_snd_2558_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2648_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v_array_2568_; lean_object* v_start_2569_; lean_object* v_stop_2570_; uint8_t v___x_2571_; 
v_array_2568_ = lean_ctor_get(v_snd_2559_, 0);
v_start_2569_ = lean_ctor_get(v_snd_2559_, 1);
v_stop_2570_ = lean_ctor_get(v_snd_2559_, 2);
v___x_2571_ = lean_nat_dec_lt(v_start_2569_, v_stop_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2573_; 
lean_dec_ref(v___x_2545_);
if (v_isShared_2567_ == 0)
{
v___x_2573_ = v___x_2566_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_fst_2564_);
lean_ctor_set(v_reuseFailAlloc_2578_, 1, v_snd_2559_);
v___x_2573_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_object* v___x_2575_; 
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v___x_2573_);
v___x_2575_ = v___x_2562_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2577_; 
v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_fst_2560_);
lean_ctor_set(v_reuseFailAlloc_2577_, 1, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2577_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
lean_object* v___x_2576_; 
v___x_2576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2576_, 0, v___x_2575_);
return v___x_2576_;
}
}
}
else
{
lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2644_; 
lean_inc(v_stop_2570_);
lean_inc(v_start_2569_);
lean_inc_ref(v_array_2568_);
v_isSharedCheck_2644_ = !lean_is_exclusive(v_snd_2559_);
if (v_isSharedCheck_2644_ == 0)
{
lean_object* v_unused_2645_; lean_object* v_unused_2646_; lean_object* v_unused_2647_; 
v_unused_2645_ = lean_ctor_get(v_snd_2559_, 2);
lean_dec(v_unused_2645_);
v_unused_2646_ = lean_ctor_get(v_snd_2559_, 1);
lean_dec(v_unused_2646_);
v_unused_2647_ = lean_ctor_get(v_snd_2559_, 0);
lean_dec(v_unused_2647_);
v___x_2580_ = v_snd_2559_;
v_isShared_2581_ = v_isSharedCheck_2644_;
goto v_resetjp_2579_;
}
else
{
lean_dec(v_snd_2559_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2644_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v_a_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; size_t v_sz_2587_; size_t v___x_2588_; lean_object* v___x_2589_; lean_object* v_fst_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2642_; 
v_a_2582_ = lean_array_uget_borrowed(v_as_2546_, v_i_2548_);
v___x_2583_ = lean_array_fget_borrowed(v_array_2568_, v_start_2569_);
v___x_2584_ = lean_box(0);
v___x_2585_ = lean_box(0);
v___x_2586_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0));
v_sz_2587_ = lean_array_size(v___x_2583_);
v___x_2588_ = ((size_t)0ULL);
lean_inc(v_a_2582_);
v___x_2589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_2582_, v___x_2583_, v_sz_2587_, v___x_2588_, v___x_2586_);
v_fst_2590_ = lean_ctor_get(v___x_2589_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___x_2589_);
if (v_isSharedCheck_2642_ == 0)
{
lean_object* v_unused_2643_; 
v_unused_2643_ = lean_ctor_get(v___x_2589_, 1);
lean_dec(v_unused_2643_);
v___x_2592_ = v___x_2589_;
v_isShared_2593_ = v_isSharedCheck_2642_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_fst_2590_);
lean_dec(v___x_2589_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2642_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2594_ = lean_unsigned_to_nat(1u);
v___x_2595_ = lean_nat_add(v_start_2569_, v___x_2594_);
lean_dec(v_start_2569_);
if (v_isShared_2581_ == 0)
{
lean_ctor_set(v___x_2580_, 1, v___x_2595_);
v___x_2597_ = v___x_2580_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_array_2568_);
lean_ctor_set(v_reuseFailAlloc_2641_, 1, v___x_2595_);
lean_ctor_set(v_reuseFailAlloc_2641_, 2, v_stop_2570_);
v___x_2597_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
if (lean_obj_tag(v_fst_2590_) == 0)
{
lean_del_object(v___x_2562_);
goto v___jp_2598_;
}
else
{
lean_object* v_val_2605_; 
v_val_2605_ = lean_ctor_get(v_fst_2590_, 0);
lean_inc(v_val_2605_);
lean_dec_ref(v_fst_2590_);
if (lean_obj_tag(v_val_2605_) == 1)
{
lean_object* v_val_2606_; lean_object* v_ctx_2607_; lean_object* v_toCommandContextInfo_2608_; lean_object* v_module_2609_; lean_object* v_decl_2610_; lean_object* v_determineInsertion_2611_; lean_object* v_env_2612_; lean_object* v___x_2613_; uint8_t v___x_2614_; 
lean_del_object(v___x_2592_);
lean_del_object(v___x_2566_);
v_val_2606_ = lean_ctor_get(v_val_2605_, 0);
lean_inc(v_val_2606_);
lean_dec_ref(v_val_2605_);
v_ctx_2607_ = lean_ctor_get(v_a_2582_, 1);
v_toCommandContextInfo_2608_ = lean_ctor_get(v_ctx_2607_, 0);
v_module_2609_ = lean_ctor_get(v_val_2606_, 0);
lean_inc(v_module_2609_);
v_decl_2610_ = lean_ctor_get(v_val_2606_, 1);
lean_inc(v_decl_2610_);
lean_dec(v_val_2606_);
v_determineInsertion_2611_ = lean_ctor_get(v_a_2582_, 2);
v_env_2612_ = lean_ctor_get(v_toCommandContextInfo_2608_, 0);
v___x_2613_ = l_Lean_Environment_mainModule(v_env_2612_);
v___x_2614_ = lean_name_eq(v_module_2609_, v___x_2613_);
lean_dec(v___x_2613_);
if (v___x_2614_ == 0)
{
lean_object* v___x_2615_; lean_object* v_edits_2617_; uint8_t v___x_2636_; 
lean_inc_ref(v_determineInsertion_2611_);
v___x_2615_ = lean_apply_1(v_determineInsertion_2611_, v_decl_2610_);
v___x_2636_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_fst_2564_, v_module_2609_);
if (v___x_2636_ == 0)
{
goto v___jp_2632_;
}
else
{
if (v___x_2614_ == 0)
{
v_edits_2617_ = v_fst_2560_;
goto v___jp_2616_;
}
else
{
goto v___jp_2632_;
}
}
v___jp_2616_:
{
lean_object* v_edit_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2630_; 
v_edit_2618_ = lean_ctor_get(v___x_2615_, 1);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2630_ == 0)
{
lean_object* v_unused_2631_; 
v_unused_2631_ = lean_ctor_get(v___x_2615_, 0);
lean_dec(v_unused_2631_);
v___x_2620_ = v___x_2615_;
v_isShared_2621_ = v_isSharedCheck_2630_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_edit_2618_);
lean_dec(v___x_2615_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2630_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2625_; 
v___x_2622_ = lean_array_push(v_edits_2617_, v_edit_2618_);
v___x_2623_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_fst_2564_, v_module_2609_, v___x_2585_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v___x_2597_);
lean_ctor_set(v___x_2562_, 0, v___x_2623_);
v___x_2625_ = v___x_2562_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2629_, 1, v___x_2597_);
v___x_2625_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2627_; 
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 1, v___x_2625_);
lean_ctor_set(v___x_2620_, 0, v___x_2622_);
v___x_2627_ = v___x_2620_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2628_, 1, v___x_2625_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
v_a_2552_ = v___x_2627_;
goto v___jp_2551_;
}
}
}
}
v___jp_2632_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_inc(v_module_2609_);
lean_inc_ref(v_ctx_2607_);
v___x_2633_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_2607_, v_module_2609_);
lean_inc_ref(v___x_2545_);
v___x_2634_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2545_);
lean_ctor_set(v___x_2634_, 1, v___x_2633_);
lean_ctor_set(v___x_2634_, 2, v___x_2584_);
lean_ctor_set(v___x_2634_, 3, v___x_2584_);
v___x_2635_ = lean_array_push(v_fst_2560_, v___x_2634_);
v_edits_2617_ = v___x_2635_;
goto v___jp_2616_;
}
}
else
{
lean_object* v___x_2638_; 
lean_dec(v_decl_2610_);
lean_dec(v_module_2609_);
if (v_isShared_2563_ == 0)
{
lean_ctor_set(v___x_2562_, 1, v___x_2597_);
lean_ctor_set(v___x_2562_, 0, v_fst_2564_);
v___x_2638_ = v___x_2562_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_fst_2564_);
lean_ctor_set(v_reuseFailAlloc_2640_, 1, v___x_2597_);
v___x_2638_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2639_, 0, v_fst_2560_);
lean_ctor_set(v___x_2639_, 1, v___x_2638_);
v_a_2552_ = v___x_2639_;
goto v___jp_2551_;
}
}
}
else
{
lean_dec(v_val_2605_);
lean_del_object(v___x_2562_);
goto v___jp_2598_;
}
}
v___jp_2598_:
{
lean_object* v___x_2600_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set(v___x_2592_, 1, v___x_2597_);
lean_ctor_set(v___x_2592_, 0, v_fst_2564_);
v___x_2600_ = v___x_2592_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_fst_2564_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2597_);
v___x_2600_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
lean_object* v___x_2602_; 
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 1, v___x_2600_);
lean_ctor_set(v___x_2566_, 0, v_fst_2560_);
v___x_2602_ = v___x_2566_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_fst_2560_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
v_a_2552_ = v___x_2602_;
goto v___jp_2551_;
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
v___jp_2551_:
{
size_t v___x_2553_; size_t v___x_2554_; 
v___x_2553_ = ((size_t)1ULL);
v___x_2554_ = lean_usize_add(v_i_2548_, v___x_2553_);
v_i_2548_ = v___x_2554_;
v_b_2549_ = v_a_2552_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg___boxed(lean_object* v___x_2652_, lean_object* v_as_2653_, lean_object* v_sz_2654_, lean_object* v_i_2655_, lean_object* v_b_2656_, lean_object* v___y_2657_){
_start:
{
size_t v_sz_boxed_2658_; size_t v_i_boxed_2659_; lean_object* v_res_2660_; 
v_sz_boxed_2658_ = lean_unbox_usize(v_sz_2654_);
lean_dec(v_sz_2654_);
v_i_boxed_2659_ = lean_unbox_usize(v_i_2655_);
lean_dec(v_i_2655_);
v_res_2660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_2652_, v_as_2653_, v_sz_boxed_2658_, v_i_boxed_2659_, v_b_2656_);
lean_dec_ref(v_as_2653_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(lean_object* v___x_2661_, lean_object* v_as_2662_, size_t v_i_2663_, size_t v_stop_2664_, lean_object* v_b_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v_a_2669_; uint8_t v___x_2673_; 
v___x_2673_ = lean_usize_dec_eq(v_i_2663_, v_stop_2664_);
if (v___x_2673_ == 0)
{
lean_object* v___x_2674_; lean_object* v_stop_2675_; lean_object* v___x_2676_; 
v___x_2674_ = lean_array_uget_borrowed(v_as_2662_, v_i_2663_);
v_stop_2675_ = lean_ctor_get(v___x_2674_, 1);
lean_inc(v_stop_2675_);
lean_inc_ref(v___x_2661_);
v___x_2676_ = l_Lean_Server_FileWorker_computeQueries(v___x_2661_, v_stop_2675_, v___y_2666_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref(v___x_2676_);
v___x_2678_ = l_Array_append___redArg(v_b_2665_, v_a_2677_);
lean_dec(v_a_2677_);
v_a_2669_ = v___x_2678_;
goto v___jp_2668_;
}
else
{
lean_dec_ref(v_b_2665_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2679_; 
v_a_2679_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2679_);
lean_dec_ref(v___x_2676_);
v_a_2669_ = v_a_2679_;
goto v___jp_2668_;
}
else
{
lean_dec_ref(v___x_2661_);
return v___x_2676_;
}
}
}
else
{
lean_object* v___x_2680_; 
lean_dec_ref(v___x_2661_);
v___x_2680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2680_, 0, v_b_2665_);
return v___x_2680_;
}
v___jp_2668_:
{
size_t v___x_2670_; size_t v___x_2671_; 
v___x_2670_ = ((size_t)1ULL);
v___x_2671_ = lean_usize_add(v_i_2663_, v___x_2670_);
v_i_2663_ = v___x_2671_;
v_b_2665_ = v_a_2669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4___boxed(lean_object* v___x_2681_, lean_object* v_as_2682_, lean_object* v_i_2683_, lean_object* v_stop_2684_, lean_object* v_b_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
size_t v_i_boxed_2688_; size_t v_stop_boxed_2689_; lean_object* v_res_2690_; 
v_i_boxed_2688_ = lean_unbox_usize(v_i_2683_);
lean_dec(v_i_2683_);
v_stop_boxed_2689_ = lean_unbox_usize(v_stop_2684_);
lean_dec(v_stop_2684_);
v_res_2690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v___x_2681_, v_as_2682_, v_i_boxed_2688_, v_stop_boxed_2689_, v_b_2685_, v___y_2686_);
lean_dec_ref(v___y_2686_);
lean_dec_ref(v_as_2682_);
return v_res_2690_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0(void){
_start:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v___x_2691_ = lean_box(0);
v___x_2692_ = lean_unsigned_to_nat(16u);
v___x_2693_ = lean_mk_array(v___x_2692_, v___x_2691_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object* v_id_2696_, lean_object* v_action_2697_, lean_object* v_unknownIdentifierRanges_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_doc_2701_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v___y_2705_; size_t v___y_2706_; size_t v___y_2707_; lean_object* v___y_2708_; lean_object* v_toEditableDocumentCore_2764_; lean_object* v_meta_2765_; lean_object* v_initSnap_2766_; lean_object* v_text_2767_; lean_object* v_a_2769_; lean_object* v___y_2809_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_doc_2701_ = lean_ctor_get(v_a_2699_, 1);
v_toEditableDocumentCore_2764_ = lean_ctor_get(v_doc_2701_, 0);
v_meta_2765_ = lean_ctor_get(v_toEditableDocumentCore_2764_, 0);
v_initSnap_2766_ = lean_ctor_get(v_toEditableDocumentCore_2764_, 1);
v_text_2767_ = lean_ctor_get(v_meta_2765_, 3);
v___x_2819_ = lean_unsigned_to_nat(0u);
v___x_2820_ = ((lean_object*)(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1));
v___x_2821_ = lean_array_get_size(v_unknownIdentifierRanges_2698_);
v___x_2822_ = lean_nat_dec_lt(v___x_2819_, v___x_2821_);
if (v___x_2822_ == 0)
{
v_a_2769_ = v___x_2820_;
goto v___jp_2768_;
}
else
{
uint8_t v___x_2823_; 
v___x_2823_ = lean_nat_dec_le(v___x_2821_, v___x_2821_);
if (v___x_2823_ == 0)
{
if (v___x_2822_ == 0)
{
v_a_2769_ = v___x_2820_;
goto v___jp_2768_;
}
else
{
size_t v___x_2824_; size_t v___x_2825_; lean_object* v___x_2826_; 
v___x_2824_ = ((size_t)0ULL);
v___x_2825_ = lean_usize_of_nat(v___x_2821_);
lean_inc_ref(v_doc_2701_);
v___x_2826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_2701_, v_unknownIdentifierRanges_2698_, v___x_2824_, v___x_2825_, v___x_2820_, v_a_2699_);
v___y_2809_ = v___x_2826_;
goto v___jp_2808_;
}
}
else
{
size_t v___x_2827_; size_t v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = ((size_t)0ULL);
v___x_2828_ = lean_usize_of_nat(v___x_2821_);
lean_inc_ref(v_doc_2701_);
v___x_2829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_2701_, v_unknownIdentifierRanges_2698_, v___x_2827_, v___x_2828_, v___x_2820_, v_a_2699_);
v___y_2809_ = v___x_2829_;
goto v___jp_2808_;
}
}
v___jp_2702_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
lean_inc_ref(v___y_2708_);
v___x_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___y_2708_);
lean_ctor_set(v___x_2709_, 1, v___y_2708_);
v___x_2710_ = lean_mk_empty_array_with_capacity(v___y_2704_);
v___x_2711_ = lean_obj_once(&l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0, &l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once, _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0);
lean_inc(v___y_2704_);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___y_2704_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = lean_array_get_size(v___y_2703_);
v___x_2714_ = l_Array_toSubarray___redArg(v___y_2703_, v___y_2704_, v___x_2713_);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2712_);
lean_ctor_set(v___x_2715_, 1, v___x_2714_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2710_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_2709_, v___y_2705_, v___y_2707_, v___y_2706_, v___x_2716_);
lean_dec_ref(v___y_2705_);
if (lean_obj_tag(v___x_2717_) == 0)
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2755_; 
v_a_2718_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2720_ = v___x_2717_;
v_isShared_2721_ = v_isSharedCheck_2755_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2717_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2755_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v_fst_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2753_; 
v_fst_2722_ = lean_ctor_get(v_a_2718_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_a_2718_);
if (v_isSharedCheck_2753_ == 0)
{
lean_object* v_unused_2754_; 
v_unused_2754_ = lean_ctor_get(v_a_2718_, 1);
lean_dec(v_unused_2754_);
v___x_2724_ = v_a_2718_;
v_isShared_2725_ = v_isSharedCheck_2753_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_fst_2722_);
lean_dec(v_a_2718_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2753_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v_toWorkDoneProgressParams_2726_; lean_object* v_toPartialResultParams_2727_; lean_object* v_title_2728_; lean_object* v_kind_x3f_2729_; lean_object* v_diagnostics_x3f_2730_; lean_object* v_isPreferred_x3f_2731_; lean_object* v_disabled_x3f_2732_; lean_object* v_command_x3f_2733_; lean_object* v_data_x3f_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2751_; 
v_toWorkDoneProgressParams_2726_ = lean_ctor_get(v_action_2697_, 0);
v_toPartialResultParams_2727_ = lean_ctor_get(v_action_2697_, 1);
v_title_2728_ = lean_ctor_get(v_action_2697_, 2);
v_kind_x3f_2729_ = lean_ctor_get(v_action_2697_, 3);
v_diagnostics_x3f_2730_ = lean_ctor_get(v_action_2697_, 4);
v_isPreferred_x3f_2731_ = lean_ctor_get(v_action_2697_, 5);
v_disabled_x3f_2732_ = lean_ctor_get(v_action_2697_, 6);
v_command_x3f_2733_ = lean_ctor_get(v_action_2697_, 8);
v_data_x3f_2734_ = lean_ctor_get(v_action_2697_, 9);
v_isSharedCheck_2751_ = !lean_is_exclusive(v_action_2697_);
if (v_isSharedCheck_2751_ == 0)
{
lean_object* v_unused_2752_; 
v_unused_2752_ = lean_ctor_get(v_action_2697_, 7);
lean_dec(v_unused_2752_);
v___x_2736_ = v_action_2697_;
v_isShared_2737_ = v_isSharedCheck_2751_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_data_x3f_2734_);
lean_inc(v_command_x3f_2733_);
lean_inc(v_disabled_x3f_2732_);
lean_inc(v_isPreferred_x3f_2731_);
lean_inc(v_diagnostics_x3f_2730_);
lean_inc(v_kind_x3f_2729_);
lean_inc(v_title_2728_);
lean_inc(v_toPartialResultParams_2727_);
lean_inc(v_toWorkDoneProgressParams_2726_);
lean_dec(v_action_2697_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2751_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_inc_ref(v_doc_2701_);
v___x_2738_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_doc_2701_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 1, v_fst_2722_);
lean_ctor_set(v___x_2724_, 0, v___x_2738_);
v___x_2740_ = v___x_2724_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2738_);
lean_ctor_set(v_reuseFailAlloc_2750_, 1, v_fst_2722_);
v___x_2740_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_2744_; 
v___x_2741_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_2740_);
v___x_2742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2742_, 0, v___x_2741_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 7, v___x_2742_);
v___x_2744_ = v___x_2736_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v_toWorkDoneProgressParams_2726_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_toPartialResultParams_2727_);
lean_ctor_set(v_reuseFailAlloc_2749_, 2, v_title_2728_);
lean_ctor_set(v_reuseFailAlloc_2749_, 3, v_kind_x3f_2729_);
lean_ctor_set(v_reuseFailAlloc_2749_, 4, v_diagnostics_x3f_2730_);
lean_ctor_set(v_reuseFailAlloc_2749_, 5, v_isPreferred_x3f_2731_);
lean_ctor_set(v_reuseFailAlloc_2749_, 6, v_disabled_x3f_2732_);
lean_ctor_set(v_reuseFailAlloc_2749_, 7, v___x_2742_);
lean_ctor_set(v_reuseFailAlloc_2749_, 8, v_command_x3f_2733_);
lean_ctor_set(v_reuseFailAlloc_2749_, 9, v_data_x3f_2734_);
v___x_2744_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
v___x_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2745_, 0, v___x_2744_);
if (v_isShared_2721_ == 0)
{
lean_ctor_set(v___x_2720_, 0, v___x_2745_);
v___x_2747_ = v___x_2720_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v_action_2697_);
v_a_2756_ = lean_ctor_get(v___x_2717_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2717_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2717_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2717_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
v___jp_2768_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; uint8_t v___x_2772_; 
v___x_2770_ = lean_array_get_size(v_a_2769_);
v___x_2771_ = lean_unsigned_to_nat(0u);
v___x_2772_ = lean_nat_dec_eq(v___x_2770_, v___x_2771_);
if (v___x_2772_ == 0)
{
lean_object* v___x_2773_; size_t v_sz_2774_; size_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2805_; 
v___x_2773_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0));
v_sz_2774_ = lean_array_size(v_a_2769_);
v___x_2775_ = ((size_t)0ULL);
lean_inc_ref(v_a_2769_);
v___x_2776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_2774_, v___x_2775_, v_a_2769_);
v___x_2777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2777_, 0, v_id_2696_);
lean_ctor_set(v___x_2777_, 1, v___x_2776_);
v___x_2778_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_2773_, v___x_2777_, v_a_2699_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2805_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2805_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2805_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2805_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; 
v___x_2783_ = lean_task_get_own(v_a_2779_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v_response_2784_; lean_object* v_stx_2785_; lean_object* v___x_2786_; 
lean_del_object(v___x_2781_);
v_response_2784_ = lean_ctor_get(v___x_2783_, 0);
lean_inc(v_response_2784_);
lean_dec_ref(v___x_2783_);
v_stx_2785_ = lean_ctor_get(v_initSnap_2766_, 3);
v___x_2786_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2785_, v___x_2772_);
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v___x_2787_; 
v___x_2787_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5));
v___y_2703_ = v_response_2784_;
v___y_2704_ = v___x_2771_;
v___y_2705_ = v_a_2769_;
v___y_2706_ = v___x_2775_;
v___y_2707_ = v_sz_2774_;
v___y_2708_ = v___x_2787_;
goto v___jp_2702_;
}
else
{
lean_object* v_val_2788_; lean_object* v___x_2789_; lean_object* v_line_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2799_; 
v_val_2788_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_val_2788_);
lean_dec_ref(v___x_2786_);
lean_inc_ref(v_text_2767_);
v___x_2789_ = l_Lean_FileMap_utf8PosToLspPos(v_text_2767_, v_val_2788_);
lean_dec(v_val_2788_);
v_line_2790_ = lean_ctor_get(v___x_2789_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2789_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v___x_2789_, 1);
lean_dec(v_unused_2800_);
v___x_2792_ = v___x_2789_;
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_line_2790_);
lean_dec(v___x_2789_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2799_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2794_ = lean_unsigned_to_nat(1u);
v___x_2795_ = lean_nat_add(v_line_2790_, v___x_2794_);
lean_dec(v_line_2790_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 1, v___x_2771_);
lean_ctor_set(v___x_2792_, 0, v___x_2795_);
v___x_2797_ = v___x_2792_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v___x_2771_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
v___y_2703_ = v_response_2784_;
v___y_2704_ = v___x_2771_;
v___y_2705_ = v_a_2769_;
v___y_2706_ = v___x_2775_;
v___y_2707_ = v_sz_2774_;
v___y_2708_ = v___x_2797_;
goto v___jp_2702_;
}
}
}
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
lean_dec(v___x_2783_);
lean_dec_ref(v_a_2769_);
lean_dec_ref(v_action_2697_);
v___x_2801_ = lean_box(0);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2801_);
v___x_2803_ = v___x_2781_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
else
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
lean_dec_ref(v_a_2769_);
lean_dec_ref(v_action_2697_);
lean_dec(v_id_2696_);
v___x_2806_ = lean_box(0);
v___x_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2806_);
return v___x_2807_;
}
}
v___jp_2808_:
{
if (lean_obj_tag(v___y_2809_) == 0)
{
lean_object* v_a_2810_; 
v_a_2810_ = lean_ctor_get(v___y_2809_, 0);
lean_inc(v_a_2810_);
lean_dec_ref(v___y_2809_);
v_a_2769_ = v_a_2810_;
goto v___jp_2768_;
}
else
{
lean_object* v_a_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2818_; 
lean_dec_ref(v_action_2697_);
lean_dec(v_id_2696_);
v_a_2811_ = lean_ctor_get(v___y_2809_, 0);
v_isSharedCheck_2818_ = !lean_is_exclusive(v___y_2809_);
if (v_isSharedCheck_2818_ == 0)
{
v___x_2813_ = v___y_2809_;
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
else
{
lean_inc(v_a_2811_);
lean_dec(v___y_2809_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2818_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2816_; 
if (v_isShared_2814_ == 0)
{
v___x_2816_ = v___x_2813_;
goto v_reusejp_2815_;
}
else
{
lean_object* v_reuseFailAlloc_2817_; 
v_reuseFailAlloc_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2817_, 0, v_a_2811_);
v___x_2816_ = v_reuseFailAlloc_2817_;
goto v_reusejp_2815_;
}
v_reusejp_2815_:
{
return v___x_2816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object* v_id_2830_, lean_object* v_action_2831_, lean_object* v_unknownIdentifierRanges_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(v_id_2830_, v_action_2831_, v_unknownIdentifierRanges_2832_, v_a_2833_);
lean_dec_ref(v_a_2833_);
lean_dec_ref(v_unknownIdentifierRanges_2832_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(lean_object* v_00_u03b2_2836_, lean_object* v_m_2837_, lean_object* v_a_2838_, lean_object* v_b_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_m_2837_, v_a_2838_, v_b_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(lean_object* v_00_u03b2_2841_, lean_object* v_m_2842_, lean_object* v_a_2843_){
_start:
{
uint8_t v___x_2844_; 
v___x_2844_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_2842_, v_a_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___boxed(lean_object* v_00_u03b2_2845_, lean_object* v_m_2846_, lean_object* v_a_2847_){
_start:
{
uint8_t v_res_2848_; lean_object* v_r_2849_; 
v_res_2848_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(v_00_u03b2_2845_, v_m_2846_, v_a_2847_);
lean_dec(v_a_2847_);
lean_dec_ref(v_m_2846_);
v_r_2849_ = lean_box(v_res_2848_);
return v_r_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(lean_object* v___x_2850_, lean_object* v_as_2851_, size_t v_sz_2852_, size_t v_i_2853_, lean_object* v_b_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v___x_2857_; 
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_2850_, v_as_2851_, v_sz_2852_, v_i_2853_, v_b_2854_);
return v___x_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(lean_object* v___x_2858_, lean_object* v_as_2859_, lean_object* v_sz_2860_, lean_object* v_i_2861_, lean_object* v_b_2862_, lean_object* v___y_2863_, lean_object* v___y_2864_){
_start:
{
size_t v_sz_boxed_2865_; size_t v_i_boxed_2866_; lean_object* v_res_2867_; 
v_sz_boxed_2865_ = lean_unbox_usize(v_sz_2860_);
lean_dec(v_sz_2860_);
v_i_boxed_2866_ = lean_unbox_usize(v_i_2861_);
lean_dec(v_i_2861_);
v_res_2867_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(v___x_2858_, v_as_2859_, v_sz_boxed_2865_, v_i_boxed_2866_, v_b_2862_, v___y_2863_);
lean_dec_ref(v___y_2863_);
lean_dec_ref(v_as_2859_);
return v_res_2867_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(lean_object* v_00_u03b2_2868_, lean_object* v_a_2869_, lean_object* v_x_2870_){
_start:
{
uint8_t v___x_2871_; 
v___x_2871_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2869_, v_x_2870_);
return v___x_2871_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2872_, lean_object* v_a_2873_, lean_object* v_x_2874_){
_start:
{
uint8_t v_res_2875_; lean_object* v_r_2876_; 
v_res_2875_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(v_00_u03b2_2872_, v_a_2873_, v_x_2874_);
lean_dec(v_x_2874_);
lean_dec(v_a_2873_);
v_r_2876_ = lean_box(v_res_2875_);
return v_r_2876_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2(lean_object* v_00_u03b2_2877_, lean_object* v_data_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_data_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2880_, lean_object* v_i_2881_, lean_object* v_source_2882_, lean_object* v_target_2883_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v_i_2881_, v_source_2882_, v_target_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_2885_, lean_object* v_x_2886_, lean_object* v_x_2887_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_x_2886_, v_x_2887_);
return v___x_2888_;
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
