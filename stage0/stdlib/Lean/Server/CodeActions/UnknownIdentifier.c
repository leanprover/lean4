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
v___x_83_ = lean_nat_add(v___y_80_, v___y_82_);
lean_dec(v___y_82_);
lean_dec(v___y_80_);
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
lean_ctor_set(v___x_63_, 3, v___y_81_);
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
lean_ctor_set(v_reuseFailAlloc_88_, 3, v___y_81_);
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
v___y_80_ = v___x_96_;
v___y_81_ = v___x_95_;
v___y_82_ = v_size_97_;
goto v___jp_79_;
}
else
{
lean_object* v___x_98_; 
v___x_98_ = lean_unsigned_to_nat(0u);
v___y_80_ = v___x_96_;
v___y_81_ = v___x_95_;
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
lean_dec_ref(v_fst_488_);
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
lean_dec_ref(v_fst_498_);
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
lean_dec_ref(v___x_516_);
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
lean_dec_ref(v_msgRange_580_);
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
lean_dec_ref(v_msgRange_627_);
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
lean_dec_ref(v___x_650_);
return v_a_651_;
}
else
{
lean_object* v_a_652_; lean_object* v___x_653_; lean_object* v___x_654_; size_t v_sz_655_; size_t v___x_656_; lean_object* v___x_657_; lean_object* v_fst_658_; 
v_a_652_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_a_652_);
lean_dec_ref(v___x_650_);
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
lean_dec_ref(v_fst_658_);
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
lean_dec_ref(v_x_668_);
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
lean_dec_ref(v___x_688_);
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
lean_dec_ref(v_fst_1028_);
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
lean_dec_ref(v_fst_1038_);
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
lean_dec_ref(v___x_1055_);
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
lean_dec_ref(v___x_1092_);
return v_a_1093_;
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; size_t v_sz_1097_; size_t v___x_1098_; lean_object* v___x_1099_; lean_object* v_fst_1100_; 
v_a_1094_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1092_);
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
lean_dec_ref(v_fst_1100_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(lean_object* v_b_1240_){
_start:
{
lean_object* v_fst_1241_; lean_object* v_snd_1242_; lean_object* v___x_1244_; uint8_t v_isShared_1245_; uint8_t v_isSharedCheck_1258_; 
v_fst_1241_ = lean_ctor_get(v_b_1240_, 0);
v_snd_1242_ = lean_ctor_get(v_b_1240_, 1);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_b_1240_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1244_ = v_b_1240_;
v_isShared_1245_ = v_isSharedCheck_1258_;
goto v_resetjp_1243_;
}
else
{
lean_inc(v_snd_1242_);
lean_inc(v_fst_1241_);
lean_dec(v_b_1240_);
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
lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v_openNamespaces_1249_; lean_object* v_currentNamespace_1250_; lean_object* v___x_1252_; 
v___x_1247_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0));
lean_inc(v_snd_1242_);
v___x_1248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1248_, 0, v_snd_1242_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
v_openNamespaces_1249_ = lean_array_push(v_fst_1241_, v___x_1248_);
v_currentNamespace_1250_ = l_Lean_Name_getPrefix(v_snd_1242_);
lean_dec(v_snd_1242_);
if (v_isShared_1245_ == 0)
{
lean_ctor_set(v___x_1244_, 1, v_currentNamespace_1250_);
lean_ctor_set(v___x_1244_, 0, v_openNamespaces_1249_);
v___x_1252_ = v___x_1244_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_openNamespaces_1249_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v_currentNamespace_1250_);
v___x_1252_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
v_b_1240_ = v___x_1252_;
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
v___x_1299_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0(v___x_1298_);
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(lean_object* v_doc_1305_, lean_object* v_currNamespace_1306_, lean_object* v_openDecls_1307_, lean_object* v_val_1308_, lean_object* v_val_1309_, uint8_t v___x_1310_, lean_object* v_decl_1311_){
_start:
{
lean_object* v_toEditableDocumentCore_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1336_; 
v_toEditableDocumentCore_1312_ = lean_ctor_get(v_doc_1305_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v_doc_1305_);
if (v_isSharedCheck_1336_ == 0)
{
lean_object* v_unused_1337_; 
v_unused_1337_ = lean_ctor_get(v_doc_1305_, 1);
lean_dec(v_unused_1337_);
v___x_1314_ = v_doc_1305_;
v_isShared_1315_ = v_isSharedCheck_1336_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_toEditableDocumentCore_1312_);
lean_dec(v_doc_1305_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1336_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v_meta_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1332_; 
v_meta_1316_ = lean_ctor_get(v_toEditableDocumentCore_1312_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_toEditableDocumentCore_1312_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; lean_object* v_unused_1334_; lean_object* v_unused_1335_; 
v_unused_1333_ = lean_ctor_get(v_toEditableDocumentCore_1312_, 3);
lean_dec(v_unused_1333_);
v_unused_1334_ = lean_ctor_get(v_toEditableDocumentCore_1312_, 2);
lean_dec(v_unused_1334_);
v_unused_1335_ = lean_ctor_get(v_toEditableDocumentCore_1312_, 1);
lean_dec(v_unused_1335_);
v___x_1318_ = v_toEditableDocumentCore_1312_;
v_isShared_1319_ = v_isSharedCheck_1332_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_meta_1316_);
lean_dec(v_toEditableDocumentCore_1312_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1332_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v_text_1320_; lean_object* v_minimizedId_1321_; lean_object* v___x_1323_; 
v_text_1320_ = lean_ctor_get(v_meta_1316_, 3);
lean_inc_ref(v_text_1320_);
lean_dec_ref(v_meta_1316_);
v_minimizedId_1321_ = l_Lean_Server_Completion_minimizeGlobalIdentifierInContext(v_currNamespace_1306_, v_openDecls_1307_, v_decl_1311_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 1, v_val_1309_);
lean_ctor_set(v___x_1314_, 0, v_val_1308_);
v___x_1323_ = v___x_1314_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_val_1308_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_val_1309_);
v___x_1323_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1324_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1320_, v___x_1323_);
lean_inc(v_minimizedId_1321_);
v___x_1325_ = l_Lean_Name_toString(v_minimizedId_1321_, v___x_1310_);
v___x_1326_ = lean_box(0);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 3, v___x_1326_);
lean_ctor_set(v___x_1318_, 2, v___x_1326_);
lean_ctor_set(v___x_1318_, 1, v___x_1325_);
lean_ctor_set(v___x_1318_, 0, v___x_1324_);
v___x_1328_ = v___x_1318_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_minimizedId_1321_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
return v___x_1329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed(lean_object* v_doc_1338_, lean_object* v_currNamespace_1339_, lean_object* v_openDecls_1340_, lean_object* v_val_1341_, lean_object* v_val_1342_, lean_object* v___x_1343_, lean_object* v_decl_1344_){
_start:
{
uint8_t v___x_172__boxed_1345_; lean_object* v_res_1346_; 
v___x_172__boxed_1345_ = lean_unbox(v___x_1343_);
v_res_1346_ = l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0(v_doc_1338_, v_currNamespace_1339_, v_openDecls_1340_, v_val_1341_, v_val_1342_, v___x_172__boxed_1345_, v_decl_1344_);
lean_dec(v_openDecls_1340_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f(lean_object* v_doc_1347_, lean_object* v_ctx_1348_, lean_object* v_stx_1349_, lean_object* v_id_1350_){
_start:
{
uint8_t v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = 1;
v___x_1352_ = l_Lean_Syntax_getPos_x3f(v_stx_1349_, v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 1)
{
lean_object* v_val_1353_; lean_object* v___x_1354_; 
v_val_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1349_, v___x_1351_);
if (lean_obj_tag(v___x_1354_) == 1)
{
lean_object* v_toCommandContextInfo_1355_; lean_object* v_val_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1371_; 
v_toCommandContextInfo_1355_ = lean_ctor_get(v_ctx_1348_, 0);
v_val_1356_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1358_ = v___x_1354_;
v_isShared_1359_ = v_isSharedCheck_1371_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_val_1356_);
lean_dec(v___x_1354_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1371_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v_currNamespace_1360_; lean_object* v_openDecls_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; 
v_currNamespace_1360_ = lean_ctor_get(v_toCommandContextInfo_1355_, 5);
v_openDecls_1361_ = lean_ctor_get(v_toCommandContextInfo_1355_, 6);
v___x_1362_ = l_Lean_Name_toString(v_id_1350_, v___x_1351_);
v___x_1363_ = lean_box(v___x_1351_);
lean_inc_n(v_openDecls_1361_, 2);
lean_inc_n(v_currNamespace_1360_, 2);
v___f_1364_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeIdQuery_x3f___lam__0___boxed), 7, 6);
lean_closure_set(v___f_1364_, 0, v_doc_1347_);
lean_closure_set(v___f_1364_, 1, v_currNamespace_1360_);
lean_closure_set(v___f_1364_, 2, v_openDecls_1361_);
lean_closure_set(v___f_1364_, 3, v_val_1353_);
lean_closure_set(v___f_1364_, 4, v_val_1356_);
lean_closure_set(v___f_1364_, 5, v___x_1363_);
v___x_1365_ = l_Lean_Server_FileWorker_collectOpenNamespaces(v_currNamespace_1360_, v_openDecls_1361_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1362_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
v___x_1367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1366_);
lean_ctor_set(v___x_1367_, 1, v_ctx_1348_);
lean_ctor_set(v___x_1367_, 2, v___f_1364_);
if (v_isShared_1359_ == 0)
{
lean_ctor_set(v___x_1358_, 0, v___x_1367_);
v___x_1369_ = v___x_1358_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1367_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
else
{
lean_object* v___x_1372_; 
lean_dec(v___x_1354_);
lean_dec(v_val_1353_);
lean_dec(v_id_1350_);
lean_dec_ref(v_ctx_1348_);
lean_dec_ref(v_doc_1347_);
v___x_1372_ = lean_box(0);
return v___x_1372_;
}
}
else
{
lean_object* v___x_1373_; 
lean_dec(v___x_1352_);
lean_dec(v_id_1350_);
lean_dec_ref(v_ctx_1348_);
lean_dec_ref(v_doc_1347_);
v___x_1373_ = lean_box(0);
return v___x_1373_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeIdQuery_x3f___boxed(lean_object* v_doc_1374_, lean_object* v_ctx_1375_, lean_object* v_stx_1376_, lean_object* v_id_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(v_doc_1374_, v_ctx_1375_, v_stx_1376_, v_id_1377_);
lean_dec(v_stx_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(lean_object* v_e_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = l_Lean_Expr_hasMVar(v_e_1379_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_e_1379_);
return v___x_1383_;
}
else
{
lean_object* v___x_1384_; lean_object* v_mctx_1385_; lean_object* v___x_1386_; lean_object* v_fst_1387_; lean_object* v_snd_1388_; lean_object* v___x_1389_; lean_object* v_cache_1390_; lean_object* v_zetaDeltaFVarIds_1391_; lean_object* v_postponed_1392_; lean_object* v_diag_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1402_; 
v___x_1384_ = lean_st_ref_get(v___y_1380_);
v_mctx_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc_ref(v_mctx_1385_);
lean_dec(v___x_1384_);
v___x_1386_ = l_Lean_instantiateMVarsCore(v_mctx_1385_, v_e_1379_);
v_fst_1387_ = lean_ctor_get(v___x_1386_, 0);
lean_inc(v_fst_1387_);
v_snd_1388_ = lean_ctor_get(v___x_1386_, 1);
lean_inc(v_snd_1388_);
lean_dec_ref(v___x_1386_);
v___x_1389_ = lean_st_ref_take(v___y_1380_);
v_cache_1390_ = lean_ctor_get(v___x_1389_, 1);
v_zetaDeltaFVarIds_1391_ = lean_ctor_get(v___x_1389_, 2);
v_postponed_1392_ = lean_ctor_get(v___x_1389_, 3);
v_diag_1393_ = lean_ctor_get(v___x_1389_, 4);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1402_ == 0)
{
lean_object* v_unused_1403_; 
v_unused_1403_ = lean_ctor_get(v___x_1389_, 0);
lean_dec(v_unused_1403_);
v___x_1395_ = v___x_1389_;
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_diag_1393_);
lean_inc(v_postponed_1392_);
lean_inc(v_zetaDeltaFVarIds_1391_);
lean_inc(v_cache_1390_);
lean_dec(v___x_1389_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1402_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 0, v_snd_1388_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_snd_1388_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_cache_1390_);
lean_ctor_set(v_reuseFailAlloc_1401_, 2, v_zetaDeltaFVarIds_1391_);
lean_ctor_set(v_reuseFailAlloc_1401_, 3, v_postponed_1392_);
lean_ctor_set(v_reuseFailAlloc_1401_, 4, v_diag_1393_);
v___x_1398_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_st_ref_set(v___y_1380_, v___x_1398_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_fst_1387_);
return v___x_1400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg___boxed(lean_object* v_e_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_1404_, v___y_1405_);
lean_dec(v___y_1405_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(lean_object* v_e_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_e_1408_, v___y_1410_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___boxed(lean_object* v_e_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0(v_e_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(lean_object* v_expr_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___y_1429_; uint8_t v___y_1430_; lean_object* v_a_1435_; lean_object* v___x_1438_; 
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v___y_1424_);
lean_inc_ref(v___y_1423_);
v___x_1438_ = lean_infer_type(v_expr_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v___x_1440_; lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1458_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = l_Lean_instantiateMVars___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__0___redArg(v_a_1439_, v___y_1424_);
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1458_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1458_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Lean_Server_Completion_getDotCompletionTypeNames(v_a_1441_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
if (lean_obj_tag(v___x_1445_) == 0)
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1456_; 
v_a_1446_ = lean_ctor_get(v___x_1445_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1445_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1448_ = v___x_1445_;
v_isShared_1449_ = v_isSharedCheck_1456_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1445_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1456_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1444_ == 0)
{
lean_ctor_set_tag(v___x_1443_, 1);
lean_ctor_set(v___x_1443_, 0, v_a_1446_);
v___x_1451_ = v___x_1443_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1453_; 
if (v_isShared_1449_ == 0)
{
lean_ctor_set(v___x_1448_, 0, v___x_1451_);
v___x_1453_ = v___x_1448_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1451_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
else
{
lean_object* v_a_1457_; 
lean_del_object(v___x_1443_);
v_a_1457_ = lean_ctor_get(v___x_1445_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1445_);
v_a_1435_ = v_a_1457_;
goto v___jp_1434_;
}
}
}
else
{
lean_object* v_a_1459_; 
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
v_a_1459_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1438_);
v_a_1435_ = v_a_1459_;
goto v___jp_1434_;
}
v___jp_1428_:
{
if (v___y_1430_ == 0)
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
lean_dec_ref(v___y_1429_);
v___x_1431_ = lean_box(0);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
else
{
lean_object* v___x_1433_; 
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___y_1429_);
return v___x_1433_;
}
}
v___jp_1434_:
{
uint8_t v___x_1436_; 
v___x_1436_ = l_Lean_Exception_isInterrupt(v_a_1435_);
if (v___x_1436_ == 0)
{
uint8_t v___x_1437_; 
lean_inc_ref(v_a_1435_);
v___x_1437_ = l_Lean_Exception_isRuntime(v_a_1435_);
v___y_1429_ = v_a_1435_;
v___y_1430_ = v___x_1437_;
goto v___jp_1428_;
}
else
{
v___y_1429_ = v_a_1435_;
v___y_1430_ = v___x_1436_;
goto v___jp_1428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed(lean_object* v_expr_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
lean_object* v_res_1466_; 
v_res_1466_ = l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0(v_expr_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1(lean_object* v_val_1467_, lean_object* v_val_1468_, lean_object* v_text_1469_, lean_object* v_decl_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v_val_1467_);
lean_ctor_set(v___x_1471_, 1, v_val_1468_);
v___x_1472_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1469_, v___x_1471_);
v___x_1473_ = l_Lean_Name_getString_x21(v_decl_1470_);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1472_);
lean_ctor_set(v___x_1475_, 1, v___x_1473_);
lean_ctor_set(v___x_1475_, 2, v___x_1474_);
lean_ctor_set(v___x_1475_, 3, v___x_1474_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v_decl_1470_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(size_t v_sz_1477_, size_t v_i_1478_, lean_object* v_bs_1479_){
_start:
{
uint8_t v___x_1480_; 
v___x_1480_ = lean_usize_dec_lt(v_i_1478_, v_sz_1477_);
if (v___x_1480_ == 0)
{
return v_bs_1479_;
}
else
{
lean_object* v_v_1481_; lean_object* v___x_1482_; lean_object* v_bs_x27_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; size_t v___x_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
v_v_1481_ = lean_array_uget(v_bs_1479_, v_i_1478_);
v___x_1482_ = lean_unsigned_to_nat(0u);
v_bs_x27_1483_ = lean_array_uset(v_bs_1479_, v_i_1478_, v___x_1482_);
v___x_1484_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00Lean_Server_FileWorker_collectOpenNamespaces_spec__0___closed__0));
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v_v_1481_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v___x_1486_ = ((size_t)1ULL);
v___x_1487_ = lean_usize_add(v_i_1478_, v___x_1486_);
v___x_1488_ = lean_array_uset(v_bs_x27_1483_, v_i_1478_, v___x_1485_);
v_i_1478_ = v___x_1487_;
v_bs_1479_ = v___x_1488_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1___boxed(lean_object* v_sz_1490_, lean_object* v_i_1491_, lean_object* v_bs_1492_){
_start:
{
size_t v_sz_boxed_1493_; size_t v_i_boxed_1494_; lean_object* v_res_1495_; 
v_sz_boxed_1493_ = lean_unbox_usize(v_sz_1490_);
lean_dec(v_sz_1490_);
v_i_boxed_1494_ = lean_unbox_usize(v_i_1491_);
lean_dec(v_i_1491_);
v_res_1495_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_boxed_1493_, v_i_boxed_1494_, v_bs_1492_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f(lean_object* v_doc_1496_, lean_object* v_ctx_1497_, lean_object* v_ti_1498_){
_start:
{
lean_object* v_toElabInfo_1500_; lean_object* v_lctx_1501_; lean_object* v_expr_1502_; lean_object* v_stx_1503_; uint8_t v___x_1504_; lean_object* v___x_1505_; 
v_toElabInfo_1500_ = lean_ctor_get(v_ti_1498_, 0);
lean_inc_ref(v_toElabInfo_1500_);
v_lctx_1501_ = lean_ctor_get(v_ti_1498_, 1);
lean_inc_ref(v_lctx_1501_);
v_expr_1502_ = lean_ctor_get(v_ti_1498_, 3);
lean_inc_ref(v_expr_1502_);
lean_dec_ref(v_ti_1498_);
v_stx_1503_ = lean_ctor_get(v_toElabInfo_1500_, 1);
lean_inc(v_stx_1503_);
lean_dec_ref(v_toElabInfo_1500_);
v___x_1504_ = 1;
v___x_1505_ = l_Lean_Syntax_getPos_x3f(v_stx_1503_, v___x_1504_);
if (lean_obj_tag(v___x_1505_) == 1)
{
lean_object* v_val_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1571_; 
v_val_1506_ = lean_ctor_get(v___x_1505_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1505_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1508_ = v___x_1505_;
v_isShared_1509_ = v_isSharedCheck_1571_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_val_1506_);
lean_dec(v___x_1505_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1571_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1503_, v___x_1504_);
lean_dec(v_stx_1503_);
if (lean_obj_tag(v___x_1510_) == 1)
{
lean_object* v_val_1511_; lean_object* v___f_1512_; lean_object* v___x_1513_; 
lean_del_object(v___x_1508_);
v_val_1511_ = lean_ctor_get(v___x_1510_, 0);
lean_inc(v_val_1511_);
lean_dec_ref(v___x_1510_);
v___f_1512_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_1512_, 0, v_expr_1502_);
lean_inc_ref(v_ctx_1497_);
v___x_1513_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1497_, v_lctx_1501_, v___f_1512_);
if (lean_obj_tag(v___x_1513_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; uint8_t v_isShared_1517_; uint8_t v_isSharedCheck_1558_; 
v_a_1514_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1516_ = v___x_1513_;
v_isShared_1517_ = v_isSharedCheck_1558_;
goto v_resetjp_1515_;
}
else
{
lean_inc(v_a_1514_);
lean_dec(v___x_1513_);
v___x_1516_ = lean_box(0);
v_isShared_1517_ = v_isSharedCheck_1558_;
goto v_resetjp_1515_;
}
v_resetjp_1515_:
{
if (lean_obj_tag(v_a_1514_) == 1)
{
lean_object* v_val_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1553_; 
v_val_1518_ = lean_ctor_get(v_a_1514_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_a_1514_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1520_ = v_a_1514_;
v_isShared_1521_ = v_isSharedCheck_1553_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_val_1518_);
lean_dec(v_a_1514_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1553_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1522_ = lean_array_get_size(v_val_1518_);
v___x_1523_ = lean_unsigned_to_nat(0u);
v___x_1524_ = lean_nat_dec_eq(v___x_1522_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v_toEditableDocumentCore_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1547_; 
v_toEditableDocumentCore_1525_ = lean_ctor_get(v_doc_1496_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_doc_1496_);
if (v_isSharedCheck_1547_ == 0)
{
lean_object* v_unused_1548_; 
v_unused_1548_ = lean_ctor_get(v_doc_1496_, 1);
lean_dec(v_unused_1548_);
v___x_1527_ = v_doc_1496_;
v_isShared_1528_ = v_isSharedCheck_1547_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_toEditableDocumentCore_1525_);
lean_dec(v_doc_1496_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1547_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v_meta_1529_; lean_object* v_text_1530_; lean_object* v_source_1531_; lean_object* v___f_1532_; lean_object* v___x_1533_; size_t v_sz_1534_; size_t v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v_meta_1529_ = lean_ctor_get(v_toEditableDocumentCore_1525_, 0);
lean_inc_ref(v_meta_1529_);
lean_dec_ref(v_toEditableDocumentCore_1525_);
v_text_1530_ = lean_ctor_get(v_meta_1529_, 3);
lean_inc_ref(v_text_1530_);
lean_dec_ref(v_meta_1529_);
v_source_1531_ = lean_ctor_get(v_text_1530_, 0);
lean_inc_ref(v_source_1531_);
lean_inc(v_val_1511_);
lean_inc(v_val_1506_);
v___f_1532_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotQuery_x3f___lam__1), 4, 3);
lean_closure_set(v___f_1532_, 0, v_val_1506_);
lean_closure_set(v___f_1532_, 1, v_val_1511_);
lean_closure_set(v___f_1532_, 2, v_text_1530_);
v___x_1533_ = lean_string_utf8_extract(v_source_1531_, v_val_1506_, v_val_1511_);
lean_dec(v_val_1511_);
lean_dec(v_val_1506_);
lean_dec_ref(v_source_1531_);
v_sz_1534_ = lean_array_size(v_val_1518_);
v___x_1535_ = ((size_t)0ULL);
v___x_1536_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_1534_, v___x_1535_, v_val_1518_);
if (v_isShared_1528_ == 0)
{
lean_ctor_set(v___x_1527_, 1, v___x_1536_);
lean_ctor_set(v___x_1527_, 0, v___x_1533_);
v___x_1538_ = v___x_1527_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1533_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1539_, 0, v___x_1538_);
lean_ctor_set(v___x_1539_, 1, v_ctx_1497_);
lean_ctor_set(v___x_1539_, 2, v___f_1532_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 0, v___x_1539_);
v___x_1541_ = v___x_1520_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1545_; 
v_reuseFailAlloc_1545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1545_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1541_);
v___x_1543_ = v___x_1516_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_del_object(v___x_1520_);
lean_dec(v_val_1518_);
lean_dec(v_val_1511_);
lean_dec(v_val_1506_);
lean_dec_ref(v_ctx_1497_);
lean_dec_ref(v_doc_1496_);
v___x_1549_ = lean_box(0);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1549_);
v___x_1551_ = v___x_1516_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
else
{
lean_object* v___x_1554_; lean_object* v___x_1556_; 
lean_dec(v_a_1514_);
lean_dec(v_val_1511_);
lean_dec(v_val_1506_);
lean_dec_ref(v_ctx_1497_);
lean_dec_ref(v_doc_1496_);
v___x_1554_ = lean_box(0);
if (v_isShared_1517_ == 0)
{
lean_ctor_set(v___x_1516_, 0, v___x_1554_);
v___x_1556_ = v___x_1516_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec(v_val_1511_);
lean_dec(v_val_1506_);
lean_dec_ref(v_ctx_1497_);
lean_dec_ref(v_doc_1496_);
v_a_1559_ = lean_ctor_get(v___x_1513_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1513_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1513_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1513_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
else
{
lean_object* v___x_1567_; lean_object* v___x_1569_; 
lean_dec(v___x_1510_);
lean_dec(v_val_1506_);
lean_dec_ref(v_expr_1502_);
lean_dec_ref(v_lctx_1501_);
lean_dec_ref(v_ctx_1497_);
lean_dec_ref(v_doc_1496_);
v___x_1567_ = lean_box(0);
if (v_isShared_1509_ == 0)
{
lean_ctor_set_tag(v___x_1508_, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1567_);
v___x_1569_ = v___x_1508_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
lean_dec(v___x_1505_);
lean_dec(v_stx_1503_);
lean_dec_ref(v_expr_1502_);
lean_dec_ref(v_lctx_1501_);
lean_dec_ref(v_ctx_1497_);
lean_dec_ref(v_doc_1496_);
v___x_1572_ = lean_box(0);
v___x_1573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1573_, 0, v___x_1572_);
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotQuery_x3f___boxed(lean_object* v_doc_1574_, lean_object* v_ctx_1575_, lean_object* v_ti_1576_, lean_object* v_a_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_Server_FileWorker_computeDotQuery_x3f(v_doc_1574_, v_ctx_1575_, v_ti_1576_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0(lean_object* v_doc_1579_, lean_object* v_val_1580_, lean_object* v_val_1581_, lean_object* v_decl_1582_){
_start:
{
lean_object* v_toEditableDocumentCore_1583_; lean_object* v___x_1585_; uint8_t v_isShared_1586_; uint8_t v_isSharedCheck_1606_; 
v_toEditableDocumentCore_1583_ = lean_ctor_get(v_doc_1579_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_doc_1579_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; 
v_unused_1607_ = lean_ctor_get(v_doc_1579_, 1);
lean_dec(v_unused_1607_);
v___x_1585_ = v_doc_1579_;
v_isShared_1586_ = v_isSharedCheck_1606_;
goto v_resetjp_1584_;
}
else
{
lean_inc(v_toEditableDocumentCore_1583_);
lean_dec(v_doc_1579_);
v___x_1585_ = lean_box(0);
v_isShared_1586_ = v_isSharedCheck_1606_;
goto v_resetjp_1584_;
}
v_resetjp_1584_:
{
lean_object* v_meta_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1602_; 
v_meta_1587_ = lean_ctor_get(v_toEditableDocumentCore_1583_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v_toEditableDocumentCore_1583_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; lean_object* v_unused_1604_; lean_object* v_unused_1605_; 
v_unused_1603_ = lean_ctor_get(v_toEditableDocumentCore_1583_, 3);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_toEditableDocumentCore_1583_, 2);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_toEditableDocumentCore_1583_, 1);
lean_dec(v_unused_1605_);
v___x_1589_ = v_toEditableDocumentCore_1583_;
v_isShared_1590_ = v_isSharedCheck_1602_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_meta_1587_);
lean_dec(v_toEditableDocumentCore_1583_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1602_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v_text_1591_; lean_object* v___x_1593_; 
v_text_1591_ = lean_ctor_get(v_meta_1587_, 3);
lean_inc_ref(v_text_1591_);
lean_dec_ref(v_meta_1587_);
if (v_isShared_1586_ == 0)
{
lean_ctor_set(v___x_1585_, 1, v_val_1581_);
lean_ctor_set(v___x_1585_, 0, v_val_1580_);
v___x_1593_ = v___x_1585_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v_val_1580_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_val_1581_);
v___x_1593_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1594_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1591_, v___x_1593_);
v___x_1595_ = l_Lean_Name_getString_x21(v_decl_1582_);
v___x_1596_ = lean_box(0);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 3, v___x_1596_);
lean_ctor_set(v___x_1589_, 2, v___x_1596_);
lean_ctor_set(v___x_1589_, 1, v___x_1595_);
lean_ctor_set(v___x_1589_, 0, v___x_1594_);
v___x_1598_ = v___x_1589_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1599_, 0, v_decl_1582_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
return v___x_1599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f(lean_object* v_doc_1608_, lean_object* v_ctx_1609_, lean_object* v_stx_1610_, lean_object* v_id_1611_, lean_object* v_lctx_1612_, lean_object* v_expectedType_x3f_1613_){
_start:
{
uint8_t v___x_1615_; lean_object* v___x_1616_; 
v___x_1615_ = 1;
v___x_1616_ = l_Lean_Syntax_getPos_x3f(v_stx_1610_, v___x_1615_);
if (lean_obj_tag(v___x_1616_) == 1)
{
lean_object* v_val_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1676_; 
v_val_1617_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1676_ == 0)
{
v___x_1619_ = v___x_1616_;
v_isShared_1620_ = v_isSharedCheck_1676_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_val_1617_);
lean_dec(v___x_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1676_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1610_, v___x_1615_);
if (lean_obj_tag(v___x_1621_) == 1)
{
lean_del_object(v___x_1619_);
if (lean_obj_tag(v_expectedType_x3f_1613_) == 1)
{
lean_object* v_val_1622_; lean_object* v_val_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1662_; 
v_val_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_val_1622_);
lean_dec_ref(v___x_1621_);
v_val_1623_ = lean_ctor_get(v_expectedType_x3f_1613_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_expectedType_x3f_1613_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1625_ = v_expectedType_x3f_1613_;
v_isShared_1626_ = v_isSharedCheck_1662_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_val_1623_);
lean_dec(v_expectedType_x3f_1613_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1662_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_alloc_closure((void*)(l_Lean_Server_Completion_getDotIdCompletionTypeNames___boxed), 6, 1);
lean_closure_set(v___x_1627_, 0, v_val_1623_);
lean_inc_ref(v_ctx_1609_);
v___x_1628_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_1609_, v_lctx_1612_, v___x_1627_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1653_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1653_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1653_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1633_ = lean_array_get_size(v_a_1629_);
v___x_1634_ = lean_unsigned_to_nat(0u);
v___x_1635_ = lean_nat_dec_eq(v___x_1633_, v___x_1634_);
if (v___x_1635_ == 0)
{
lean_object* v___f_1636_; lean_object* v___x_1637_; size_t v_sz_1638_; size_t v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___f_1636_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_computeDotIdQuery_x3f___lam__0), 4, 3);
lean_closure_set(v___f_1636_, 0, v_doc_1608_);
lean_closure_set(v___f_1636_, 1, v_val_1617_);
lean_closure_set(v___f_1636_, 2, v_val_1622_);
v___x_1637_ = l_Lean_Name_toString(v_id_1611_, v___x_1615_);
v_sz_1638_ = lean_array_size(v_a_1629_);
v___x_1639_ = ((size_t)0ULL);
v___x_1640_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_computeDotQuery_x3f_spec__1(v_sz_1638_, v___x_1639_, v_a_1629_);
v___x_1641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1641_, 0, v___x_1637_);
lean_ctor_set(v___x_1641_, 1, v___x_1640_);
v___x_1642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1642_, 0, v___x_1641_);
lean_ctor_set(v___x_1642_, 1, v_ctx_1609_);
lean_ctor_set(v___x_1642_, 2, v___f_1636_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1642_);
v___x_1644_ = v___x_1625_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
lean_object* v___x_1646_; 
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1644_);
v___x_1646_ = v___x_1631_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
else
{
lean_object* v___x_1649_; lean_object* v___x_1651_; 
lean_dec(v_a_1629_);
lean_del_object(v___x_1625_);
lean_dec(v_val_1622_);
lean_dec(v_val_1617_);
lean_dec(v_id_1611_);
lean_dec_ref(v_ctx_1609_);
lean_dec_ref(v_doc_1608_);
v___x_1649_ = lean_box(0);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v___x_1649_);
v___x_1651_ = v___x_1631_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v___x_1649_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
else
{
lean_object* v_a_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1661_; 
lean_del_object(v___x_1625_);
lean_dec(v_val_1622_);
lean_dec(v_val_1617_);
lean_dec(v_id_1611_);
lean_dec_ref(v_ctx_1609_);
lean_dec_ref(v_doc_1608_);
v_a_1654_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1656_ = v___x_1628_;
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_a_1654_);
lean_dec(v___x_1628_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1661_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1659_; 
if (v_isShared_1657_ == 0)
{
v___x_1659_ = v___x_1656_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1654_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
}
else
{
lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1670_; 
lean_dec(v_val_1617_);
lean_dec(v_expectedType_x3f_1613_);
lean_dec_ref(v_lctx_1612_);
lean_dec(v_id_1611_);
lean_dec_ref(v_ctx_1609_);
lean_dec_ref(v_doc_1608_);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1670_ == 0)
{
lean_object* v_unused_1671_; 
v_unused_1671_ = lean_ctor_get(v___x_1621_, 0);
lean_dec(v_unused_1671_);
v___x_1664_ = v___x_1621_;
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
else
{
lean_dec(v___x_1621_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1670_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1666_; lean_object* v___x_1668_; 
v___x_1666_ = lean_box(0);
if (v_isShared_1665_ == 0)
{
lean_ctor_set_tag(v___x_1664_, 0);
lean_ctor_set(v___x_1664_, 0, v___x_1666_);
v___x_1668_ = v___x_1664_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v___x_1666_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v___x_1672_; lean_object* v___x_1674_; 
lean_dec(v___x_1621_);
lean_dec(v_val_1617_);
lean_dec(v_expectedType_x3f_1613_);
lean_dec_ref(v_lctx_1612_);
lean_dec(v_id_1611_);
lean_dec_ref(v_ctx_1609_);
lean_dec_ref(v_doc_1608_);
v___x_1672_ = lean_box(0);
if (v_isShared_1620_ == 0)
{
lean_ctor_set_tag(v___x_1619_, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1672_);
v___x_1674_ = v___x_1619_;
goto v_reusejp_1673_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v___x_1672_);
v___x_1674_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1673_;
}
v_reusejp_1673_:
{
return v___x_1674_;
}
}
}
}
else
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
lean_dec(v___x_1616_);
lean_dec(v_expectedType_x3f_1613_);
lean_dec_ref(v_lctx_1612_);
lean_dec(v_id_1611_);
lean_dec_ref(v_ctx_1609_);
lean_dec_ref(v_doc_1608_);
v___x_1677_ = lean_box(0);
v___x_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1678_, 0, v___x_1677_);
return v___x_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeDotIdQuery_x3f___boxed(lean_object* v_doc_1679_, lean_object* v_ctx_1680_, lean_object* v_stx_1681_, lean_object* v_id_1682_, lean_object* v_lctx_1683_, lean_object* v_expectedType_x3f_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(v_doc_1679_, v_ctx_1680_, v_stx_1681_, v_id_1682_, v_lctx_1683_, v_expectedType_x3f_1684_);
lean_dec(v_stx_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(lean_object* v_doc_1687_, lean_object* v_as_1688_, size_t v_sz_1689_, size_t v_i_1690_, lean_object* v_b_1691_){
_start:
{
lean_object* v_a_1694_; lean_object* v_query_x3f_1699_; uint8_t v___x_1702_; 
v___x_1702_ = lean_usize_dec_lt(v_i_1690_, v_sz_1689_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; 
lean_dec_ref(v_doc_1687_);
v___x_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_b_1691_);
return v___x_1703_;
}
else
{
lean_object* v_a_1704_; lean_object* v_fst_1705_; lean_object* v_info_1706_; 
v_a_1704_ = lean_array_uget_borrowed(v_as_1688_, v_i_1690_);
v_fst_1705_ = lean_ctor_get(v_a_1704_, 0);
v_info_1706_ = lean_ctor_get(v_fst_1705_, 2);
switch(lean_obj_tag(v_info_1706_))
{
case 1:
{
lean_object* v_ctx_1707_; lean_object* v_stx_1708_; lean_object* v_id_1709_; lean_object* v___x_1710_; 
v_ctx_1707_ = lean_ctor_get(v_fst_1705_, 1);
v_stx_1708_ = lean_ctor_get(v_info_1706_, 0);
v_id_1709_ = lean_ctor_get(v_info_1706_, 1);
lean_inc(v_id_1709_);
lean_inc_ref(v_ctx_1707_);
lean_inc_ref(v_doc_1687_);
v___x_1710_ = l_Lean_Server_FileWorker_computeIdQuery_x3f(v_doc_1687_, v_ctx_1707_, v_stx_1708_, v_id_1709_);
v_query_x3f_1699_ = v___x_1710_;
goto v___jp_1698_;
}
case 0:
{
lean_object* v_ctx_1711_; lean_object* v_termInfo_1712_; lean_object* v___x_1713_; 
v_ctx_1711_ = lean_ctor_get(v_fst_1705_, 1);
v_termInfo_1712_ = lean_ctor_get(v_info_1706_, 0);
lean_inc_ref(v_termInfo_1712_);
lean_inc_ref(v_ctx_1711_);
lean_inc_ref(v_doc_1687_);
v___x_1713_ = l_Lean_Server_FileWorker_computeDotQuery_x3f(v_doc_1687_, v_ctx_1711_, v_termInfo_1712_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref(v___x_1713_);
v_query_x3f_1699_ = v_a_1714_;
goto v___jp_1698_;
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1723_; 
lean_dec_ref(v_b_1691_);
lean_dec_ref(v_doc_1687_);
v_a_1715_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1717_ = v___x_1713_;
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1713_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1723_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1719_; lean_object* v___x_1721_; 
v___x_1719_ = l_Lean_Server_RequestError_ofIoError(v_a_1715_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1719_);
v___x_1721_ = v___x_1717_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
case 2:
{
lean_object* v_ctx_1724_; lean_object* v_stx_1725_; lean_object* v_id_1726_; lean_object* v_lctx_1727_; lean_object* v_expectedType_x3f_1728_; lean_object* v___x_1729_; 
v_ctx_1724_ = lean_ctor_get(v_fst_1705_, 1);
v_stx_1725_ = lean_ctor_get(v_info_1706_, 0);
v_id_1726_ = lean_ctor_get(v_info_1706_, 1);
v_lctx_1727_ = lean_ctor_get(v_info_1706_, 2);
v_expectedType_x3f_1728_ = lean_ctor_get(v_info_1706_, 3);
lean_inc(v_expectedType_x3f_1728_);
lean_inc_ref(v_lctx_1727_);
lean_inc(v_id_1726_);
lean_inc_ref(v_ctx_1724_);
lean_inc_ref(v_doc_1687_);
v___x_1729_ = l_Lean_Server_FileWorker_computeDotIdQuery_x3f(v_doc_1687_, v_ctx_1724_, v_stx_1725_, v_id_1726_, v_lctx_1727_, v_expectedType_x3f_1728_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref(v___x_1729_);
v_query_x3f_1699_ = v_a_1730_;
goto v___jp_1698_;
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1739_; 
lean_dec_ref(v_b_1691_);
lean_dec_ref(v_doc_1687_);
v_a_1731_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1733_ = v___x_1729_;
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1729_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = l_Lean_Server_RequestError_ofIoError(v_a_1731_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v___x_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
default: 
{
v_a_1694_ = v_b_1691_;
goto v___jp_1693_;
}
}
}
v___jp_1693_:
{
size_t v___x_1695_; size_t v___x_1696_; 
v___x_1695_ = ((size_t)1ULL);
v___x_1696_ = lean_usize_add(v_i_1690_, v___x_1695_);
v_i_1690_ = v___x_1696_;
v_b_1691_ = v_a_1694_;
goto _start;
}
v___jp_1698_:
{
if (lean_obj_tag(v_query_x3f_1699_) == 1)
{
lean_object* v_val_1700_; lean_object* v___x_1701_; 
v_val_1700_ = lean_ctor_get(v_query_x3f_1699_, 0);
lean_inc(v_val_1700_);
lean_dec_ref(v_query_x3f_1699_);
v___x_1701_ = lean_array_push(v_b_1691_, v_val_1700_);
v_a_1694_ = v___x_1701_;
goto v___jp_1693_;
}
else
{
lean_dec(v_query_x3f_1699_);
v_a_1694_ = v_b_1691_;
goto v___jp_1693_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg___boxed(lean_object* v_doc_1740_, lean_object* v_as_1741_, lean_object* v_sz_1742_, lean_object* v_i_1743_, lean_object* v_b_1744_, lean_object* v___y_1745_){
_start:
{
size_t v_sz_boxed_1746_; size_t v_i_boxed_1747_; lean_object* v_res_1748_; 
v_sz_boxed_1746_ = lean_unbox_usize(v_sz_1742_);
lean_dec(v_sz_1742_);
v_i_boxed_1747_ = lean_unbox_usize(v_i_1743_);
lean_dec(v_i_1743_);
v_res_1748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_1740_, v_as_1741_, v_sz_boxed_1746_, v_i_boxed_1747_, v_b_1744_);
lean_dec_ref(v_as_1741_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(lean_object* v_doc_1749_, lean_object* v_as_1750_, size_t v_sz_1751_, size_t v_i_1752_, lean_object* v_b_1753_, lean_object* v___y_1754_){
_start:
{
uint8_t v___x_1756_; 
v___x_1756_ = lean_usize_dec_lt(v_i_1752_, v_sz_1751_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec_ref(v_doc_1749_);
v___x_1757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_b_1753_);
return v___x_1757_;
}
else
{
lean_object* v_a_1758_; size_t v_sz_1759_; size_t v___x_1760_; lean_object* v___x_1761_; 
v_a_1758_ = lean_array_uget_borrowed(v_as_1750_, v_i_1752_);
v_sz_1759_ = lean_array_size(v_a_1758_);
v___x_1760_ = ((size_t)0ULL);
lean_inc_ref(v_doc_1749_);
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_1749_, v_a_1758_, v_sz_1759_, v___x_1760_, v_b_1753_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_a_1762_);
v___x_1763_ = lean_array_get_size(v_a_1762_);
v___x_1764_ = lean_unsigned_to_nat(0u);
v___x_1765_ = lean_nat_dec_eq(v___x_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_dec(v_a_1762_);
lean_dec_ref(v_doc_1749_);
return v___x_1761_;
}
else
{
size_t v___x_1766_; size_t v___x_1767_; 
lean_dec_ref(v___x_1761_);
v___x_1766_ = ((size_t)1ULL);
v___x_1767_ = lean_usize_add(v_i_1752_, v___x_1766_);
v_i_1752_ = v___x_1767_;
v_b_1753_ = v_a_1762_;
goto _start;
}
}
else
{
lean_dec_ref(v_doc_1749_);
return v___x_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1___boxed(lean_object* v_doc_1769_, lean_object* v_as_1770_, lean_object* v_sz_1771_, lean_object* v_i_1772_, lean_object* v_b_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
size_t v_sz_boxed_1776_; size_t v_i_boxed_1777_; lean_object* v_res_1778_; 
v_sz_boxed_1776_ = lean_unbox_usize(v_sz_1771_);
lean_dec(v_sz_1771_);
v_i_boxed_1777_ = lean_unbox_usize(v_i_1772_);
lean_dec(v_i_1772_);
v_res_1778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_1769_, v_as_1770_, v_sz_boxed_1776_, v_i_boxed_1777_, v_b_1773_, v___y_1774_);
lean_dec_ref(v___y_1774_);
lean_dec_ref(v_as_1770_);
return v_res_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries(lean_object* v_doc_1781_, lean_object* v_requestedPos_1782_, lean_object* v_a_1783_){
_start:
{
lean_object* v_toEditableDocumentCore_1785_; uint8_t v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v_toEditableDocumentCore_1785_ = lean_ctor_get(v_doc_1781_, 0);
v___x_1786_ = 1;
lean_inc(v_requestedPos_1782_);
lean_inc_ref(v_doc_1781_);
v___x_1787_ = l_Lean_Server_RequestM_findCmdDataAtPos(v_doc_1781_, v_requestedPos_1782_, v___x_1786_);
v___x_1788_ = lean_task_get_own(v___x_1787_);
if (lean_obj_tag(v___x_1788_) == 1)
{
lean_object* v_val_1789_; lean_object* v_meta_1790_; lean_object* v_fst_1791_; lean_object* v_snd_1792_; lean_object* v_text_1793_; lean_object* v___x_1794_; lean_object* v_fst_1795_; lean_object* v_queries_1796_; size_t v_sz_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
v_val_1789_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_val_1789_);
lean_dec_ref(v___x_1788_);
v_meta_1790_ = lean_ctor_get(v_toEditableDocumentCore_1785_, 0);
v_fst_1791_ = lean_ctor_get(v_val_1789_, 0);
lean_inc(v_fst_1791_);
v_snd_1792_ = lean_ctor_get(v_val_1789_, 1);
lean_inc(v_snd_1792_);
lean_dec(v_val_1789_);
v_text_1793_ = lean_ctor_get(v_meta_1790_, 3);
lean_inc_ref(v_text_1793_);
v___x_1794_ = l_Lean_Server_Completion_findPrioritizedCompletionPartitionsAt(v_text_1793_, v_requestedPos_1782_, v_fst_1791_, v_snd_1792_);
v_fst_1795_ = lean_ctor_get(v___x_1794_, 0);
lean_inc(v_fst_1795_);
lean_dec_ref(v___x_1794_);
v_queries_1796_ = ((lean_object*)(l_Lean_Server_FileWorker_computeQueries___closed__0));
v_sz_1797_ = lean_array_size(v_fst_1795_);
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__1(v_doc_1781_, v_fst_1795_, v_sz_1797_, v___x_1798_, v_queries_1796_, v_a_1783_);
lean_dec(v_fst_1795_);
return v___x_1799_;
}
else
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
lean_dec(v___x_1788_);
lean_dec(v_requestedPos_1782_);
lean_dec_ref(v_doc_1781_);
v___x_1800_ = ((lean_object*)(l_Lean_Server_FileWorker_computeQueries___closed__0));
v___x_1801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1801_, 0, v___x_1800_);
return v___x_1801_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_computeQueries___boxed(lean_object* v_doc_1802_, lean_object* v_requestedPos_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lean_Server_FileWorker_computeQueries(v_doc_1802_, v_requestedPos_1803_, v_a_1804_);
lean_dec_ref(v_a_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(lean_object* v_doc_1807_, lean_object* v_as_1808_, size_t v_sz_1809_, size_t v_i_1810_, lean_object* v_b_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___redArg(v_doc_1807_, v_as_1808_, v_sz_1809_, v_i_1810_, v_b_1811_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0___boxed(lean_object* v_doc_1815_, lean_object* v_as_1816_, lean_object* v_sz_1817_, lean_object* v_i_1818_, lean_object* v_b_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
size_t v_sz_boxed_1822_; size_t v_i_boxed_1823_; lean_object* v_res_1824_; 
v_sz_boxed_1822_ = lean_unbox_usize(v_sz_1817_);
lean_dec(v_sz_1817_);
v_i_boxed_1823_ = lean_unbox_usize(v_i_1818_);
lean_dec(v_i_1818_);
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_computeQueries_spec__0(v_doc_1815_, v_as_1816_, v_sz_boxed_1822_, v_i_boxed_1823_, v_b_1819_, v___y_1820_);
lean_dec_ref(v___y_1820_);
lean_dec_ref(v_as_1816_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(lean_object* v_params_1833_, lean_object* v_name_1834_){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1836_, 0, v_params_1833_);
lean_ctor_set(v___x_1836_, 1, v_name_1834_);
lean_ctor_set(v___x_1836_, 2, v___x_1835_);
return v___x_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(lean_object* v_params_1838_, lean_object* v_kind_1839_){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1840_ = lean_box(0);
v___x_1841_ = ((lean_object*)(l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction___closed__0));
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_kind_1839_);
v___x_1843_ = ((lean_object*)(l_Lean_Server_FileWorker_importAllUnknownIdentifiersProvider));
v___x_1844_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_1838_, v___x_1843_);
v___x_1845_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_1844_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
v___x_1847_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1840_);
lean_ctor_set(v___x_1847_, 1, v___x_1840_);
lean_ctor_set(v___x_1847_, 2, v___x_1841_);
lean_ctor_set(v___x_1847_, 3, v___x_1842_);
lean_ctor_set(v___x_1847_, 4, v___x_1840_);
lean_ctor_set(v___x_1847_, 5, v___x_1840_);
lean_ctor_set(v___x_1847_, 6, v___x_1840_);
lean_ctor_set(v___x_1847_, 7, v___x_1840_);
lean_ctor_set(v___x_1847_, 8, v___x_1840_);
lean_ctor_set(v___x_1847_, 9, v___x_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(lean_object* v_ctx_1852_, lean_object* v_mod_1853_){
_start:
{
lean_object* v_toCommandContextInfo_1854_; lean_object* v_parentDecl_x3f_1855_; lean_object* v___x_1856_; uint8_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_text_1861_; 
v_toCommandContextInfo_1854_ = lean_ctor_get(v_ctx_1852_, 0);
lean_inc_ref(v_toCommandContextInfo_1854_);
v_parentDecl_x3f_1855_ = lean_ctor_get(v_ctx_1852_, 1);
lean_inc(v_parentDecl_x3f_1855_);
lean_dec_ref(v_ctx_1852_);
v___x_1856_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__0));
v___x_1857_ = 1;
v___x_1858_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_mod_1853_, v___x_1857_);
v___x_1859_ = lean_string_append(v___x_1856_, v___x_1858_);
lean_dec_ref(v___x_1858_);
v___x_1860_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1));
v_text_1861_ = lean_string_append(v___x_1859_, v___x_1860_);
if (lean_obj_tag(v_parentDecl_x3f_1855_) == 1)
{
lean_object* v_val_1862_; lean_object* v_env_1863_; uint8_t v___x_1864_; 
v_val_1862_ = lean_ctor_get(v_parentDecl_x3f_1855_, 0);
lean_inc_n(v_val_1862_, 2);
lean_dec_ref(v_parentDecl_x3f_1855_);
v_env_1863_ = lean_ctor_get(v_toCommandContextInfo_1854_, 0);
lean_inc_ref_n(v_env_1863_, 2);
lean_dec_ref(v_toCommandContextInfo_1854_);
v___x_1864_ = l_Lean_isMarkedMeta(v_env_1863_, v_val_1862_);
if (v___x_1864_ == 0)
{
uint8_t v_isExporting_1865_; 
lean_dec(v_val_1862_);
v_isExporting_1865_ = lean_ctor_get_uint8(v_env_1863_, sizeof(void*)*8);
lean_dec_ref(v_env_1863_);
if (v_isExporting_1865_ == 0)
{
return v_text_1861_;
}
else
{
lean_object* v___x_1866_; lean_object* v_text_1867_; 
v___x_1866_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2));
v_text_1867_ = lean_string_append(v___x_1866_, v_text_1861_);
lean_dec_ref(v_text_1861_);
return v_text_1867_;
}
}
else
{
lean_object* v___x_1868_; lean_object* v_text_1869_; uint8_t v___x_1870_; 
lean_dec_ref(v_env_1863_);
v___x_1868_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__3));
v_text_1869_ = lean_string_append(v___x_1868_, v_text_1861_);
lean_dec_ref(v_text_1861_);
v___x_1870_ = l_Lean_isPrivateName(v_val_1862_);
lean_dec(v_val_1862_);
if (v___x_1870_ == 0)
{
if (v___x_1864_ == 0)
{
return v_text_1869_;
}
else
{
lean_object* v___x_1871_; lean_object* v_text_1872_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__2));
v_text_1872_ = lean_string_append(v___x_1871_, v_text_1869_);
lean_dec_ref(v_text_1869_);
return v_text_1872_;
}
}
else
{
return v_text_1869_;
}
}
}
else
{
lean_dec(v_parentDecl_x3f_1855_);
lean_dec_ref(v_toCommandContextInfo_1854_);
return v_text_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0(lean_object* v_x_1874_){
_start:
{
if (lean_obj_tag(v_x_1874_) == 0)
{
lean_object* v_response_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1893_; 
v_response_1875_ = lean_ctor_get(v_x_1874_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_x_1874_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1877_ = v_x_1874_;
v_isShared_1878_ = v_isSharedCheck_1893_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_response_1875_);
lean_dec(v_x_1874_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1893_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1879_; 
lean_inc(v_response_1875_);
v___x_1879_ = l_Lean_Lsp_instFromJsonLeanQueryModuleResponse_fromJson(v_response_1875_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; uint8_t v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
lean_del_object(v___x_1877_);
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref(v___x_1879_);
v___x_1881_ = 0;
v___x_1882_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___lam__0___closed__0));
v___x_1883_ = l_Lean_Json_compress(v_response_1875_);
v___x_1884_ = lean_string_append(v___x_1882_, v___x_1883_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = ((lean_object*)(l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText___closed__1));
v___x_1886_ = lean_string_append(v___x_1884_, v___x_1885_);
v___x_1887_ = lean_string_append(v___x_1886_, v_a_1880_);
lean_dec(v_a_1880_);
v___x_1888_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set_uint8(v___x_1888_, sizeof(void*)*1, v___x_1881_);
return v___x_1888_;
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; 
lean_dec(v_response_1875_);
v_a_1889_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1889_);
lean_dec_ref(v___x_1879_);
if (v_isShared_1878_ == 0)
{
lean_ctor_set(v___x_1877_, 0, v_a_1889_);
v___x_1891_ = v___x_1877_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1889_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
else
{
uint8_t v_code_1894_; lean_object* v_message_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
v_code_1894_ = lean_ctor_get_uint8(v_x_1874_, sizeof(void*)*1);
v_message_1895_ = lean_ctor_get(v_x_1874_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_x_1874_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v_x_1874_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_message_1895_);
lean_dec(v_x_1874_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 1);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_message_1895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1901_, sizeof(void*)*1, v_code_1894_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(lean_object* v_method_1904_, lean_object* v_param_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_serverRequestEmitter_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___f_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v_serverRequestEmitter_1908_ = lean_ctor_get(v_a_1906_, 5);
v___x_1909_ = l_Lean_Lsp_instToJsonLeanQueryModuleParams_toJson(v_param_1905_);
lean_inc_ref(v_serverRequestEmitter_1908_);
v___x_1910_ = lean_apply_3(v_serverRequestEmitter_1908_, v_method_1904_, v___x_1909_, lean_box(0));
v___f_1911_ = ((lean_object*)(l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___closed__0));
v___x_1912_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_1911_, v___x_1910_);
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v___x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1___boxed(lean_object* v_method_1914_, lean_object* v_param_1915_, lean_object* v_a_1916_, lean_object* v_a_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v_method_1914_, v_param_1915_, v_a_1916_);
lean_dec_ref(v_a_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__0(lean_object* v_val_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v_val_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___lam__1(lean_object* v_val_1921_){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v_val_1921_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(size_t v_sz_1923_, size_t v_i_1924_, lean_object* v_bs_1925_){
_start:
{
uint8_t v___x_1926_; 
v___x_1926_ = lean_usize_dec_lt(v_i_1924_, v_sz_1923_);
if (v___x_1926_ == 0)
{
return v_bs_1925_;
}
else
{
lean_object* v_v_1927_; lean_object* v_toLeanModuleQuery_1928_; lean_object* v___x_1929_; lean_object* v_bs_x27_1930_; size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v_v_1927_ = lean_array_uget_borrowed(v_bs_1925_, v_i_1924_);
v_toLeanModuleQuery_1928_ = lean_ctor_get(v_v_1927_, 0);
lean_inc_ref(v_toLeanModuleQuery_1928_);
v___x_1929_ = lean_unsigned_to_nat(0u);
v_bs_x27_1930_ = lean_array_uset(v_bs_1925_, v_i_1924_, v___x_1929_);
v___x_1931_ = ((size_t)1ULL);
v___x_1932_ = lean_usize_add(v_i_1924_, v___x_1931_);
v___x_1933_ = lean_array_uset(v_bs_x27_1930_, v_i_1924_, v_toLeanModuleQuery_1928_);
v_i_1924_ = v___x_1932_;
v_bs_1925_ = v___x_1933_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0___boxed(lean_object* v_sz_1935_, lean_object* v_i_1936_, lean_object* v_bs_1937_){
_start:
{
size_t v_sz_boxed_1938_; size_t v_i_boxed_1939_; lean_object* v_res_1940_; 
v_sz_boxed_1938_ = lean_unbox_usize(v_sz_1935_);
lean_dec(v_sz_1935_);
v_i_boxed_1939_ = lean_unbox_usize(v_i_1936_);
lean_dec(v_i_1936_);
v_res_1940_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_boxed_1938_, v_i_boxed_1939_, v_bs_1937_);
return v_res_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(lean_object* v_a_1944_, lean_object* v_kind_1945_, lean_object* v___x_1946_, lean_object* v_params_1947_, lean_object* v___x_1948_, lean_object* v___x_1949_, lean_object* v_as_1950_, size_t v_sz_1951_, size_t v_i_1952_, lean_object* v_b_1953_){
_start:
{
lean_object* v_a_1956_; uint8_t v___x_1960_; 
v___x_1960_ = lean_usize_dec_lt(v_i_1952_, v_sz_1951_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; 
lean_dec_ref(v___x_1948_);
lean_dec_ref(v_params_1947_);
lean_dec_ref(v___x_1946_);
lean_dec_ref(v_kind_1945_);
lean_dec_ref(v_a_1944_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v_b_1953_);
return v___x_1961_;
}
else
{
lean_object* v_a_1962_; lean_object* v_module_1963_; lean_object* v_decl_1964_; uint8_t v_isExactMatch_1965_; lean_object* v_fst_1966_; lean_object* v_snd_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_2058_; 
v_a_1962_ = lean_array_uget_borrowed(v_as_1950_, v_i_1952_);
v_module_1963_ = lean_ctor_get(v_a_1962_, 0);
v_decl_1964_ = lean_ctor_get(v_a_1962_, 1);
v_isExactMatch_1965_ = lean_ctor_get_uint8(v_a_1962_, sizeof(void*)*2);
v_fst_1966_ = lean_ctor_get(v_b_1953_, 0);
v_snd_1967_ = lean_ctor_get(v_b_1953_, 1);
v_isSharedCheck_2058_ = !lean_is_exclusive(v_b_1953_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_1969_ = v_b_1953_;
v_isShared_1970_ = v_isSharedCheck_2058_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_snd_1967_);
lean_inc(v_fst_1966_);
lean_dec(v_b_1953_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_2058_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_ctx_1971_; lean_object* v_determineInsertion_1972_; uint8_t v___y_1974_; uint8_t v___y_1975_; lean_object* v_toCommandContextInfo_2049_; lean_object* v_env_2050_; lean_object* v___x_2051_; uint8_t v___x_2052_; uint8_t v___y_2054_; uint8_t v___x_2057_; 
v_ctx_1971_ = lean_ctor_get(v_a_1944_, 1);
v_determineInsertion_1972_ = lean_ctor_get(v_a_1944_, 2);
v_toCommandContextInfo_2049_ = lean_ctor_get(v_ctx_1971_, 0);
v_env_2050_ = lean_ctor_get(v_toCommandContextInfo_2049_, 0);
v___x_2051_ = lean_unsigned_to_nat(0u);
v___x_2052_ = lean_nat_dec_eq(v___x_1949_, v___x_2051_);
lean_inc(v_decl_1964_);
lean_inc_ref(v_env_2050_);
v___x_2057_ = l_Lean_Environment_contains(v_env_2050_, v_decl_1964_, v___x_1960_);
if (v___x_2057_ == 0)
{
v___y_2054_ = v___x_1960_;
goto v___jp_2053_;
}
else
{
v___y_2054_ = v___x_2052_;
goto v___jp_2053_;
}
v___jp_1973_:
{
if (v___y_1975_ == 0)
{
lean_object* v___x_1976_; 
lean_inc_ref(v_determineInsertion_1972_);
lean_inc(v_decl_1964_);
v___x_1976_ = lean_apply_1(v_determineInsertion_1972_, v_decl_1964_);
if (v___y_1974_ == 0)
{
lean_object* v_fullName_1977_; lean_object* v_edit_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2005_; 
v_fullName_1977_ = lean_ctor_get(v___x_1976_, 0);
v_edit_1978_ = lean_ctor_get(v___x_1976_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1980_ = v___x_1976_;
v_isShared_1981_ = v_isSharedCheck_2005_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_edit_1978_);
lean_inc(v_fullName_1977_);
lean_dec(v___x_1976_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2005_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1992_; 
v___x_1982_ = lean_box(0);
v___x_1983_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__0));
v___x_1984_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fullName_1977_, v___x_1960_);
v___x_1985_ = lean_string_append(v___x_1983_, v___x_1984_);
lean_dec_ref(v___x_1984_);
lean_inc_ref(v_kind_1945_);
v___x_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1986_, 0, v_kind_1945_);
lean_inc_ref(v___x_1946_);
v___x_1987_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_1946_);
v___x_1988_ = lean_unsigned_to_nat(1u);
v___x_1989_ = lean_mk_empty_array_with_capacity(v___x_1988_);
v___x_1990_ = lean_array_push(v___x_1989_, v_edit_1978_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v___x_1990_);
lean_ctor_set(v___x_1980_, 0, v___x_1987_);
v___x_1992_ = v___x_1980_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v___x_1987_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___x_1990_);
v___x_1992_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_1993_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_1992_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
v___x_1995_ = ((lean_object*)(l_Lean_Server_FileWorker_importUnknownIdentifiersProvider));
lean_inc_ref(v_params_1947_);
v___x_1996_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_1947_, v___x_1995_);
v___x_1997_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_1996_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
v___x_1999_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1982_);
lean_ctor_set(v___x_1999_, 1, v___x_1982_);
lean_ctor_set(v___x_1999_, 2, v___x_1985_);
lean_ctor_set(v___x_1999_, 3, v___x_1986_);
lean_ctor_set(v___x_1999_, 4, v___x_1982_);
lean_ctor_set(v___x_1999_, 5, v___x_1982_);
lean_ctor_set(v___x_1999_, 6, v___x_1982_);
lean_ctor_set(v___x_1999_, 7, v___x_1994_);
lean_ctor_set(v___x_1999_, 8, v___x_1982_);
lean_ctor_set(v___x_1999_, 9, v___x_1998_);
v___x_2000_ = lean_array_push(v_fst_1966_, v___x_1999_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_2000_);
v___x_2002_ = v___x_1969_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_2000_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v_snd_1967_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
v_a_1956_ = v___x_2002_;
goto v___jp_1955_;
}
}
}
}
else
{
lean_object* v_fullName_2006_; lean_object* v_edit_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2045_; 
v_fullName_2006_ = lean_ctor_get(v___x_1976_, 0);
v_edit_2007_ = lean_ctor_get(v___x_1976_, 1);
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_1976_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2009_ = v___x_1976_;
v_isShared_2010_ = v_isSharedCheck_2045_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_edit_2007_);
lean_inc(v_fullName_2006_);
lean_dec(v___x_1976_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2045_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v___x_2011_ = lean_box(0);
v___x_2012_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__1));
v___x_2013_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fullName_2006_, v___y_1974_);
v___x_2014_ = lean_string_append(v___x_2012_, v___x_2013_);
lean_dec_ref(v___x_2013_);
v___x_2015_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___closed__2));
v___x_2016_ = lean_string_append(v___x_2014_, v___x_2015_);
lean_inc_n(v_module_1963_, 2);
v___x_2017_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_1963_, v___y_1974_);
v___x_2018_ = lean_string_append(v___x_2016_, v___x_2017_);
lean_dec_ref(v___x_2017_);
lean_inc_ref(v_kind_1945_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_kind_1945_);
lean_inc_ref(v___x_1946_);
v___x_2020_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v___x_1946_);
lean_inc_ref(v_ctx_1971_);
v___x_2021_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_1971_, v_module_1963_);
lean_inc_ref(v___x_1948_);
v___x_2022_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2022_, 0, v___x_1948_);
lean_ctor_set(v___x_2022_, 1, v___x_2021_);
lean_ctor_set(v___x_2022_, 2, v___x_2011_);
lean_ctor_set(v___x_2022_, 3, v___x_2011_);
v___x_2023_ = lean_unsigned_to_nat(2u);
v___x_2024_ = lean_mk_empty_array_with_capacity(v___x_2023_);
v___x_2025_ = lean_array_push(v___x_2024_, v___x_2022_);
v___x_2026_ = lean_array_push(v___x_2025_, v_edit_2007_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___x_2026_);
lean_ctor_set(v___x_2009_, 0, v___x_2020_);
v___x_2028_ = v___x_2009_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v___x_2026_);
v___x_2028_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2029_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_2028_);
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
v___x_2031_ = ((lean_object*)(l_Lean_Server_FileWorker_importUnknownIdentifiersProvider));
lean_inc_ref(v_params_1947_);
v___x_2032_ = l_Lean_Server_FileWorker_mkUnknownIdentifierCodeActionData(v_params_1947_, v___x_2031_);
v___x_2033_ = l_Lean_Server_instToJsonCodeActionResolveData_toJson(v___x_2032_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2011_);
lean_ctor_set(v___x_2035_, 1, v___x_2011_);
lean_ctor_set(v___x_2035_, 2, v___x_2018_);
lean_ctor_set(v___x_2035_, 3, v___x_2019_);
lean_ctor_set(v___x_2035_, 4, v___x_2011_);
lean_ctor_set(v___x_2035_, 5, v___x_2011_);
lean_ctor_set(v___x_2035_, 6, v___x_2011_);
lean_ctor_set(v___x_2035_, 7, v___x_2030_);
lean_ctor_set(v___x_2035_, 8, v___x_2011_);
lean_ctor_set(v___x_2035_, 9, v___x_2034_);
v___x_2036_ = lean_array_push(v_fst_1966_, v___x_2035_);
if (v_isExactMatch_1965_ == 0)
{
lean_object* v___x_2038_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_2036_);
v___x_2038_ = v___x_1969_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v_snd_1967_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
v_a_1956_ = v___x_2038_;
goto v___jp_1955_;
}
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2042_; 
lean_dec(v_snd_1967_);
v___x_2040_ = lean_box(v___x_1960_);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 1, v___x_2040_);
lean_ctor_set(v___x_1969_, 0, v___x_2036_);
v___x_2042_ = v___x_1969_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
v_a_1956_ = v___x_2042_;
goto v___jp_1955_;
}
}
}
}
}
}
else
{
lean_object* v___x_2047_; 
if (v_isShared_1970_ == 0)
{
v___x_2047_ = v___x_1969_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_fst_1966_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v_snd_1967_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
v_a_1956_ = v___x_2047_;
goto v___jp_1955_;
}
}
}
v___jp_2053_:
{
if (v___y_2054_ == 0)
{
v___y_1974_ = v___y_2054_;
v___y_1975_ = v___x_2052_;
goto v___jp_1973_;
}
else
{
lean_object* v___x_2055_; uint8_t v___x_2056_; 
v___x_2055_ = l_Lean_Environment_mainModule(v_env_2050_);
v___x_2056_ = lean_name_eq(v_module_1963_, v___x_2055_);
lean_dec(v___x_2055_);
v___y_1974_ = v___y_2054_;
v___y_1975_ = v___x_2056_;
goto v___jp_1973_;
}
}
}
}
v___jp_1955_:
{
size_t v___x_1957_; size_t v___x_1958_; 
v___x_1957_ = ((size_t)1ULL);
v___x_1958_ = lean_usize_add(v_i_1952_, v___x_1957_);
v_i_1952_ = v___x_1958_;
v_b_1953_ = v_a_1956_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg___boxed(lean_object* v_a_2059_, lean_object* v_kind_2060_, lean_object* v___x_2061_, lean_object* v_params_2062_, lean_object* v___x_2063_, lean_object* v___x_2064_, lean_object* v_as_2065_, lean_object* v_sz_2066_, lean_object* v_i_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_){
_start:
{
size_t v_sz_boxed_2070_; size_t v_i_boxed_2071_; lean_object* v_res_2072_; 
v_sz_boxed_2070_ = lean_unbox_usize(v_sz_2066_);
lean_dec(v_sz_2066_);
v_i_boxed_2071_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_2059_, v_kind_2060_, v___x_2061_, v_params_2062_, v___x_2063_, v___x_2064_, v_as_2065_, v_sz_boxed_2070_, v_i_boxed_2071_, v_b_2068_);
lean_dec_ref(v_as_2065_);
lean_dec(v___x_2064_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(lean_object* v_kind_2073_, lean_object* v___x_2074_, lean_object* v_params_2075_, lean_object* v___x_2076_, lean_object* v___x_2077_, lean_object* v_as_2078_, size_t v_sz_2079_, size_t v_i_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_usize_dec_lt(v_i_2080_, v_sz_2079_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_params_2075_);
lean_dec_ref(v___x_2074_);
lean_dec_ref(v_kind_2073_);
v___x_2085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2085_, 0, v_b_2081_);
return v___x_2085_;
}
else
{
lean_object* v_snd_2086_; lean_object* v_snd_2087_; lean_object* v_fst_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2153_; 
v_snd_2086_ = lean_ctor_get(v_b_2081_, 1);
lean_inc(v_snd_2086_);
v_snd_2087_ = lean_ctor_get(v_snd_2086_, 1);
lean_inc(v_snd_2087_);
v_fst_2088_ = lean_ctor_get(v_b_2081_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v_b_2081_);
if (v_isSharedCheck_2153_ == 0)
{
lean_object* v_unused_2154_; 
v_unused_2154_ = lean_ctor_get(v_b_2081_, 1);
lean_dec(v_unused_2154_);
v___x_2090_ = v_b_2081_;
v_isShared_2091_ = v_isSharedCheck_2153_;
goto v_resetjp_2089_;
}
else
{
lean_inc(v_fst_2088_);
lean_dec(v_b_2081_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2153_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v_fst_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2151_; 
v_fst_2092_ = lean_ctor_get(v_snd_2086_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v_snd_2086_);
if (v_isSharedCheck_2151_ == 0)
{
lean_object* v_unused_2152_; 
v_unused_2152_ = lean_ctor_get(v_snd_2086_, 1);
lean_dec(v_unused_2152_);
v___x_2094_ = v_snd_2086_;
v_isShared_2095_ = v_isSharedCheck_2151_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_fst_2092_);
lean_dec(v_snd_2086_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2151_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_array_2096_; lean_object* v_start_2097_; lean_object* v_stop_2098_; uint8_t v___x_2099_; 
v_array_2096_ = lean_ctor_get(v_snd_2087_, 0);
v_start_2097_ = lean_ctor_get(v_snd_2087_, 1);
v_stop_2098_ = lean_ctor_get(v_snd_2087_, 2);
v___x_2099_ = lean_nat_dec_lt(v_start_2097_, v_stop_2098_);
if (v___x_2099_ == 0)
{
lean_object* v___x_2101_; 
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_params_2075_);
lean_dec_ref(v___x_2074_);
lean_dec_ref(v_kind_2073_);
if (v_isShared_2095_ == 0)
{
v___x_2101_ = v___x_2094_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_fst_2092_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_snd_2087_);
v___x_2101_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v___x_2103_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2101_);
v___x_2103_ = v___x_2090_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_fst_2088_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; 
v___x_2104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
return v___x_2104_;
}
}
}
else
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2147_; 
lean_inc(v_stop_2098_);
lean_inc(v_start_2097_);
lean_inc_ref(v_array_2096_);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_snd_2087_);
if (v_isSharedCheck_2147_ == 0)
{
lean_object* v_unused_2148_; lean_object* v_unused_2149_; lean_object* v_unused_2150_; 
v_unused_2148_ = lean_ctor_get(v_snd_2087_, 2);
lean_dec(v_unused_2148_);
v_unused_2149_ = lean_ctor_get(v_snd_2087_, 1);
lean_dec(v_unused_2149_);
v_unused_2150_ = lean_ctor_get(v_snd_2087_, 0);
lean_dec(v_unused_2150_);
v___x_2108_ = v_snd_2087_;
v_isShared_2109_ = v_isSharedCheck_2147_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v_snd_2087_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2147_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v___x_2113_; 
v_a_2110_ = lean_array_uget_borrowed(v_as_2078_, v_i_2080_);
v___x_2111_ = lean_array_fget_borrowed(v_array_2096_, v_start_2097_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 1, v_fst_2092_);
lean_ctor_set(v___x_2094_, 0, v_fst_2088_);
v___x_2113_ = v___x_2094_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_fst_2088_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_fst_2092_);
v___x_2113_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
size_t v_sz_2114_; size_t v___x_2115_; lean_object* v___x_2116_; 
v_sz_2114_ = lean_array_size(v___x_2111_);
v___x_2115_ = ((size_t)0ULL);
lean_inc_ref(v___x_2076_);
lean_inc_ref(v_params_2075_);
lean_inc_ref(v___x_2074_);
lean_inc_ref(v_kind_2073_);
lean_inc(v_a_2110_);
v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_2110_, v_kind_2073_, v___x_2074_, v_params_2075_, v___x_2076_, v___x_2077_, v___x_2111_, v_sz_2114_, v___x_2115_, v___x_2113_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v_fst_2118_; lean_object* v_snd_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2137_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref(v___x_2116_);
v_fst_2118_ = lean_ctor_get(v_a_2117_, 0);
v_snd_2119_ = lean_ctor_get(v_a_2117_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_a_2117_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2121_ = v_a_2117_;
v_isShared_2122_ = v_isSharedCheck_2137_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_snd_2119_);
lean_inc(v_fst_2118_);
lean_dec(v_a_2117_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2137_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_unsigned_to_nat(1u);
v___x_2124_ = lean_nat_add(v_start_2097_, v___x_2123_);
lean_dec(v_start_2097_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 1, v___x_2124_);
v___x_2126_ = v___x_2108_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_array_2096_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2136_, 2, v_stop_2098_);
v___x_2126_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2128_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v___x_2126_);
lean_ctor_set(v___x_2121_, 0, v_snd_2119_);
v___x_2128_ = v___x_2121_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_snd_2119_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
lean_object* v___x_2130_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 1, v___x_2128_);
lean_ctor_set(v___x_2090_, 0, v_fst_2118_);
v___x_2130_ = v___x_2090_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_fst_2118_);
lean_ctor_set(v_reuseFailAlloc_2134_, 1, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
size_t v___x_2131_; size_t v___x_2132_; 
v___x_2131_ = ((size_t)1ULL);
v___x_2132_ = lean_usize_add(v_i_2080_, v___x_2131_);
v_i_2080_ = v___x_2132_;
v_b_2081_ = v___x_2130_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_del_object(v___x_2108_);
lean_dec(v_stop_2098_);
lean_dec(v_start_2097_);
lean_dec_ref(v_array_2096_);
lean_del_object(v___x_2090_);
lean_dec_ref(v___x_2076_);
lean_dec_ref(v_params_2075_);
lean_dec_ref(v___x_2074_);
lean_dec_ref(v_kind_2073_);
v_a_2138_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2116_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2116_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3___boxed(lean_object* v_kind_2155_, lean_object* v___x_2156_, lean_object* v_params_2157_, lean_object* v___x_2158_, lean_object* v___x_2159_, lean_object* v_as_2160_, lean_object* v_sz_2161_, lean_object* v_i_2162_, lean_object* v_b_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
size_t v_sz_boxed_2166_; size_t v_i_boxed_2167_; lean_object* v_res_2168_; 
v_sz_boxed_2166_ = lean_unbox_usize(v_sz_2161_);
lean_dec(v_sz_2161_);
v_i_boxed_2167_ = lean_unbox_usize(v_i_2162_);
lean_dec(v_i_2162_);
v_res_2168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_2155_, v___x_2156_, v_params_2157_, v___x_2158_, v___x_2159_, v_as_2160_, v_sz_boxed_2166_, v_i_boxed_2167_, v_b_2163_, v___y_2164_);
lean_dec_ref(v___y_2164_);
lean_dec_ref(v_as_2160_);
lean_dec(v___x_2159_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(lean_object* v_id_2177_, lean_object* v_params_2178_, lean_object* v_requestedRange_2179_, lean_object* v_kind_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_doc_2183_; lean_object* v_cancelTk_2184_; lean_object* v_toEditableDocumentCore_2185_; lean_object* v_stop_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2315_; 
v_doc_2183_ = lean_ctor_get(v_a_2181_, 1);
v_cancelTk_2184_ = lean_ctor_get(v_a_2181_, 4);
v_toEditableDocumentCore_2185_ = lean_ctor_get(v_doc_2183_, 0);
v_stop_2186_ = lean_ctor_get(v_requestedRange_2179_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_requestedRange_2179_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v_requestedRange_2179_, 0);
lean_dec(v_unused_2316_);
v___x_2188_ = v_requestedRange_2179_;
v_isShared_2189_ = v_isSharedCheck_2315_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_stop_2186_);
lean_dec(v_requestedRange_2179_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2315_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2190_; 
lean_inc_ref(v_doc_2183_);
v___x_2190_ = l_Lean_Server_FileWorker_computeQueries(v_doc_2183_, v_stop_2186_, v_a_2181_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2306_; 
v_a_2191_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2193_ = v___x_2190_;
v_isShared_2194_ = v_isSharedCheck_2306_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2190_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2306_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2195_ = lean_array_get_size(v_a_2191_);
v___x_2196_ = lean_unsigned_to_nat(0u);
v___x_2197_ = lean_nat_dec_eq(v___x_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; size_t v_sz_2199_; size_t v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
lean_del_object(v___x_2193_);
v___x_2198_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0));
v_sz_2199_ = lean_array_size(v_a_2191_);
v___x_2200_ = ((size_t)0ULL);
lean_inc(v_a_2191_);
v___x_2201_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_2199_, v___x_2200_, v_a_2191_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 1, v___x_2201_);
lean_ctor_set(v___x_2188_, 0, v_id_2177_);
v___x_2203_ = v___x_2188_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_id_2177_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2201_);
v___x_2203_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2300_; 
v___x_2204_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_2198_, v___x_2203_, v_a_2181_);
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2207_ = v___x_2204_;
v_isShared_2208_ = v_isSharedCheck_2300_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2204_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2300_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___f_2209_; lean_object* v___f_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___y_2219_; 
v___f_2209_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__1));
v___f_2210_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__2));
v___x_2211_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2209_, v_a_2205_);
v___x_2212_ = l_Lean_Server_RequestCancellationToken_requestCancellationTask(v_cancelTk_2184_);
v___x_2213_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2210_, v___x_2212_);
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2213_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2211_);
lean_ctor_set(v___x_2216_, 1, v___x_2215_);
v___x_2217_ = l_Lean_Server_ServerTask_waitAny___redArg(v___x_2216_);
if (lean_obj_tag(v___x_2217_) == 0)
{
lean_object* v_val_2238_; 
v_val_2238_ = lean_ctor_get(v___x_2217_, 0);
lean_inc(v_val_2238_);
lean_dec_ref(v___x_2217_);
if (lean_obj_tag(v_val_2238_) == 0)
{
lean_object* v_response_2239_; lean_object* v___y_2241_; lean_object* v_initSnap_2281_; lean_object* v_meta_2282_; lean_object* v_stx_2283_; lean_object* v___x_2284_; 
v_response_2239_ = lean_ctor_get(v_val_2238_, 0);
lean_inc(v_response_2239_);
lean_dec_ref(v_val_2238_);
v_initSnap_2281_ = lean_ctor_get(v_toEditableDocumentCore_2185_, 1);
v_meta_2282_ = lean_ctor_get(v_toEditableDocumentCore_2185_, 0);
v_stx_2283_ = lean_ctor_get(v_initSnap_2281_, 3);
v___x_2284_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2283_, v___x_2197_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v___x_2285_; 
v___x_2285_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5));
v___y_2241_ = v___x_2285_;
goto v___jp_2240_;
}
else
{
lean_object* v_val_2286_; lean_object* v_text_2287_; lean_object* v___x_2288_; lean_object* v_line_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2298_; 
v_val_2286_ = lean_ctor_get(v___x_2284_, 0);
lean_inc(v_val_2286_);
lean_dec_ref(v___x_2284_);
v_text_2287_ = lean_ctor_get(v_meta_2282_, 3);
lean_inc_ref(v_text_2287_);
v___x_2288_ = l_Lean_FileMap_utf8PosToLspPos(v_text_2287_, v_val_2286_);
lean_dec(v_val_2286_);
v_line_2289_ = lean_ctor_get(v___x_2288_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2288_);
if (v_isSharedCheck_2298_ == 0)
{
lean_object* v_unused_2299_; 
v_unused_2299_ = lean_ctor_get(v___x_2288_, 1);
lean_dec(v_unused_2299_);
v___x_2291_ = v___x_2288_;
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_line_2289_);
lean_dec(v___x_2288_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2298_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2293_ = lean_unsigned_to_nat(1u);
v___x_2294_ = lean_nat_add(v_line_2289_, v___x_2293_);
lean_dec(v_line_2289_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v___x_2196_);
lean_ctor_set(v___x_2291_, 0, v___x_2294_);
v___x_2296_ = v___x_2291_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v___x_2196_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
v___y_2241_ = v___x_2296_;
goto v___jp_2240_;
}
}
}
v___jp_2240_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; uint8_t v___x_2245_; 
lean_inc_ref(v___y_2241_);
v___x_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___y_2241_);
lean_ctor_set(v___x_2242_, 1, v___y_2241_);
v___x_2243_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3));
v___x_2244_ = lean_array_get_size(v_response_2239_);
v___x_2245_ = lean_nat_dec_lt(v___x_2196_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v___x_2247_; 
lean_dec_ref(v___x_2242_);
lean_dec(v_response_2239_);
lean_dec(v_a_2191_);
lean_dec_ref(v_kind_2180_);
lean_dec_ref(v_params_2178_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2243_);
v___x_2247_ = v___x_2207_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___x_2243_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
else
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
lean_del_object(v___x_2207_);
v___x_2249_ = l_Array_toSubarray___redArg(v_response_2239_, v___x_2196_, v___x_2244_);
v___x_2250_ = lean_box(v___x_2197_);
v___x_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v___x_2249_);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2243_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
lean_inc_ref(v_params_2178_);
lean_inc_ref(v_doc_2183_);
v___x_2253_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__3(v_kind_2180_, v_doc_2183_, v_params_2178_, v___x_2242_, v___x_2195_, v_a_2191_, v_sz_2199_, v___x_2200_, v___x_2252_, v_a_2181_);
lean_dec(v_a_2191_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2272_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2272_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2272_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_snd_2258_; lean_object* v_fst_2259_; uint8_t v___x_2260_; 
v_snd_2258_ = lean_ctor_get(v_a_2254_, 1);
v_fst_2259_ = lean_ctor_get(v_snd_2258_, 0);
v___x_2260_ = lean_unbox(v_fst_2259_);
if (v___x_2260_ == 0)
{
lean_object* v_fst_2261_; lean_object* v___x_2263_; 
lean_dec_ref(v_params_2178_);
v_fst_2261_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_fst_2261_);
lean_dec(v_a_2254_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v_fst_2261_);
v___x_2263_ = v___x_2256_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_fst_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
else
{
lean_object* v_fst_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2270_; 
v_fst_2265_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_fst_2265_);
lean_dec(v_a_2254_);
v___x_2266_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__4));
v___x_2267_ = l_Lean_Server_FileWorker_importAllUnknownIdentifiersCodeAction(v_params_2178_, v___x_2266_);
v___x_2268_ = lean_array_push(v_fst_2265_, v___x_2267_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2268_);
v___x_2270_ = v___x_2256_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v___x_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
lean_dec_ref(v_params_2178_);
v_a_2273_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2253_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2253_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
}
}
}
}
else
{
lean_dec(v_val_2238_);
lean_del_object(v___x_2207_);
lean_dec(v_a_2191_);
lean_dec_ref(v_kind_2180_);
lean_dec_ref(v_params_2178_);
v___y_2219_ = v_a_2181_;
goto v___jp_2218_;
}
}
else
{
lean_dec(v___x_2217_);
lean_del_object(v___x_2207_);
lean_dec(v_a_2191_);
lean_dec_ref(v_kind_2180_);
lean_dec_ref(v_params_2178_);
v___y_2219_ = v_a_2181_;
goto v___jp_2218_;
}
v___jp_2218_:
{
lean_object* v___x_2220_; 
v___x_2220_ = l_Lean_Server_RequestM_checkCancelled(v___y_2219_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2228_; 
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v___x_2220_, 0);
lean_dec(v_unused_2229_);
v___x_2222_ = v___x_2220_;
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
else
{
lean_dec(v___x_2220_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2228_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2224_; lean_object* v___x_2226_; 
v___x_2224_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3));
if (v_isShared_2223_ == 0)
{
lean_ctor_set(v___x_2222_, 0, v___x_2224_);
v___x_2226_ = v___x_2222_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v___x_2224_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_a_2230_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2220_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2220_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2302_; lean_object* v___x_2304_; 
lean_dec(v_a_2191_);
lean_del_object(v___x_2188_);
lean_dec_ref(v_kind_2180_);
lean_dec_ref(v_params_2178_);
lean_dec(v_id_2177_);
v___x_2302_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__3));
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2302_);
v___x_2304_ = v___x_2193_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2314_; 
lean_del_object(v___x_2188_);
lean_dec_ref(v_kind_2180_);
lean_dec_ref(v_params_2178_);
lean_dec(v_id_2177_);
v_a_2307_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2309_ = v___x_2190_;
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2190_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2314_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2312_; 
if (v_isShared_2310_ == 0)
{
v___x_2312_ = v___x_2309_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_a_2307_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___boxed(lean_object* v_id_2317_, lean_object* v_params_2318_, lean_object* v_requestedRange_2319_, lean_object* v_kind_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction(v_id_2317_, v_params_2318_, v_requestedRange_2319_, v_kind_2320_, v_a_2321_);
lean_dec_ref(v_a_2321_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(lean_object* v_a_2324_, lean_object* v_kind_2325_, lean_object* v___x_2326_, lean_object* v_params_2327_, lean_object* v___x_2328_, lean_object* v___x_2329_, lean_object* v_as_2330_, size_t v_sz_2331_, size_t v_i_2332_, lean_object* v_b_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___redArg(v_a_2324_, v_kind_2325_, v___x_2326_, v_params_2327_, v___x_2328_, v___x_2329_, v_as_2330_, v_sz_2331_, v_i_2332_, v_b_2333_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2___boxed(lean_object* v_a_2337_, lean_object* v_kind_2338_, lean_object* v___x_2339_, lean_object* v_params_2340_, lean_object* v___x_2341_, lean_object* v___x_2342_, lean_object* v_as_2343_, lean_object* v_sz_2344_, lean_object* v_i_2345_, lean_object* v_b_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
size_t v_sz_boxed_2349_; size_t v_i_boxed_2350_; lean_object* v_res_2351_; 
v_sz_boxed_2349_ = lean_unbox_usize(v_sz_2344_);
lean_dec(v_sz_2344_);
v_i_boxed_2350_ = lean_unbox_usize(v_i_2345_);
lean_dec(v_i_2345_);
v_res_2351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__2(v_a_2337_, v_kind_2338_, v___x_2339_, v_params_2340_, v___x_2341_, v___x_2342_, v_as_2343_, v_sz_boxed_2349_, v_i_boxed_2350_, v_b_2346_, v___y_2347_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_as_2343_);
lean_dec(v___x_2342_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(lean_object* v_a_2355_, lean_object* v_as_2356_, size_t v_sz_2357_, size_t v_i_2358_, lean_object* v_b_2359_){
_start:
{
lean_object* v_a_2361_; uint8_t v___x_2365_; 
v___x_2365_ = lean_usize_dec_lt(v_i_2358_, v_sz_2357_);
if (v___x_2365_ == 0)
{
lean_dec_ref(v_a_2355_);
lean_inc_ref(v_b_2359_);
return v_b_2359_;
}
else
{
lean_object* v_a_2366_; lean_object* v_decl_2367_; uint8_t v_isExactMatch_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; 
v_a_2366_ = lean_array_uget_borrowed(v_as_2356_, v_i_2358_);
v_decl_2367_ = lean_ctor_get(v_a_2366_, 1);
v_isExactMatch_2368_ = lean_ctor_get_uint8(v_a_2366_, sizeof(void*)*2);
v___x_2369_ = lean_box(0);
v___x_2370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0));
if (v_isExactMatch_2368_ == 0)
{
v_a_2361_ = v___x_2370_;
goto v___jp_2360_;
}
else
{
lean_object* v_ctx_2371_; lean_object* v_toCommandContextInfo_2372_; lean_object* v_env_2373_; uint8_t v___x_2374_; 
v_ctx_2371_ = lean_ctor_get(v_a_2355_, 1);
v_toCommandContextInfo_2372_ = lean_ctor_get(v_ctx_2371_, 0);
v_env_2373_ = lean_ctor_get(v_toCommandContextInfo_2372_, 0);
lean_inc(v_decl_2367_);
lean_inc_ref(v_env_2373_);
v___x_2374_ = l_Lean_Environment_contains(v_env_2373_, v_decl_2367_, v_isExactMatch_2368_);
if (v___x_2374_ == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; 
lean_dec_ref(v_a_2355_);
lean_inc(v_a_2366_);
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v_a_2366_);
v___x_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v___x_2369_);
return v___x_2377_;
}
else
{
v_a_2361_ = v___x_2370_;
goto v___jp_2360_;
}
}
}
v___jp_2360_:
{
size_t v___x_2362_; size_t v___x_2363_; 
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2358_, v___x_2362_);
v_i_2358_ = v___x_2363_;
v_b_2359_ = v_a_2361_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___boxed(lean_object* v_a_2378_, lean_object* v_as_2379_, lean_object* v_sz_2380_, lean_object* v_i_2381_, lean_object* v_b_2382_){
_start:
{
size_t v_sz_boxed_2383_; size_t v_i_boxed_2384_; lean_object* v_res_2385_; 
v_sz_boxed_2383_ = lean_unbox_usize(v_sz_2380_);
lean_dec(v_sz_2380_);
v_i_boxed_2384_ = lean_unbox_usize(v_i_2381_);
lean_dec(v_i_2381_);
v_res_2385_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_2378_, v_as_2379_, v_sz_boxed_2383_, v_i_boxed_2384_, v_b_2382_);
lean_dec_ref(v_b_2382_);
lean_dec_ref(v_as_2379_);
return v_res_2385_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(lean_object* v_a_2386_, lean_object* v_x_2387_){
_start:
{
if (lean_obj_tag(v_x_2387_) == 0)
{
uint8_t v___x_2388_; 
v___x_2388_ = 0;
return v___x_2388_;
}
else
{
lean_object* v_key_2389_; lean_object* v_tail_2390_; uint8_t v___x_2391_; 
v_key_2389_ = lean_ctor_get(v_x_2387_, 0);
v_tail_2390_ = lean_ctor_get(v_x_2387_, 2);
v___x_2391_ = lean_name_eq(v_key_2389_, v_a_2386_);
if (v___x_2391_ == 0)
{
v_x_2387_ = v_tail_2390_;
goto _start;
}
else
{
return v___x_2391_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg___boxed(lean_object* v_a_2393_, lean_object* v_x_2394_){
_start:
{
uint8_t v_res_2395_; lean_object* v_r_2396_; 
v_res_2395_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2393_, v_x_2394_);
lean_dec(v_x_2394_);
lean_dec(v_a_2393_);
v_r_2396_ = lean_box(v_res_2395_);
return v_r_2396_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2397_; uint64_t v___x_2398_; 
v___x_2397_ = lean_unsigned_to_nat(1723u);
v___x_2398_ = lean_uint64_of_nat(v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(lean_object* v_m_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v_buckets_2401_; lean_object* v___x_2402_; uint64_t v___y_2404_; 
v_buckets_2401_ = lean_ctor_get(v_m_2399_, 1);
v___x_2402_ = lean_array_get_size(v_buckets_2401_);
if (lean_obj_tag(v_a_2400_) == 0)
{
uint64_t v___x_2418_; 
v___x_2418_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
v___y_2404_ = v___x_2418_;
goto v___jp_2403_;
}
else
{
uint64_t v_hash_2419_; 
v_hash_2419_ = lean_ctor_get_uint64(v_a_2400_, sizeof(void*)*2);
v___y_2404_ = v_hash_2419_;
goto v___jp_2403_;
}
v___jp_2403_:
{
uint64_t v___x_2405_; uint64_t v___x_2406_; uint64_t v_fold_2407_; uint64_t v___x_2408_; uint64_t v___x_2409_; uint64_t v___x_2410_; size_t v___x_2411_; size_t v___x_2412_; size_t v___x_2413_; size_t v___x_2414_; size_t v___x_2415_; lean_object* v___x_2416_; uint8_t v___x_2417_; 
v___x_2405_ = 32ULL;
v___x_2406_ = lean_uint64_shift_right(v___y_2404_, v___x_2405_);
v_fold_2407_ = lean_uint64_xor(v___y_2404_, v___x_2406_);
v___x_2408_ = 16ULL;
v___x_2409_ = lean_uint64_shift_right(v_fold_2407_, v___x_2408_);
v___x_2410_ = lean_uint64_xor(v_fold_2407_, v___x_2409_);
v___x_2411_ = lean_uint64_to_usize(v___x_2410_);
v___x_2412_ = lean_usize_of_nat(v___x_2402_);
v___x_2413_ = ((size_t)1ULL);
v___x_2414_ = lean_usize_sub(v___x_2412_, v___x_2413_);
v___x_2415_ = lean_usize_land(v___x_2411_, v___x_2414_);
v___x_2416_ = lean_array_uget_borrowed(v_buckets_2401_, v___x_2415_);
v___x_2417_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2400_, v___x_2416_);
return v___x_2417_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___boxed(lean_object* v_m_2420_, lean_object* v_a_2421_){
_start:
{
uint8_t v_res_2422_; lean_object* v_r_2423_; 
v_res_2422_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_2420_, v_a_2421_);
lean_dec(v_a_2421_);
lean_dec_ref(v_m_2420_);
v_r_2423_ = lean_box(v_res_2422_);
return v_r_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(lean_object* v_x_2424_, lean_object* v_x_2425_){
_start:
{
if (lean_obj_tag(v_x_2425_) == 0)
{
return v_x_2424_;
}
else
{
lean_object* v_key_2426_; lean_object* v_value_2427_; lean_object* v_tail_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2454_; 
v_key_2426_ = lean_ctor_get(v_x_2425_, 0);
v_value_2427_ = lean_ctor_get(v_x_2425_, 1);
v_tail_2428_ = lean_ctor_get(v_x_2425_, 2);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_x_2425_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2430_ = v_x_2425_;
v_isShared_2431_ = v_isSharedCheck_2454_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_tail_2428_);
lean_inc(v_value_2427_);
lean_inc(v_key_2426_);
lean_dec(v_x_2425_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2454_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; uint64_t v___y_2434_; 
v___x_2432_ = lean_array_get_size(v_x_2424_);
if (lean_obj_tag(v_key_2426_) == 0)
{
uint64_t v___x_2452_; 
v___x_2452_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
v___y_2434_ = v___x_2452_;
goto v___jp_2433_;
}
else
{
uint64_t v_hash_2453_; 
v_hash_2453_ = lean_ctor_get_uint64(v_key_2426_, sizeof(void*)*2);
v___y_2434_ = v_hash_2453_;
goto v___jp_2433_;
}
v___jp_2433_:
{
uint64_t v___x_2435_; uint64_t v___x_2436_; uint64_t v_fold_2437_; uint64_t v___x_2438_; uint64_t v___x_2439_; uint64_t v___x_2440_; size_t v___x_2441_; size_t v___x_2442_; size_t v___x_2443_; size_t v___x_2444_; size_t v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2448_; 
v___x_2435_ = 32ULL;
v___x_2436_ = lean_uint64_shift_right(v___y_2434_, v___x_2435_);
v_fold_2437_ = lean_uint64_xor(v___y_2434_, v___x_2436_);
v___x_2438_ = 16ULL;
v___x_2439_ = lean_uint64_shift_right(v_fold_2437_, v___x_2438_);
v___x_2440_ = lean_uint64_xor(v_fold_2437_, v___x_2439_);
v___x_2441_ = lean_uint64_to_usize(v___x_2440_);
v___x_2442_ = lean_usize_of_nat(v___x_2432_);
v___x_2443_ = ((size_t)1ULL);
v___x_2444_ = lean_usize_sub(v___x_2442_, v___x_2443_);
v___x_2445_ = lean_usize_land(v___x_2441_, v___x_2444_);
v___x_2446_ = lean_array_uget_borrowed(v_x_2424_, v___x_2445_);
lean_inc(v___x_2446_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 2, v___x_2446_);
v___x_2448_ = v___x_2430_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_key_2426_);
lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_value_2427_);
lean_ctor_set(v_reuseFailAlloc_2451_, 2, v___x_2446_);
v___x_2448_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_array_uset(v_x_2424_, v___x_2445_, v___x_2448_);
v_x_2424_ = v___x_2449_;
v_x_2425_ = v_tail_2428_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(lean_object* v_i_2455_, lean_object* v_source_2456_, lean_object* v_target_2457_){
_start:
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = lean_array_get_size(v_source_2456_);
v___x_2459_ = lean_nat_dec_lt(v_i_2455_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_dec_ref(v_source_2456_);
lean_dec(v_i_2455_);
return v_target_2457_;
}
else
{
lean_object* v_es_2460_; lean_object* v___x_2461_; lean_object* v_source_2462_; lean_object* v_target_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_es_2460_ = lean_array_fget(v_source_2456_, v_i_2455_);
v___x_2461_ = lean_box(0);
v_source_2462_ = lean_array_fset(v_source_2456_, v_i_2455_, v___x_2461_);
v_target_2463_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_target_2457_, v_es_2460_);
v___x_2464_ = lean_unsigned_to_nat(1u);
v___x_2465_ = lean_nat_add(v_i_2455_, v___x_2464_);
lean_dec(v_i_2455_);
v_i_2455_ = v___x_2465_;
v_source_2456_ = v_source_2462_;
v_target_2457_ = v_target_2463_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(lean_object* v_data_2467_){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v_nbuckets_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2468_ = lean_array_get_size(v_data_2467_);
v___x_2469_ = lean_unsigned_to_nat(2u);
v_nbuckets_2470_ = lean_nat_mul(v___x_2468_, v___x_2469_);
v___x_2471_ = lean_unsigned_to_nat(0u);
v___x_2472_ = lean_box(0);
v___x_2473_ = lean_mk_array(v_nbuckets_2470_, v___x_2472_);
v___x_2474_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v___x_2471_, v_data_2467_, v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(lean_object* v_m_2475_, lean_object* v_a_2476_, lean_object* v_b_2477_){
_start:
{
lean_object* v_size_2478_; lean_object* v_buckets_2479_; lean_object* v___x_2480_; uint64_t v___y_2482_; 
v_size_2478_ = lean_ctor_get(v_m_2475_, 0);
v_buckets_2479_ = lean_ctor_get(v_m_2475_, 1);
v___x_2480_ = lean_array_get_size(v_buckets_2479_);
if (lean_obj_tag(v_a_2476_) == 0)
{
uint64_t v___x_2519_; 
v___x_2519_ = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg___closed__0);
v___y_2482_ = v___x_2519_;
goto v___jp_2481_;
}
else
{
uint64_t v_hash_2520_; 
v_hash_2520_ = lean_ctor_get_uint64(v_a_2476_, sizeof(void*)*2);
v___y_2482_ = v_hash_2520_;
goto v___jp_2481_;
}
v___jp_2481_:
{
uint64_t v___x_2483_; uint64_t v___x_2484_; uint64_t v_fold_2485_; uint64_t v___x_2486_; uint64_t v___x_2487_; uint64_t v___x_2488_; size_t v___x_2489_; size_t v___x_2490_; size_t v___x_2491_; size_t v___x_2492_; size_t v___x_2493_; lean_object* v_bkt_2494_; uint8_t v___x_2495_; 
v___x_2483_ = 32ULL;
v___x_2484_ = lean_uint64_shift_right(v___y_2482_, v___x_2483_);
v_fold_2485_ = lean_uint64_xor(v___y_2482_, v___x_2484_);
v___x_2486_ = 16ULL;
v___x_2487_ = lean_uint64_shift_right(v_fold_2485_, v___x_2486_);
v___x_2488_ = lean_uint64_xor(v_fold_2485_, v___x_2487_);
v___x_2489_ = lean_uint64_to_usize(v___x_2488_);
v___x_2490_ = lean_usize_of_nat(v___x_2480_);
v___x_2491_ = ((size_t)1ULL);
v___x_2492_ = lean_usize_sub(v___x_2490_, v___x_2491_);
v___x_2493_ = lean_usize_land(v___x_2489_, v___x_2492_);
v_bkt_2494_ = lean_array_uget_borrowed(v_buckets_2479_, v___x_2493_);
v___x_2495_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2476_, v_bkt_2494_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2516_; 
lean_inc_ref(v_buckets_2479_);
lean_inc(v_size_2478_);
v_isSharedCheck_2516_ = !lean_is_exclusive(v_m_2475_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; lean_object* v_unused_2518_; 
v_unused_2517_ = lean_ctor_get(v_m_2475_, 1);
lean_dec(v_unused_2517_);
v_unused_2518_ = lean_ctor_get(v_m_2475_, 0);
lean_dec(v_unused_2518_);
v___x_2497_ = v_m_2475_;
v_isShared_2498_ = v_isSharedCheck_2516_;
goto v_resetjp_2496_;
}
else
{
lean_dec(v_m_2475_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2516_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v_size_x27_2500_; lean_object* v___x_2501_; lean_object* v_buckets_x27_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; 
v___x_2499_ = lean_unsigned_to_nat(1u);
v_size_x27_2500_ = lean_nat_add(v_size_2478_, v___x_2499_);
lean_dec(v_size_2478_);
lean_inc(v_bkt_2494_);
v___x_2501_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2501_, 0, v_a_2476_);
lean_ctor_set(v___x_2501_, 1, v_b_2477_);
lean_ctor_set(v___x_2501_, 2, v_bkt_2494_);
v_buckets_x27_2502_ = lean_array_uset(v_buckets_2479_, v___x_2493_, v___x_2501_);
v___x_2503_ = lean_unsigned_to_nat(4u);
v___x_2504_ = lean_nat_mul(v_size_x27_2500_, v___x_2503_);
v___x_2505_ = lean_unsigned_to_nat(3u);
v___x_2506_ = lean_nat_div(v___x_2504_, v___x_2505_);
lean_dec(v___x_2504_);
v___x_2507_ = lean_array_get_size(v_buckets_x27_2502_);
v___x_2508_ = lean_nat_dec_le(v___x_2506_, v___x_2507_);
lean_dec(v___x_2506_);
if (v___x_2508_ == 0)
{
lean_object* v_val_2509_; lean_object* v___x_2511_; 
v_val_2509_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_buckets_x27_2502_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 1, v_val_2509_);
lean_ctor_set(v___x_2497_, 0, v_size_x27_2500_);
v___x_2511_ = v___x_2497_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_size_x27_2500_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v_val_2509_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
else
{
lean_object* v___x_2514_; 
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 1, v_buckets_x27_2502_);
lean_ctor_set(v___x_2497_, 0, v_size_x27_2500_);
v___x_2514_ = v___x_2497_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_size_x27_2500_);
lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_buckets_x27_2502_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
}
else
{
lean_dec(v_b_2477_);
lean_dec(v_a_2476_);
return v_m_2475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(lean_object* v___x_2521_, lean_object* v_as_2522_, size_t v_sz_2523_, size_t v_i_2524_, lean_object* v_b_2525_){
_start:
{
lean_object* v_a_2528_; uint8_t v___x_2532_; 
v___x_2532_ = lean_usize_dec_lt(v_i_2524_, v_sz_2523_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; 
lean_dec_ref(v___x_2521_);
v___x_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2533_, 0, v_b_2525_);
return v___x_2533_;
}
else
{
lean_object* v_snd_2534_; lean_object* v_snd_2535_; lean_object* v_fst_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2626_; 
v_snd_2534_ = lean_ctor_get(v_b_2525_, 1);
lean_inc(v_snd_2534_);
v_snd_2535_ = lean_ctor_get(v_snd_2534_, 1);
lean_inc(v_snd_2535_);
v_fst_2536_ = lean_ctor_get(v_b_2525_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v_b_2525_);
if (v_isSharedCheck_2626_ == 0)
{
lean_object* v_unused_2627_; 
v_unused_2627_ = lean_ctor_get(v_b_2525_, 1);
lean_dec(v_unused_2627_);
v___x_2538_ = v_b_2525_;
v_isShared_2539_ = v_isSharedCheck_2626_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_fst_2536_);
lean_dec(v_b_2525_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2626_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v_fst_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2624_; 
v_fst_2540_ = lean_ctor_get(v_snd_2534_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v_snd_2534_);
if (v_isSharedCheck_2624_ == 0)
{
lean_object* v_unused_2625_; 
v_unused_2625_ = lean_ctor_get(v_snd_2534_, 1);
lean_dec(v_unused_2625_);
v___x_2542_ = v_snd_2534_;
v_isShared_2543_ = v_isSharedCheck_2624_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_fst_2540_);
lean_dec(v_snd_2534_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2624_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v_array_2544_; lean_object* v_start_2545_; lean_object* v_stop_2546_; uint8_t v___x_2547_; 
v_array_2544_ = lean_ctor_get(v_snd_2535_, 0);
v_start_2545_ = lean_ctor_get(v_snd_2535_, 1);
v_stop_2546_ = lean_ctor_get(v_snd_2535_, 2);
v___x_2547_ = lean_nat_dec_lt(v_start_2545_, v_stop_2546_);
if (v___x_2547_ == 0)
{
lean_object* v___x_2549_; 
lean_dec_ref(v___x_2521_);
if (v_isShared_2543_ == 0)
{
v___x_2549_ = v___x_2542_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_fst_2540_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_snd_2535_);
v___x_2549_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2551_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 1, v___x_2549_);
v___x_2551_ = v___x_2538_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_fst_2536_);
lean_ctor_set(v_reuseFailAlloc_2553_, 1, v___x_2549_);
v___x_2551_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
lean_object* v___x_2552_; 
v___x_2552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2552_, 0, v___x_2551_);
return v___x_2552_;
}
}
}
else
{
lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2620_; 
lean_inc(v_stop_2546_);
lean_inc(v_start_2545_);
lean_inc_ref(v_array_2544_);
v_isSharedCheck_2620_ = !lean_is_exclusive(v_snd_2535_);
if (v_isSharedCheck_2620_ == 0)
{
lean_object* v_unused_2621_; lean_object* v_unused_2622_; lean_object* v_unused_2623_; 
v_unused_2621_ = lean_ctor_get(v_snd_2535_, 2);
lean_dec(v_unused_2621_);
v_unused_2622_ = lean_ctor_get(v_snd_2535_, 1);
lean_dec(v_unused_2622_);
v_unused_2623_ = lean_ctor_get(v_snd_2535_, 0);
lean_dec(v_unused_2623_);
v___x_2556_ = v_snd_2535_;
v_isShared_2557_ = v_isSharedCheck_2620_;
goto v_resetjp_2555_;
}
else
{
lean_dec(v_snd_2535_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2620_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v_a_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; size_t v_sz_2563_; size_t v___x_2564_; lean_object* v___x_2565_; lean_object* v_fst_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2618_; 
v_a_2558_ = lean_array_uget_borrowed(v_as_2522_, v_i_2524_);
v___x_2559_ = lean_array_fget_borrowed(v_array_2544_, v_start_2545_);
v___x_2560_ = lean_box(0);
v___x_2561_ = lean_box(0);
v___x_2562_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0___closed__0));
v_sz_2563_ = lean_array_size(v___x_2559_);
v___x_2564_ = ((size_t)0ULL);
lean_inc(v_a_2558_);
v___x_2565_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__0(v_a_2558_, v___x_2559_, v_sz_2563_, v___x_2564_, v___x_2562_);
v_fst_2566_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2618_ == 0)
{
lean_object* v_unused_2619_; 
v_unused_2619_ = lean_ctor_get(v___x_2565_, 1);
lean_dec(v_unused_2619_);
v___x_2568_ = v___x_2565_;
v_isShared_2569_ = v_isSharedCheck_2618_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_fst_2566_);
lean_dec(v___x_2565_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2618_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2570_ = lean_unsigned_to_nat(1u);
v___x_2571_ = lean_nat_add(v_start_2545_, v___x_2570_);
lean_dec(v_start_2545_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 1, v___x_2571_);
v___x_2573_ = v___x_2556_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_array_2544_);
lean_ctor_set(v_reuseFailAlloc_2617_, 1, v___x_2571_);
lean_ctor_set(v_reuseFailAlloc_2617_, 2, v_stop_2546_);
v___x_2573_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
if (lean_obj_tag(v_fst_2566_) == 0)
{
lean_del_object(v___x_2538_);
goto v___jp_2574_;
}
else
{
lean_object* v_val_2581_; 
v_val_2581_ = lean_ctor_get(v_fst_2566_, 0);
lean_inc(v_val_2581_);
lean_dec_ref(v_fst_2566_);
if (lean_obj_tag(v_val_2581_) == 1)
{
lean_object* v_val_2582_; lean_object* v_ctx_2583_; lean_object* v_toCommandContextInfo_2584_; lean_object* v_module_2585_; lean_object* v_decl_2586_; lean_object* v_determineInsertion_2587_; lean_object* v_env_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; 
lean_del_object(v___x_2568_);
lean_del_object(v___x_2542_);
v_val_2582_ = lean_ctor_get(v_val_2581_, 0);
lean_inc(v_val_2582_);
lean_dec_ref(v_val_2581_);
v_ctx_2583_ = lean_ctor_get(v_a_2558_, 1);
v_toCommandContextInfo_2584_ = lean_ctor_get(v_ctx_2583_, 0);
v_module_2585_ = lean_ctor_get(v_val_2582_, 0);
lean_inc(v_module_2585_);
v_decl_2586_ = lean_ctor_get(v_val_2582_, 1);
lean_inc(v_decl_2586_);
lean_dec(v_val_2582_);
v_determineInsertion_2587_ = lean_ctor_get(v_a_2558_, 2);
v_env_2588_ = lean_ctor_get(v_toCommandContextInfo_2584_, 0);
v___x_2589_ = l_Lean_Environment_mainModule(v_env_2588_);
v___x_2590_ = lean_name_eq(v_module_2585_, v___x_2589_);
lean_dec(v___x_2589_);
if (v___x_2590_ == 0)
{
lean_object* v___x_2591_; lean_object* v_edits_2593_; uint8_t v___x_2612_; 
lean_inc_ref(v_determineInsertion_2587_);
v___x_2591_ = lean_apply_1(v_determineInsertion_2587_, v_decl_2586_);
v___x_2612_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_fst_2540_, v_module_2585_);
if (v___x_2612_ == 0)
{
goto v___jp_2608_;
}
else
{
if (v___x_2590_ == 0)
{
v_edits_2593_ = v_fst_2536_;
goto v___jp_2592_;
}
else
{
goto v___jp_2608_;
}
}
v___jp_2592_:
{
lean_object* v_edit_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2606_; 
v_edit_2594_ = lean_ctor_get(v___x_2591_, 1);
v_isSharedCheck_2606_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2606_ == 0)
{
lean_object* v_unused_2607_; 
v_unused_2607_ = lean_ctor_get(v___x_2591_, 0);
lean_dec(v_unused_2607_);
v___x_2596_ = v___x_2591_;
v_isShared_2597_ = v_isSharedCheck_2606_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_edit_2594_);
lean_dec(v___x_2591_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2606_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v___x_2598_ = lean_array_push(v_edits_2593_, v_edit_2594_);
v___x_2599_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_fst_2540_, v_module_2585_, v___x_2561_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 1, v___x_2573_);
lean_ctor_set(v___x_2538_, 0, v___x_2599_);
v___x_2601_ = v___x_2538_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2605_; 
v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2605_, 1, v___x_2573_);
v___x_2601_ = v_reuseFailAlloc_2605_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2603_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 1, v___x_2601_);
lean_ctor_set(v___x_2596_, 0, v___x_2598_);
v___x_2603_ = v___x_2596_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2604_, 1, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
v_a_2528_ = v___x_2603_;
goto v___jp_2527_;
}
}
}
}
v___jp_2608_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_inc(v_module_2585_);
lean_inc_ref(v_ctx_2583_);
v___x_2609_ = l___private_Lean_Server_CodeActions_UnknownIdentifier_0__Lean_Server_FileWorker_mkImportText(v_ctx_2583_, v_module_2585_);
lean_inc_ref(v___x_2521_);
v___x_2610_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2521_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
lean_ctor_set(v___x_2610_, 2, v___x_2560_);
lean_ctor_set(v___x_2610_, 3, v___x_2560_);
v___x_2611_ = lean_array_push(v_fst_2536_, v___x_2610_);
v_edits_2593_ = v___x_2611_;
goto v___jp_2592_;
}
}
else
{
lean_object* v___x_2614_; 
lean_dec(v_decl_2586_);
lean_dec(v_module_2585_);
if (v_isShared_2539_ == 0)
{
lean_ctor_set(v___x_2538_, 1, v___x_2573_);
lean_ctor_set(v___x_2538_, 0, v_fst_2540_);
v___x_2614_ = v___x_2538_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_fst_2540_);
lean_ctor_set(v_reuseFailAlloc_2616_, 1, v___x_2573_);
v___x_2614_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v_fst_2536_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v_a_2528_ = v___x_2615_;
goto v___jp_2527_;
}
}
}
else
{
lean_dec(v_val_2581_);
lean_del_object(v___x_2538_);
goto v___jp_2574_;
}
}
v___jp_2574_:
{
lean_object* v___x_2576_; 
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 1, v___x_2573_);
lean_ctor_set(v___x_2568_, 0, v_fst_2540_);
v___x_2576_ = v___x_2568_;
goto v_reusejp_2575_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_fst_2540_);
lean_ctor_set(v_reuseFailAlloc_2580_, 1, v___x_2573_);
v___x_2576_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2575_;
}
v_reusejp_2575_:
{
lean_object* v___x_2578_; 
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 1, v___x_2576_);
lean_ctor_set(v___x_2542_, 0, v_fst_2536_);
v___x_2578_ = v___x_2542_;
goto v_reusejp_2577_;
}
else
{
lean_object* v_reuseFailAlloc_2579_; 
v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2579_, 0, v_fst_2536_);
lean_ctor_set(v_reuseFailAlloc_2579_, 1, v___x_2576_);
v___x_2578_ = v_reuseFailAlloc_2579_;
goto v_reusejp_2577_;
}
v_reusejp_2577_:
{
v_a_2528_ = v___x_2578_;
goto v___jp_2527_;
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
v___jp_2527_:
{
size_t v___x_2529_; size_t v___x_2530_; 
v___x_2529_ = ((size_t)1ULL);
v___x_2530_ = lean_usize_add(v_i_2524_, v___x_2529_);
v_i_2524_ = v___x_2530_;
v_b_2525_ = v_a_2528_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg___boxed(lean_object* v___x_2628_, lean_object* v_as_2629_, lean_object* v_sz_2630_, lean_object* v_i_2631_, lean_object* v_b_2632_, lean_object* v___y_2633_){
_start:
{
size_t v_sz_boxed_2634_; size_t v_i_boxed_2635_; lean_object* v_res_2636_; 
v_sz_boxed_2634_ = lean_unbox_usize(v_sz_2630_);
lean_dec(v_sz_2630_);
v_i_boxed_2635_ = lean_unbox_usize(v_i_2631_);
lean_dec(v_i_2631_);
v_res_2636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_2628_, v_as_2629_, v_sz_boxed_2634_, v_i_boxed_2635_, v_b_2632_);
lean_dec_ref(v_as_2629_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(lean_object* v___x_2637_, lean_object* v_as_2638_, size_t v_i_2639_, size_t v_stop_2640_, lean_object* v_b_2641_, lean_object* v___y_2642_){
_start:
{
lean_object* v_a_2645_; uint8_t v___x_2649_; 
v___x_2649_ = lean_usize_dec_eq(v_i_2639_, v_stop_2640_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v_stop_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_array_uget_borrowed(v_as_2638_, v_i_2639_);
v_stop_2651_ = lean_ctor_get(v___x_2650_, 1);
lean_inc(v_stop_2651_);
lean_inc_ref(v___x_2637_);
v___x_2652_ = l_Lean_Server_FileWorker_computeQueries(v___x_2637_, v_stop_2651_, v___y_2642_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2654_; 
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v___x_2654_ = l_Array_append___redArg(v_b_2641_, v_a_2653_);
lean_dec(v_a_2653_);
v_a_2645_ = v___x_2654_;
goto v___jp_2644_;
}
else
{
lean_dec_ref(v_b_2641_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2655_; 
v_a_2655_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2655_);
lean_dec_ref(v___x_2652_);
v_a_2645_ = v_a_2655_;
goto v___jp_2644_;
}
else
{
lean_dec_ref(v___x_2637_);
return v___x_2652_;
}
}
}
else
{
lean_object* v___x_2656_; 
lean_dec_ref(v___x_2637_);
v___x_2656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_b_2641_);
return v___x_2656_;
}
v___jp_2644_:
{
size_t v___x_2646_; size_t v___x_2647_; 
v___x_2646_ = ((size_t)1ULL);
v___x_2647_ = lean_usize_add(v_i_2639_, v___x_2646_);
v_i_2639_ = v___x_2647_;
v_b_2641_ = v_a_2645_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4___boxed(lean_object* v___x_2657_, lean_object* v_as_2658_, lean_object* v_i_2659_, lean_object* v_stop_2660_, lean_object* v_b_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_){
_start:
{
size_t v_i_boxed_2664_; size_t v_stop_boxed_2665_; lean_object* v_res_2666_; 
v_i_boxed_2664_ = lean_unbox_usize(v_i_2659_);
lean_dec(v_i_2659_);
v_stop_boxed_2665_ = lean_unbox_usize(v_stop_2660_);
lean_dec(v_stop_2660_);
v_res_2666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v___x_2657_, v_as_2658_, v_i_boxed_2664_, v_stop_boxed_2665_, v_b_2661_, v___y_2662_);
lean_dec_ref(v___y_2662_);
lean_dec_ref(v_as_2658_);
return v_res_2666_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0(void){
_start:
{
lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
v___x_2667_ = lean_box(0);
v___x_2668_ = lean_unsigned_to_nat(16u);
v___x_2669_ = lean_mk_array(v___x_2668_, v___x_2667_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(lean_object* v_id_2672_, lean_object* v_action_2673_, lean_object* v_unknownIdentifierRanges_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v_doc_2677_; size_t v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; size_t v___y_2682_; lean_object* v___y_2683_; lean_object* v___y_2684_; lean_object* v_toEditableDocumentCore_2740_; lean_object* v_meta_2741_; lean_object* v_initSnap_2742_; lean_object* v_text_2743_; lean_object* v_a_2745_; lean_object* v___y_2785_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; 
v_doc_2677_ = lean_ctor_get(v_a_2675_, 1);
v_toEditableDocumentCore_2740_ = lean_ctor_get(v_doc_2677_, 0);
v_meta_2741_ = lean_ctor_get(v_toEditableDocumentCore_2740_, 0);
v_initSnap_2742_ = lean_ctor_get(v_toEditableDocumentCore_2740_, 1);
v_text_2743_ = lean_ctor_get(v_meta_2741_, 3);
v___x_2795_ = lean_unsigned_to_nat(0u);
v___x_2796_ = ((lean_object*)(l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__1));
v___x_2797_ = lean_array_get_size(v_unknownIdentifierRanges_2674_);
v___x_2798_ = lean_nat_dec_lt(v___x_2795_, v___x_2797_);
if (v___x_2798_ == 0)
{
v_a_2745_ = v___x_2796_;
goto v___jp_2744_;
}
else
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_nat_dec_le(v___x_2797_, v___x_2797_);
if (v___x_2799_ == 0)
{
if (v___x_2798_ == 0)
{
v_a_2745_ = v___x_2796_;
goto v___jp_2744_;
}
else
{
size_t v___x_2800_; size_t v___x_2801_; lean_object* v___x_2802_; 
v___x_2800_ = ((size_t)0ULL);
v___x_2801_ = lean_usize_of_nat(v___x_2797_);
lean_inc_ref(v_doc_2677_);
v___x_2802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_2677_, v_unknownIdentifierRanges_2674_, v___x_2800_, v___x_2801_, v___x_2796_, v_a_2675_);
v___y_2785_ = v___x_2802_;
goto v___jp_2784_;
}
}
else
{
size_t v___x_2803_; size_t v___x_2804_; lean_object* v___x_2805_; 
v___x_2803_ = ((size_t)0ULL);
v___x_2804_ = lean_usize_of_nat(v___x_2797_);
lean_inc_ref(v_doc_2677_);
v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__4(v_doc_2677_, v_unknownIdentifierRanges_2674_, v___x_2803_, v___x_2804_, v___x_2796_, v_a_2675_);
v___y_2785_ = v___x_2805_;
goto v___jp_2784_;
}
}
v___jp_2678_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_inc_ref(v___y_2684_);
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___y_2684_);
lean_ctor_set(v___x_2685_, 1, v___y_2684_);
v___x_2686_ = lean_mk_empty_array_with_capacity(v___y_2681_);
v___x_2687_ = lean_obj_once(&l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0, &l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0_once, _init_l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___closed__0);
lean_inc(v___y_2681_);
v___x_2688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___y_2681_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
v___x_2689_ = lean_array_get_size(v___y_2683_);
v___x_2690_ = l_Array_toSubarray___redArg(v___y_2683_, v___y_2681_, v___x_2689_);
v___x_2691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2688_);
lean_ctor_set(v___x_2691_, 1, v___x_2690_);
v___x_2692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2692_, 0, v___x_2686_);
lean_ctor_set(v___x_2692_, 1, v___x_2691_);
v___x_2693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_2685_, v___y_2680_, v___y_2682_, v___y_2679_, v___x_2692_);
lean_dec_ref(v___y_2680_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2731_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2696_ = v___x_2693_;
v_isShared_2697_ = v_isSharedCheck_2731_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2693_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2731_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v_fst_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2729_; 
v_fst_2698_ = lean_ctor_get(v_a_2694_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v_a_2694_);
if (v_isSharedCheck_2729_ == 0)
{
lean_object* v_unused_2730_; 
v_unused_2730_ = lean_ctor_get(v_a_2694_, 1);
lean_dec(v_unused_2730_);
v___x_2700_ = v_a_2694_;
v_isShared_2701_ = v_isSharedCheck_2729_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_fst_2698_);
lean_dec(v_a_2694_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2729_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_toWorkDoneProgressParams_2702_; lean_object* v_toPartialResultParams_2703_; lean_object* v_title_2704_; lean_object* v_kind_x3f_2705_; lean_object* v_diagnostics_x3f_2706_; lean_object* v_isPreferred_x3f_2707_; lean_object* v_disabled_x3f_2708_; lean_object* v_command_x3f_2709_; lean_object* v_data_x3f_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2727_; 
v_toWorkDoneProgressParams_2702_ = lean_ctor_get(v_action_2673_, 0);
v_toPartialResultParams_2703_ = lean_ctor_get(v_action_2673_, 1);
v_title_2704_ = lean_ctor_get(v_action_2673_, 2);
v_kind_x3f_2705_ = lean_ctor_get(v_action_2673_, 3);
v_diagnostics_x3f_2706_ = lean_ctor_get(v_action_2673_, 4);
v_isPreferred_x3f_2707_ = lean_ctor_get(v_action_2673_, 5);
v_disabled_x3f_2708_ = lean_ctor_get(v_action_2673_, 6);
v_command_x3f_2709_ = lean_ctor_get(v_action_2673_, 8);
v_data_x3f_2710_ = lean_ctor_get(v_action_2673_, 9);
v_isSharedCheck_2727_ = !lean_is_exclusive(v_action_2673_);
if (v_isSharedCheck_2727_ == 0)
{
lean_object* v_unused_2728_; 
v_unused_2728_ = lean_ctor_get(v_action_2673_, 7);
lean_dec(v_unused_2728_);
v___x_2712_ = v_action_2673_;
v_isShared_2713_ = v_isSharedCheck_2727_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_data_x3f_2710_);
lean_inc(v_command_x3f_2709_);
lean_inc(v_disabled_x3f_2708_);
lean_inc(v_isPreferred_x3f_2707_);
lean_inc(v_diagnostics_x3f_2706_);
lean_inc(v_kind_x3f_2705_);
lean_inc(v_title_2704_);
lean_inc(v_toPartialResultParams_2703_);
lean_inc(v_toWorkDoneProgressParams_2702_);
lean_dec(v_action_2673_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2727_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2714_; lean_object* v___x_2716_; 
lean_inc_ref(v_doc_2677_);
v___x_2714_ = l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(v_doc_2677_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 1, v_fst_2698_);
lean_ctor_set(v___x_2700_, 0, v___x_2714_);
v___x_2716_ = v___x_2700_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v___x_2714_);
lean_ctor_set(v_reuseFailAlloc_2726_, 1, v_fst_2698_);
v___x_2716_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2720_; 
v___x_2717_ = l_Lean_Lsp_WorkspaceEdit_ofTextDocumentEdit(v___x_2716_);
v___x_2718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2717_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 7, v___x_2718_);
v___x_2720_ = v___x_2712_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_toWorkDoneProgressParams_2702_);
lean_ctor_set(v_reuseFailAlloc_2725_, 1, v_toPartialResultParams_2703_);
lean_ctor_set(v_reuseFailAlloc_2725_, 2, v_title_2704_);
lean_ctor_set(v_reuseFailAlloc_2725_, 3, v_kind_x3f_2705_);
lean_ctor_set(v_reuseFailAlloc_2725_, 4, v_diagnostics_x3f_2706_);
lean_ctor_set(v_reuseFailAlloc_2725_, 5, v_isPreferred_x3f_2707_);
lean_ctor_set(v_reuseFailAlloc_2725_, 6, v_disabled_x3f_2708_);
lean_ctor_set(v_reuseFailAlloc_2725_, 7, v___x_2718_);
lean_ctor_set(v_reuseFailAlloc_2725_, 8, v_command_x3f_2709_);
lean_ctor_set(v_reuseFailAlloc_2725_, 9, v_data_x3f_2710_);
v___x_2720_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
lean_object* v___x_2721_; lean_object* v___x_2723_; 
v___x_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2720_);
if (v_isShared_2697_ == 0)
{
lean_ctor_set(v___x_2696_, 0, v___x_2721_);
v___x_2723_ = v___x_2696_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec_ref(v_action_2673_);
v_a_2732_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2693_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2693_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
v___jp_2744_:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; 
v___x_2746_ = lean_array_get_size(v_a_2745_);
v___x_2747_ = lean_unsigned_to_nat(0u);
v___x_2748_ = lean_nat_dec_eq(v___x_2746_, v___x_2747_);
if (v___x_2748_ == 0)
{
lean_object* v___x_2749_; size_t v_sz_2750_; size_t v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2781_; 
v___x_2749_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__0));
v_sz_2750_ = lean_array_size(v_a_2745_);
v___x_2751_ = ((size_t)0ULL);
lean_inc_ref(v_a_2745_);
v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__0(v_sz_2750_, v___x_2751_, v_a_2745_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_id_2672_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
v___x_2754_ = l_Lean_Server_RequestM_sendServerRequest___at___00Lean_Server_FileWorker_handleUnknownIdentifierCodeAction_spec__1(v___x_2749_, v___x_2753_, v_a_2675_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2754_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2757_ = v___x_2754_;
v_isShared_2758_ = v_isSharedCheck_2781_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2754_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2781_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; 
v___x_2759_ = lean_task_get_own(v_a_2755_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v_response_2760_; lean_object* v_stx_2761_; lean_object* v___x_2762_; 
lean_del_object(v___x_2757_);
v_response_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_response_2760_);
lean_dec_ref(v___x_2759_);
v_stx_2761_ = lean_ctor_get(v_initSnap_2742_, 3);
v___x_2762_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2761_, v___x_2748_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = ((lean_object*)(l_Lean_Server_FileWorker_handleUnknownIdentifierCodeAction___closed__5));
v___y_2679_ = v___x_2751_;
v___y_2680_ = v_a_2745_;
v___y_2681_ = v___x_2747_;
v___y_2682_ = v_sz_2750_;
v___y_2683_ = v_response_2760_;
v___y_2684_ = v___x_2763_;
goto v___jp_2678_;
}
else
{
lean_object* v_val_2764_; lean_object* v___x_2765_; lean_object* v_line_2766_; lean_object* v___x_2768_; uint8_t v_isShared_2769_; uint8_t v_isSharedCheck_2775_; 
v_val_2764_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_val_2764_);
lean_dec_ref(v___x_2762_);
lean_inc_ref(v_text_2743_);
v___x_2765_ = l_Lean_FileMap_utf8PosToLspPos(v_text_2743_, v_val_2764_);
lean_dec(v_val_2764_);
v_line_2766_ = lean_ctor_get(v___x_2765_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2765_);
if (v_isSharedCheck_2775_ == 0)
{
lean_object* v_unused_2776_; 
v_unused_2776_ = lean_ctor_get(v___x_2765_, 1);
lean_dec(v_unused_2776_);
v___x_2768_ = v___x_2765_;
v_isShared_2769_ = v_isSharedCheck_2775_;
goto v_resetjp_2767_;
}
else
{
lean_inc(v_line_2766_);
lean_dec(v___x_2765_);
v___x_2768_ = lean_box(0);
v_isShared_2769_ = v_isSharedCheck_2775_;
goto v_resetjp_2767_;
}
v_resetjp_2767_:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2770_ = lean_unsigned_to_nat(1u);
v___x_2771_ = lean_nat_add(v_line_2766_, v___x_2770_);
lean_dec(v_line_2766_);
if (v_isShared_2769_ == 0)
{
lean_ctor_set(v___x_2768_, 1, v___x_2747_);
lean_ctor_set(v___x_2768_, 0, v___x_2771_);
v___x_2773_ = v___x_2768_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v___x_2747_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
v___y_2679_ = v___x_2751_;
v___y_2680_ = v_a_2745_;
v___y_2681_ = v___x_2747_;
v___y_2682_ = v_sz_2750_;
v___y_2683_ = v_response_2760_;
v___y_2684_ = v___x_2773_;
goto v___jp_2678_;
}
}
}
}
else
{
lean_object* v___x_2777_; lean_object* v___x_2779_; 
lean_dec(v___x_2759_);
lean_dec_ref(v_a_2745_);
lean_dec_ref(v_action_2673_);
v___x_2777_ = lean_box(0);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2777_);
v___x_2779_ = v___x_2757_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2777_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
else
{
lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec_ref(v_a_2745_);
lean_dec_ref(v_action_2673_);
lean_dec(v_id_2672_);
v___x_2782_ = lean_box(0);
v___x_2783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
return v___x_2783_;
}
}
v___jp_2784_:
{
if (lean_obj_tag(v___y_2785_) == 0)
{
lean_object* v_a_2786_; 
v_a_2786_ = lean_ctor_get(v___y_2785_, 0);
lean_inc(v_a_2786_);
lean_dec_ref(v___y_2785_);
v_a_2745_ = v_a_2786_;
goto v___jp_2744_;
}
else
{
lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2794_; 
lean_dec_ref(v_action_2673_);
lean_dec(v_id_2672_);
v_a_2787_ = lean_ctor_get(v___y_2785_, 0);
v_isSharedCheck_2794_ = !lean_is_exclusive(v___y_2785_);
if (v_isSharedCheck_2794_ == 0)
{
v___x_2789_ = v___y_2785_;
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_dec(v___y_2785_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2794_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v___x_2792_; 
if (v_isShared_2790_ == 0)
{
v___x_2792_ = v___x_2789_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
v___x_2792_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
return v___x_2792_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f___boxed(lean_object* v_id_2806_, lean_object* v_action_2807_, lean_object* v_unknownIdentifierRanges_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f(v_id_2806_, v_action_2807_, v_unknownIdentifierRanges_2808_, v_a_2809_);
lean_dec_ref(v_a_2809_);
lean_dec_ref(v_unknownIdentifierRanges_2808_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1(lean_object* v_00_u03b2_2812_, lean_object* v_m_2813_, lean_object* v_a_2814_, lean_object* v_b_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1___redArg(v_m_2813_, v_a_2814_, v_b_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(lean_object* v_00_u03b2_2817_, lean_object* v_m_2818_, lean_object* v_a_2819_){
_start:
{
uint8_t v___x_2820_; 
v___x_2820_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___redArg(v_m_2818_, v_a_2819_);
return v___x_2820_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2___boxed(lean_object* v_00_u03b2_2821_, lean_object* v_m_2822_, lean_object* v_a_2823_){
_start:
{
uint8_t v_res_2824_; lean_object* v_r_2825_; 
v_res_2824_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__2(v_00_u03b2_2821_, v_m_2822_, v_a_2823_);
lean_dec(v_a_2823_);
lean_dec_ref(v_m_2822_);
v_r_2825_ = lean_box(v_res_2824_);
return v_r_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(lean_object* v___x_2826_, lean_object* v_as_2827_, size_t v_sz_2828_, size_t v_i_2829_, lean_object* v_b_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v___x_2833_; 
v___x_2833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___redArg(v___x_2826_, v_as_2827_, v_sz_2828_, v_i_2829_, v_b_2830_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3___boxed(lean_object* v___x_2834_, lean_object* v_as_2835_, lean_object* v_sz_2836_, lean_object* v_i_2837_, lean_object* v_b_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
size_t v_sz_boxed_2841_; size_t v_i_boxed_2842_; lean_object* v_res_2843_; 
v_sz_boxed_2841_ = lean_unbox_usize(v_sz_2836_);
lean_dec(v_sz_2836_);
v_i_boxed_2842_ = lean_unbox_usize(v_i_2837_);
lean_dec(v_i_2837_);
v_res_2843_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__3(v___x_2834_, v_as_2835_, v_sz_boxed_2841_, v_i_boxed_2842_, v_b_2838_, v___y_2839_);
lean_dec_ref(v___y_2839_);
lean_dec_ref(v_as_2835_);
return v_res_2843_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(lean_object* v_00_u03b2_2844_, lean_object* v_a_2845_, lean_object* v_x_2846_){
_start:
{
uint8_t v___x_2847_; 
v___x_2847_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___redArg(v_a_2845_, v_x_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1___boxed(lean_object* v_00_u03b2_2848_, lean_object* v_a_2849_, lean_object* v_x_2850_){
_start:
{
uint8_t v_res_2851_; lean_object* v_r_2852_; 
v_res_2851_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__1(v_00_u03b2_2848_, v_a_2849_, v_x_2850_);
lean_dec(v_x_2850_);
lean_dec(v_a_2849_);
v_r_2852_ = lean_box(v_res_2851_);
return v_r_2852_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2(lean_object* v_00_u03b2_2853_, lean_object* v_data_2854_){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2___redArg(v_data_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2856_, lean_object* v_i_2857_, lean_object* v_source_2858_, lean_object* v_target_2859_){
_start:
{
lean_object* v___x_2860_; 
v___x_2860_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3___redArg(v_i_2857_, v_source_2858_, v_target_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7(lean_object* v_00_u03b2_2861_, lean_object* v_x_2862_, lean_object* v_x_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Server_FileWorker_handleResolveImportAllUnknownIdentifiersCodeAction_x3f_spec__1_spec__2_spec__3_spec__7___redArg(v_x_2862_, v_x_2863_);
return v___x_2864_;
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
