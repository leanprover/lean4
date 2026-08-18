// Lean compiler output
// Module: Lean.Server.FileWorker.InlayHints
// Imports: public import Lean.Server.GoTo public import Lean.Server.Requests
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Server_documentUriFromModule_x3f(lean_object*);
lean_object* l_Lean_FileMap_utf8RangeToLspRange(lean_object*, lean_object*);
lean_object* l_Lean_Lsp_instFromJsonInlayHintParams_fromJson(lean_object*);
lean_object* l_Lean_Json_compress(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Lsp_instToJsonInlayHint_toJson(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_FileMap_lspRangeToUtf8Range(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Syntax_Range_bsize(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_Range_contains(lean_object*, lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Syntax_Range_overlaps(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f(lean_object*);
lean_object* l_Lean_Elab_InlayHint_resolveDeferred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
uint8_t l_Lean_Elab_instBEqInlayHintTextEdit_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Server_statefulRequestHandlers;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Server_instInhabitedRequestError_default;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_endPos(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_Server_RequestCancellationToken_cancellationTasks(lean_object*);
lean_object* l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(lean_object*, uint32_t, lean_object*);
uint8_t l_Lean_Server_RequestCancellationToken_wasCancelled(lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_InlayHintKind_toLspInlayHintKind(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toLspInlayHintKind___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintInfo_toLspInlayHint(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintInfo_toLspInlayHint___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Lean.Server.FileWorker.InlayHints"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Server.FileWorker.applyEditToHint\?"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Got position "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = " that should have been invalidated by edit at range "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value;
static const lean_string_object l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Server"};
static const lean_object* l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value;
static const lean_string_object l_Lean_Server_FileWorker_instImpl___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "FileWorker"};
static const lean_object* l_Lean_Server_FileWorker_instImpl___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value;
static const lean_string_object l_Lean_Server_FileWorker_instImpl___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "InlayHintState"};
static const lean_object* l_Lean_Server_FileWorker_instImpl___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value;
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_0),((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(251, 1, 140, 35, 91, 244, 83, 213)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_1),((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(232, 14, 27, 113, 182, 128, 119, 36)}};
static const lean_ctor_object l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value_aux_2),((lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value),LEAN_SCALAR_PTR_LITERAL(105, 230, 109, 194, 171, 115, 34, 220)}};
static const lean_object* l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_ = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instTypeNameInlayHintState = (const lean_object*)&l_Lean_Server_FileWorker_instImpl___closed__4_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16__value;
static const lean_array_object l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instInhabitedInlayHintState_default = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_instInhabitedInlayHintState = (const lean_object*)&l_Lean_Server_FileWorker_instInhabitedInlayHintState_default___closed__1_value;
static const lean_array_object l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_InlayHintState_init___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value;
static const lean_ctor_object l_Lean_Server_FileWorker_InlayHintState_init___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Server_FileWorker_InlayHintState_init___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_InlayHintState_init___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Server_FileWorker_InlayHintState_init = (const lean_object*)&l_Lean_Server_FileWorker_InlayHintState_init___closed__1_value;
static lean_once_cell_t l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Server.InfoUtils.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Lean.Server.InfoUtils"};
static const lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_handleInlayHints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Server.FileWorker.handleInlayHints"};
static const lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleInlayHints___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_handleInlayHints___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 399, .m_capacity = 399, .m_length = 398, .m_data = "assertion violation: finishedSnaps >= oldFinishedSnaps\n  -- VS Code emits inlay hint requests *every time the user scrolls*. This is reasonably expensive,\n  -- so in addition to re-using old inlay hints from parts of the file that haven't been processed\n  -- yet, we also re-use old inlay hints from parts of the file that have been processed already\n  -- with the current state of the document.\n  "};
static const lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleInlayHints___closed__1_value;
static lean_once_cell_t l_Lean_Server_FileWorker_handleInlayHints___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Server_FileWorker_InlayHintState_init___closed__0_value)}};
static const lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Cannot parse request params: "};
static const lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0_value;
static const lean_string_object l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1 = (const lean_object*)&l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "': already registered"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "textDocument/inlayHint"};
static const lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "workspace/inlayHint/refresh"};
static const lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleInlayHints___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation(lean_object* v_text_1_, lean_object* v_l_2_){
_start:
{
lean_object* v_module_4_; lean_object* v_range_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_42_; 
v_module_4_ = lean_ctor_get(v_l_2_, 0);
v_range_5_ = lean_ctor_get(v_l_2_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_l_2_);
if (v_isSharedCheck_42_ == 0)
{
v___x_7_ = v_l_2_;
v_isShared_8_ = v_isSharedCheck_42_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_range_5_);
lean_inc(v_module_4_);
lean_dec(v_l_2_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_42_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_Server_documentUriFromModule_x3f(v_module_4_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_33_; 
v_a_10_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_33_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_33_ == 0)
{
v___x_12_ = v___x_9_;
v_isShared_13_ = v_isSharedCheck_33_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_dec(v___x_9_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_33_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
if (lean_obj_tag(v_a_10_) == 1)
{
lean_object* v_val_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_28_; 
v_val_14_ = lean_ctor_get(v_a_10_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v_a_10_);
if (v_isSharedCheck_28_ == 0)
{
v___x_16_ = v_a_10_;
v_isShared_17_ = v_isSharedCheck_28_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_val_14_);
lean_dec(v_a_10_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_28_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_20_; 
v___x_18_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_1_, v_range_5_);
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___x_18_);
lean_ctor_set(v___x_7_, 0, v_val_14_);
v___x_20_ = v___x_7_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_val_14_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v___x_18_);
v___x_20_ = v_reuseFailAlloc_27_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_22_; 
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 0, v___x_20_);
v___x_22_ = v___x_16_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_20_);
v___x_22_ = v_reuseFailAlloc_26_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
lean_object* v___x_24_; 
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_22_);
v___x_24_ = v___x_12_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_22_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
}
}
else
{
lean_object* v___x_29_; lean_object* v___x_31_; 
lean_dec(v_a_10_);
lean_del_object(v___x_7_);
lean_dec_ref(v_range_5_);
lean_dec_ref(v_text_1_);
v___x_29_ = lean_box(0);
if (v_isShared_13_ == 0)
{
lean_ctor_set(v___x_12_, 0, v___x_29_);
v___x_31_ = v___x_12_;
goto v_reusejp_30_;
}
else
{
lean_object* v_reuseFailAlloc_32_; 
v_reuseFailAlloc_32_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_32_, 0, v___x_29_);
v___x_31_ = v_reuseFailAlloc_32_;
goto v_reusejp_30_;
}
v_reusejp_30_:
{
return v___x_31_;
}
}
}
}
else
{
lean_object* v_a_34_; lean_object* v___x_36_; uint8_t v_isShared_37_; uint8_t v_isSharedCheck_41_; 
lean_del_object(v___x_7_);
lean_dec_ref(v_range_5_);
lean_dec_ref(v_text_1_);
v_a_34_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_41_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_41_ == 0)
{
v___x_36_ = v___x_9_;
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
else
{
lean_inc(v_a_34_);
lean_dec(v___x_9_);
v___x_36_ = lean_box(0);
v_isShared_37_ = v_isSharedCheck_41_;
goto v_resetjp_35_;
}
v_resetjp_35_:
{
lean_object* v___x_39_; 
if (v_isShared_37_ == 0)
{
v___x_39_ = v___x_36_;
goto v_reusejp_38_;
}
else
{
lean_object* v_reuseFailAlloc_40_; 
v_reuseFailAlloc_40_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_40_, 0, v_a_34_);
v___x_39_ = v_reuseFailAlloc_40_;
goto v_reusejp_38_;
}
v_reusejp_38_:
{
return v___x_39_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation___boxed(lean_object* v_text_43_, lean_object* v_l_44_, lean_object* v_a_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Lean_Elab_InlayHintLinkLocation_toLspLocation(v_text_43_, v_l_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(lean_object* v_text_47_, lean_object* v_p_48_){
_start:
{
lean_object* v_value_50_; lean_object* v_tooltip_x3f_51_; lean_object* v_location_x3f_52_; lean_object* v___y_54_; lean_object* v___y_55_; lean_object* v_a_60_; 
v_value_50_ = lean_ctor_get(v_p_48_, 0);
lean_inc_ref(v_value_50_);
v_tooltip_x3f_51_ = lean_ctor_get(v_p_48_, 1);
lean_inc(v_tooltip_x3f_51_);
v_location_x3f_52_ = lean_ctor_get(v_p_48_, 2);
lean_inc(v_location_x3f_52_);
lean_dec_ref(v_p_48_);
if (lean_obj_tag(v_location_x3f_52_) == 0)
{
lean_object* v___x_73_; 
lean_dec_ref(v_text_47_);
v___x_73_ = lean_box(0);
v_a_60_ = v___x_73_;
goto v___jp_59_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_75_; 
v_val_74_ = lean_ctor_get(v_location_x3f_52_, 0);
lean_inc(v_val_74_);
lean_dec_ref_known(v_location_x3f_52_, 1);
v___x_75_ = l_Lean_Elab_InlayHintLinkLocation_toLspLocation(v_text_47_, v_val_74_);
if (lean_obj_tag(v___x_75_) == 0)
{
lean_object* v_a_76_; 
v_a_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v_a_76_);
lean_dec_ref_known(v___x_75_, 1);
v_a_60_ = v_a_76_;
goto v___jp_59_;
}
else
{
lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_84_; 
lean_dec(v_tooltip_x3f_51_);
lean_dec_ref(v_value_50_);
v_a_77_ = lean_ctor_get(v___x_75_, 0);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_84_ == 0)
{
v___x_79_ = v___x_75_;
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_84_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_a_77_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
v___jp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = lean_box(0);
v___x_57_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_57_, 0, v_value_50_);
lean_ctor_set(v___x_57_, 1, v___y_55_);
lean_ctor_set(v___x_57_, 2, v___y_54_);
lean_ctor_set(v___x_57_, 3, v___x_56_);
v___x_58_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
return v___x_58_;
}
v___jp_59_:
{
if (lean_obj_tag(v_tooltip_x3f_51_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_box(0);
v___y_54_ = v_a_60_;
v___y_55_ = v___x_61_;
goto v___jp_53_;
}
else
{
lean_object* v_val_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_72_; 
v_val_62_ = lean_ctor_get(v_tooltip_x3f_51_, 0);
v_isSharedCheck_72_ = !lean_is_exclusive(v_tooltip_x3f_51_);
if (v_isSharedCheck_72_ == 0)
{
v___x_64_ = v_tooltip_x3f_51_;
v_isShared_65_ = v_isSharedCheck_72_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_val_62_);
lean_dec(v_tooltip_x3f_51_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_72_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_66_ = 1;
v___x_67_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_67_, 0, v_val_62_);
lean_ctor_set_uint8(v___x_67_, sizeof(void*)*1, v___x_66_);
v___x_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_68_);
v___x_70_ = v___x_64_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
v___y_54_ = v_a_60_;
v___y_55_ = v___x_70_;
goto v___jp_53_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart___boxed(lean_object* v_text_85_, lean_object* v_p_86_, lean_object* v_a_87_){
_start:
{
lean_object* v_res_88_; 
v_res_88_ = l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(v_text_85_, v_p_86_);
return v_res_88_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(lean_object* v_text_89_, size_t v_sz_90_, size_t v_i_91_, lean_object* v_bs_92_){
_start:
{
uint8_t v___x_94_; 
v___x_94_ = lean_usize_dec_lt(v_i_91_, v_sz_90_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; 
lean_dec_ref(v_text_89_);
v___x_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_95_, 0, v_bs_92_);
return v___x_95_;
}
else
{
lean_object* v_v_96_; lean_object* v___x_97_; 
v_v_96_ = lean_array_uget_borrowed(v_bs_92_, v_i_91_);
lean_inc(v_v_96_);
lean_inc_ref(v_text_89_);
v___x_97_ = l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(v_text_89_, v_v_96_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v_bs_x27_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_97_, 1);
v___x_99_ = lean_unsigned_to_nat(0u);
v_bs_x27_100_ = lean_array_uset(v_bs_92_, v_i_91_, v___x_99_);
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_add(v_i_91_, v___x_101_);
v___x_103_ = lean_array_uset(v_bs_x27_100_, v_i_91_, v_a_98_);
v_i_91_ = v___x_102_;
v_bs_92_ = v___x_103_;
goto _start;
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec_ref(v_bs_92_);
lean_dec_ref(v_text_89_);
v_a_105_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_97_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_97_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___x_110_; 
if (v_isShared_108_ == 0)
{
v___x_110_ = v___x_107_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_a_105_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0___boxed(lean_object* v_text_113_, lean_object* v_sz_114_, lean_object* v_i_115_, lean_object* v_bs_116_, lean_object* v___y_117_){
_start:
{
size_t v_sz_boxed_118_; size_t v_i_boxed_119_; lean_object* v_res_120_; 
v_sz_boxed_118_ = lean_unbox_usize(v_sz_114_);
lean_dec(v_sz_114_);
v_i_boxed_119_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(v_text_113_, v_sz_boxed_118_, v_i_boxed_119_, v_bs_116_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(lean_object* v_text_121_, lean_object* v_x_122_){
_start:
{
if (lean_obj_tag(v_x_122_) == 0)
{
lean_object* v_n_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_132_; 
lean_dec_ref(v_text_121_);
v_n_124_ = lean_ctor_get(v_x_122_, 0);
v_isSharedCheck_132_ = !lean_is_exclusive(v_x_122_);
if (v_isSharedCheck_132_ == 0)
{
v___x_126_ = v_x_122_;
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_n_124_);
lean_dec(v_x_122_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_132_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_n_124_);
v___x_129_ = v_reuseFailAlloc_131_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
lean_object* v___x_130_; 
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
}
else
{
lean_object* v_p_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_159_; 
v_p_133_ = lean_ctor_get(v_x_122_, 0);
v_isSharedCheck_159_ = !lean_is_exclusive(v_x_122_);
if (v_isSharedCheck_159_ == 0)
{
v___x_135_ = v_x_122_;
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_p_133_);
lean_dec(v_x_122_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_159_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
size_t v_sz_137_; size_t v___x_138_; lean_object* v___x_139_; 
v_sz_137_ = lean_array_size(v_p_133_);
v___x_138_ = ((size_t)0ULL);
v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(v_text_121_, v_sz_137_, v___x_138_, v_p_133_);
if (lean_obj_tag(v___x_139_) == 0)
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_150_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_150_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v_a_140_);
v___x_145_ = v___x_135_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_149_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_147_; 
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_145_);
v___x_147_ = v___x_142_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
lean_del_object(v___x_135_);
v_a_151_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_139_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_139_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___boxed(lean_object* v_text_160_, lean_object* v_x_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_res_163_; 
v_res_163_ = l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(v_text_160_, v_x_161_);
return v_res_163_;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_InlayHintKind_toLspInlayHintKind(uint8_t v_x_164_){
_start:
{
if (v_x_164_ == 0)
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
else
{
uint8_t v___x_166_; 
v___x_166_ = 1;
return v___x_166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toLspInlayHintKind___boxed(lean_object* v_x_167_){
_start:
{
uint8_t v_x_18__boxed_168_; uint8_t v_res_169_; lean_object* v_r_170_; 
v_x_18__boxed_168_ = lean_unbox(v_x_167_);
v_res_169_ = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(v_x_18__boxed_168_);
v_r_170_ = lean_box(v_res_169_);
return v_r_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(lean_object* v_text_171_, lean_object* v_e_172_){
_start:
{
lean_object* v_range_173_; lean_object* v_newText_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v_range_173_ = lean_ctor_get(v_e_172_, 0);
lean_inc_ref(v_range_173_);
v_newText_174_ = lean_ctor_get(v_e_172_, 1);
lean_inc_ref(v_newText_174_);
lean_dec_ref(v_e_172_);
v___x_175_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_171_, v_range_173_);
v___x_176_ = lean_box(0);
v___x_177_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_177_, 0, v___x_175_);
lean_ctor_set(v___x_177_, 1, v_newText_174_);
lean_ctor_set(v___x_177_, 2, v___x_176_);
lean_ctor_set(v___x_177_, 3, v___x_176_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(lean_object* v_text_178_, size_t v_sz_179_, size_t v_i_180_, lean_object* v_bs_181_){
_start:
{
uint8_t v___x_182_; 
v___x_182_ = lean_usize_dec_lt(v_i_180_, v_sz_179_);
if (v___x_182_ == 0)
{
lean_dec_ref(v_text_178_);
return v_bs_181_;
}
else
{
lean_object* v_v_183_; lean_object* v___x_184_; lean_object* v_bs_x27_185_; lean_object* v___x_186_; size_t v___x_187_; size_t v___x_188_; lean_object* v___x_189_; 
v_v_183_ = lean_array_uget(v_bs_181_, v_i_180_);
v___x_184_ = lean_unsigned_to_nat(0u);
v_bs_x27_185_ = lean_array_uset(v_bs_181_, v_i_180_, v___x_184_);
lean_inc_ref(v_text_178_);
v___x_186_ = l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(v_text_178_, v_v_183_);
v___x_187_ = ((size_t)1ULL);
v___x_188_ = lean_usize_add(v_i_180_, v___x_187_);
v___x_189_ = lean_array_uset(v_bs_x27_185_, v_i_180_, v___x_186_);
v_i_180_ = v___x_188_;
v_bs_181_ = v___x_189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0___boxed(lean_object* v_text_191_, lean_object* v_sz_192_, lean_object* v_i_193_, lean_object* v_bs_194_){
_start:
{
size_t v_sz_boxed_195_; size_t v_i_boxed_196_; lean_object* v_res_197_; 
v_sz_boxed_195_ = lean_unbox_usize(v_sz_192_);
lean_dec(v_sz_192_);
v_i_boxed_196_ = lean_unbox_usize(v_i_193_);
lean_dec(v_i_193_);
v_res_197_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(v_text_191_, v_sz_boxed_195_, v_i_boxed_196_, v_bs_194_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintInfo_toLspInlayHint(lean_object* v_text_198_, lean_object* v_i_199_){
_start:
{
lean_object* v_position_201_; lean_object* v_label_202_; lean_object* v_kind_x3f_203_; lean_object* v_textEdits_204_; lean_object* v_tooltip_x3f_205_; uint8_t v_paddingLeft_206_; uint8_t v_paddingRight_207_; lean_object* v___x_208_; 
v_position_201_ = lean_ctor_get(v_i_199_, 0);
lean_inc(v_position_201_);
v_label_202_ = lean_ctor_get(v_i_199_, 1);
lean_inc_ref(v_label_202_);
v_kind_x3f_203_ = lean_ctor_get(v_i_199_, 2);
lean_inc(v_kind_x3f_203_);
v_textEdits_204_ = lean_ctor_get(v_i_199_, 3);
lean_inc_ref(v_textEdits_204_);
v_tooltip_x3f_205_ = lean_ctor_get(v_i_199_, 4);
lean_inc(v_tooltip_x3f_205_);
v_paddingLeft_206_ = lean_ctor_get_uint8(v_i_199_, sizeof(void*)*5);
v_paddingRight_207_ = lean_ctor_get_uint8(v_i_199_, sizeof(void*)*5 + 1);
lean_dec_ref(v_i_199_);
lean_inc_ref(v_text_198_);
v___x_208_ = l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(v_text_198_, v_label_202_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_257_; 
v_a_209_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_257_ == 0)
{
v___x_211_ = v___x_208_;
v_isShared_212_ = v_isSharedCheck_257_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_208_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_257_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_213_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_228_; 
lean_inc_ref(v_text_198_);
v___x_213_ = l_Lean_FileMap_utf8PosToLspPos(v_text_198_, v_position_201_);
lean_dec(v_position_201_);
if (lean_obj_tag(v_kind_x3f_203_) == 0)
{
lean_object* v___x_245_; 
v___x_245_ = lean_box(0);
v___y_228_ = v___x_245_;
goto v___jp_227_;
}
else
{
lean_object* v_val_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_256_; 
v_val_246_ = lean_ctor_get(v_kind_x3f_203_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v_kind_x3f_203_);
if (v_isSharedCheck_256_ == 0)
{
v___x_248_ = v_kind_x3f_203_;
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_val_246_);
lean_dec(v_kind_x3f_203_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
uint8_t v___x_250_; uint8_t v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_250_ = lean_unbox(v_val_246_);
lean_dec(v_val_246_);
v___x_251_ = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(v___x_250_);
v___x_252_ = lean_box(v___x_251_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 0, v___x_252_);
v___x_254_ = v___x_248_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
v___y_228_ = v___x_254_;
goto v___jp_227_;
}
}
}
v___jp_214_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_225_; 
v___x_218_ = lean_box(v_paddingLeft_206_);
v___x_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
v___x_220_ = lean_box(v_paddingRight_207_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
v___x_222_ = lean_box(0);
v___x_223_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_223_, 0, v___x_213_);
lean_ctor_set(v___x_223_, 1, v_a_209_);
lean_ctor_set(v___x_223_, 2, v___y_216_);
lean_ctor_set(v___x_223_, 3, v___y_215_);
lean_ctor_set(v___x_223_, 4, v___y_217_);
lean_ctor_set(v___x_223_, 5, v___x_219_);
lean_ctor_set(v___x_223_, 6, v___x_221_);
lean_ctor_set(v___x_223_, 7, v___x_222_);
if (v_isShared_212_ == 0)
{
lean_ctor_set(v___x_211_, 0, v___x_223_);
v___x_225_ = v___x_211_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_226_; 
v_reuseFailAlloc_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_226_, 0, v___x_223_);
v___x_225_ = v_reuseFailAlloc_226_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
return v___x_225_;
}
}
v___jp_227_:
{
size_t v_sz_229_; size_t v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_sz_229_ = lean_array_size(v_textEdits_204_);
v___x_230_ = ((size_t)0ULL);
v___x_231_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(v_text_198_, v_sz_229_, v___x_230_, v_textEdits_204_);
v___x_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
if (lean_obj_tag(v_tooltip_x3f_205_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
v___y_215_ = v___x_232_;
v___y_216_ = v___y_228_;
v___y_217_ = v___x_233_;
goto v___jp_214_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_244_; 
v_val_234_ = lean_ctor_get(v_tooltip_x3f_205_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v_tooltip_x3f_205_);
if (v_isSharedCheck_244_ == 0)
{
v___x_236_ = v_tooltip_x3f_205_;
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_val_234_);
lean_dec(v_tooltip_x3f_205_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
uint8_t v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_238_ = 1;
v___x_239_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_239_, 0, v_val_234_);
lean_ctor_set_uint8(v___x_239_, sizeof(void*)*1, v___x_238_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 0, v___x_240_);
v___x_242_ = v___x_236_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
v___y_215_ = v___x_232_;
v___y_216_ = v___y_228_;
v___y_217_ = v___x_242_;
goto v___jp_214_;
}
}
}
}
}
}
else
{
lean_object* v_a_258_; lean_object* v___x_260_; uint8_t v_isShared_261_; uint8_t v_isSharedCheck_265_; 
lean_dec(v_tooltip_x3f_205_);
lean_dec_ref(v_textEdits_204_);
lean_dec(v_kind_x3f_203_);
lean_dec(v_position_201_);
lean_dec_ref(v_text_198_);
v_a_258_ = lean_ctor_get(v___x_208_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_208_);
if (v_isSharedCheck_265_ == 0)
{
v___x_260_ = v___x_208_;
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
else
{
lean_inc(v_a_258_);
lean_dec(v___x_208_);
v___x_260_ = lean_box(0);
v_isShared_261_ = v_isSharedCheck_265_;
goto v_resetjp_259_;
}
v_resetjp_259_:
{
lean_object* v___x_263_; 
if (v_isShared_261_ == 0)
{
v___x_263_ = v___x_260_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_a_258_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintInfo_toLspInlayHint___boxed(lean_object* v_text_266_, lean_object* v_i_267_, lean_object* v_a_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v_text_266_, v_i_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__0(lean_object* v_a_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lean_nat_to_int(v_a_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(lean_object* v_msg_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_unsigned_to_nat(0u);
v___x_274_ = lean_panic_fn_borrowed(v___x_273_, v_msg_272_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(lean_object* v_range_280_, lean_object* v_byteOffset_281_, lean_object* v_p_282_){
_start:
{
lean_object* v_start_283_; lean_object* v_stop_284_; uint8_t v___x_285_; 
v_start_283_ = lean_ctor_get(v_range_280_, 0);
lean_inc(v_start_283_);
v_stop_284_ = lean_ctor_get(v_range_280_, 1);
lean_inc(v_stop_284_);
lean_dec_ref(v_range_280_);
v___x_285_ = lean_nat_dec_lt(v_stop_284_, v_p_282_);
if (v___x_285_ == 0)
{
uint8_t v___x_286_; 
v___x_286_ = lean_nat_dec_lt(v_p_282_, v_start_283_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_287_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_288_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1));
v___x_289_ = lean_unsigned_to_nat(87u);
v___x_290_ = lean_unsigned_to_nat(6u);
v___x_291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2));
v___x_292_ = l_Nat_reprFast(v_p_282_);
v___x_293_ = lean_string_append(v___x_291_, v___x_292_);
lean_dec_ref(v___x_292_);
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3));
v___x_295_ = lean_string_append(v___x_293_, v___x_294_);
v___x_296_ = l_Nat_reprFast(v_start_283_);
v___x_297_ = lean_string_append(v___x_295_, v___x_296_);
lean_dec_ref(v___x_296_);
v___x_298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4));
v___x_299_ = lean_string_append(v___x_297_, v___x_298_);
v___x_300_ = l_Nat_reprFast(v_stop_284_);
v___x_301_ = lean_string_append(v___x_299_, v___x_300_);
lean_dec_ref(v___x_300_);
v___x_302_ = l_mkPanicMessageWithDecl(v___x_287_, v___x_288_, v___x_289_, v___x_290_, v___x_301_);
lean_dec_ref(v___x_301_);
v___x_303_ = l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(v___x_302_);
return v___x_303_;
}
else
{
lean_dec(v_stop_284_);
lean_dec(v_start_283_);
return v_p_282_;
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_stop_284_);
lean_dec(v_start_283_);
v___x_304_ = lean_nat_to_int(v_p_282_);
v___x_305_ = lean_int_add(v___x_304_, v_byteOffset_281_);
lean_dec(v___x_304_);
v___x_306_ = l_Int_toNat(v___x_305_);
lean_dec(v___x_305_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___boxed(lean_object* v_range_307_, lean_object* v_byteOffset_308_, lean_object* v_p_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_307_, v_byteOffset_308_, v_p_309_);
lean_dec(v_byteOffset_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(lean_object* v_range_311_, lean_object* v_byteOffset_312_, size_t v_sz_313_, size_t v_i_314_, lean_object* v_bs_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = lean_usize_dec_lt(v_i_314_, v_sz_313_);
if (v___x_316_ == 0)
{
lean_dec_ref(v_range_311_);
return v_bs_315_;
}
else
{
lean_object* v_v_317_; lean_object* v_range_318_; lean_object* v_newText_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_343_; 
v_v_317_ = lean_array_uget(v_bs_315_, v_i_314_);
v_range_318_ = lean_ctor_get(v_v_317_, 0);
v_newText_319_ = lean_ctor_get(v_v_317_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_v_317_);
if (v_isSharedCheck_343_ == 0)
{
v___x_321_ = v_v_317_;
v_isShared_322_ = v_isSharedCheck_343_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_newText_319_);
lean_inc(v_range_318_);
lean_dec(v_v_317_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_343_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v_start_323_; lean_object* v_stop_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_342_; 
v_start_323_ = lean_ctor_get(v_range_318_, 0);
v_stop_324_ = lean_ctor_get(v_range_318_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_range_318_);
if (v_isSharedCheck_342_ == 0)
{
v___x_326_ = v_range_318_;
v_isShared_327_ = v_isSharedCheck_342_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_stop_324_);
lean_inc(v_start_323_);
lean_dec(v_range_318_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_342_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v_bs_x27_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v_bs_x27_329_ = lean_array_uset(v_bs_315_, v_i_314_, v___x_328_);
lean_inc_ref_n(v_range_311_, 2);
v___x_330_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_311_, v_byteOffset_312_, v_start_323_);
v___x_331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_311_, v_byteOffset_312_, v_stop_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 1, v___x_331_);
lean_ctor_set(v___x_326_, 0, v___x_330_);
v___x_333_ = v___x_326_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_331_);
v___x_333_ = v_reuseFailAlloc_341_;
goto v_reusejp_332_;
}
v_reusejp_332_:
{
lean_object* v___x_335_; 
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 0, v___x_333_);
v___x_335_ = v___x_321_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_333_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_newText_319_);
v___x_335_ = v_reuseFailAlloc_340_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
size_t v___x_336_; size_t v___x_337_; lean_object* v___x_338_; 
v___x_336_ = ((size_t)1ULL);
v___x_337_ = lean_usize_add(v_i_314_, v___x_336_);
v___x_338_ = lean_array_uset(v_bs_x27_329_, v_i_314_, v___x_335_);
v_i_314_ = v___x_337_;
v_bs_315_ = v___x_338_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2___boxed(lean_object* v_range_344_, lean_object* v_byteOffset_345_, lean_object* v_sz_346_, lean_object* v_i_347_, lean_object* v_bs_348_){
_start:
{
size_t v_sz_boxed_349_; size_t v_i_boxed_350_; lean_object* v_res_351_; 
v_sz_boxed_349_ = lean_unbox_usize(v_sz_346_);
lean_dec(v_sz_346_);
v_i_boxed_350_ = lean_unbox_usize(v_i_347_);
lean_dec(v_i_347_);
v_res_351_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_344_, v_byteOffset_345_, v_sz_boxed_349_, v_i_boxed_350_, v_bs_348_);
lean_dec(v_byteOffset_345_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(lean_object* v_range_352_, lean_object* v_byteOffset_353_, size_t v_sz_354_, size_t v_i_355_, lean_object* v_bs_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = lean_usize_dec_lt(v_i_355_, v_sz_354_);
if (v___x_357_ == 0)
{
lean_dec_ref(v_range_352_);
return v_bs_356_;
}
else
{
lean_object* v_v_358_; lean_object* v_range_359_; lean_object* v_newText_360_; lean_object* v___x_362_; uint8_t v_isShared_363_; uint8_t v_isSharedCheck_384_; 
v_v_358_ = lean_array_uget(v_bs_356_, v_i_355_);
v_range_359_ = lean_ctor_get(v_v_358_, 0);
v_newText_360_ = lean_ctor_get(v_v_358_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_v_358_);
if (v_isSharedCheck_384_ == 0)
{
v___x_362_ = v_v_358_;
v_isShared_363_ = v_isSharedCheck_384_;
goto v_resetjp_361_;
}
else
{
lean_inc(v_newText_360_);
lean_inc(v_range_359_);
lean_dec(v_v_358_);
v___x_362_ = lean_box(0);
v_isShared_363_ = v_isSharedCheck_384_;
goto v_resetjp_361_;
}
v_resetjp_361_:
{
lean_object* v_start_364_; lean_object* v_stop_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_383_; 
v_start_364_ = lean_ctor_get(v_range_359_, 0);
v_stop_365_ = lean_ctor_get(v_range_359_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v_range_359_);
if (v_isSharedCheck_383_ == 0)
{
v___x_367_ = v_range_359_;
v_isShared_368_ = v_isSharedCheck_383_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_stop_365_);
lean_inc(v_start_364_);
lean_dec(v_range_359_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_383_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_369_; lean_object* v_bs_x27_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
v___x_369_ = lean_unsigned_to_nat(0u);
v_bs_x27_370_ = lean_array_uset(v_bs_356_, v_i_355_, v___x_369_);
lean_inc_ref_n(v_range_352_, 2);
v___x_371_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_352_, v_byteOffset_353_, v_start_364_);
v___x_372_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_352_, v_byteOffset_353_, v_stop_365_);
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 1, v___x_372_);
lean_ctor_set(v___x_367_, 0, v___x_371_);
v___x_374_ = v___x_367_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_371_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_382_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_376_; 
if (v_isShared_363_ == 0)
{
lean_ctor_set(v___x_362_, 0, v___x_374_);
v___x_376_ = v___x_362_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_newText_360_);
v___x_376_ = v_reuseFailAlloc_381_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
size_t v___x_377_; size_t v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_add(v_i_355_, v___x_377_);
v___x_379_ = lean_array_uset(v_bs_x27_370_, v_i_355_, v___x_376_);
v___x_380_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_352_, v_byteOffset_353_, v_sz_354_, v___x_378_, v___x_379_);
return v___x_380_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___boxed(lean_object* v_range_385_, lean_object* v_byteOffset_386_, lean_object* v_sz_387_, lean_object* v_i_388_, lean_object* v_bs_389_){
_start:
{
size_t v_sz_boxed_390_; size_t v_i_boxed_391_; lean_object* v_res_392_; 
v_sz_boxed_390_ = lean_unbox_usize(v_sz_387_);
lean_dec(v_sz_387_);
v_i_boxed_391_ = lean_unbox_usize(v_i_388_);
lean_dec(v_i_388_);
v_res_392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_385_, v_byteOffset_386_, v_sz_boxed_390_, v_i_boxed_391_, v_bs_389_);
lean_dec(v_byteOffset_386_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(lean_object* v_hintMod_393_, lean_object* v_range_394_, lean_object* v_byteOffset_395_, size_t v_sz_396_, size_t v_i_397_, lean_object* v_bs_398_){
_start:
{
uint8_t v___x_399_; 
v___x_399_ = lean_usize_dec_lt(v_i_397_, v_sz_396_);
if (v___x_399_ == 0)
{
lean_dec_ref(v_range_394_);
return v_bs_398_;
}
else
{
lean_object* v_v_400_; lean_object* v_value_401_; lean_object* v_tooltip_x3f_402_; lean_object* v_location_x3f_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_446_; 
v_v_400_ = lean_array_uget(v_bs_398_, v_i_397_);
v_value_401_ = lean_ctor_get(v_v_400_, 0);
v_tooltip_x3f_402_ = lean_ctor_get(v_v_400_, 1);
v_location_x3f_403_ = lean_ctor_get(v_v_400_, 2);
v_isSharedCheck_446_ = !lean_is_exclusive(v_v_400_);
if (v_isSharedCheck_446_ == 0)
{
v___x_405_ = v_v_400_;
v_isShared_406_ = v_isSharedCheck_446_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_location_x3f_403_);
lean_inc(v_tooltip_x3f_402_);
lean_inc(v_value_401_);
lean_dec(v_v_400_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_446_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v_bs_x27_408_; lean_object* v___y_410_; lean_object* v___y_416_; 
v___x_407_ = lean_unsigned_to_nat(0u);
v_bs_x27_408_ = lean_array_uset(v_bs_398_, v_i_397_, v___x_407_);
if (lean_obj_tag(v_location_x3f_403_) == 0)
{
lean_object* v___x_421_; 
lean_del_object(v___x_405_);
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v_value_401_);
lean_ctor_set(v___x_421_, 1, v_tooltip_x3f_402_);
lean_ctor_set(v___x_421_, 2, v_location_x3f_403_);
v___y_410_ = v___x_421_;
goto v___jp_409_;
}
else
{
lean_object* v_val_422_; lean_object* v_module_423_; lean_object* v_range_424_; uint8_t v___x_425_; 
v_val_422_ = lean_ctor_get(v_location_x3f_403_, 0);
lean_inc(v_val_422_);
lean_dec_ref_known(v_location_x3f_403_, 1);
v_module_423_ = lean_ctor_get(v_val_422_, 0);
v_range_424_ = lean_ctor_get(v_val_422_, 1);
lean_inc_ref(v_range_424_);
v___x_425_ = lean_name_eq(v_module_423_, v_hintMod_393_);
if (v___x_425_ == 0)
{
lean_dec_ref(v_range_424_);
v___y_416_ = v_val_422_;
goto v___jp_415_;
}
else
{
lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_443_; 
lean_inc(v_module_423_);
v_isSharedCheck_443_ = !lean_is_exclusive(v_val_422_);
if (v_isSharedCheck_443_ == 0)
{
lean_object* v_unused_444_; lean_object* v_unused_445_; 
v_unused_444_ = lean_ctor_get(v_val_422_, 1);
lean_dec(v_unused_444_);
v_unused_445_ = lean_ctor_get(v_val_422_, 0);
lean_dec(v_unused_445_);
v___x_427_ = v_val_422_;
v_isShared_428_ = v_isSharedCheck_443_;
goto v_resetjp_426_;
}
else
{
lean_dec(v_val_422_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_443_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_start_429_; lean_object* v_stop_430_; lean_object* v___x_432_; uint8_t v_isShared_433_; uint8_t v_isSharedCheck_442_; 
v_start_429_ = lean_ctor_get(v_range_424_, 0);
v_stop_430_ = lean_ctor_get(v_range_424_, 1);
v_isSharedCheck_442_ = !lean_is_exclusive(v_range_424_);
if (v_isSharedCheck_442_ == 0)
{
v___x_432_ = v_range_424_;
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
else
{
lean_inc(v_stop_430_);
lean_inc(v_start_429_);
lean_dec(v_range_424_);
v___x_432_ = lean_box(0);
v_isShared_433_ = v_isSharedCheck_442_;
goto v_resetjp_431_;
}
v_resetjp_431_:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_437_; 
lean_inc_ref_n(v_range_394_, 2);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_394_, v_byteOffset_395_, v_start_429_);
v___x_435_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_394_, v_byteOffset_395_, v_stop_430_);
if (v_isShared_433_ == 0)
{
lean_ctor_set(v___x_432_, 1, v___x_435_);
lean_ctor_set(v___x_432_, 0, v___x_434_);
v___x_437_ = v___x_432_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_435_);
v___x_437_ = v_reuseFailAlloc_441_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_439_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 1, v___x_437_);
v___x_439_ = v___x_427_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_module_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
v___y_416_ = v___x_439_;
goto v___jp_415_;
}
}
}
}
}
}
v___jp_409_:
{
size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; 
v___x_411_ = ((size_t)1ULL);
v___x_412_ = lean_usize_add(v_i_397_, v___x_411_);
v___x_413_ = lean_array_uset(v_bs_x27_408_, v_i_397_, v___y_410_);
v_i_397_ = v___x_412_;
v_bs_398_ = v___x_413_;
goto _start;
}
v___jp_415_:
{
lean_object* v___x_417_; lean_object* v___x_419_; 
v___x_417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_417_, 0, v___y_416_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 2, v___x_417_);
v___x_419_ = v___x_405_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v_value_401_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_tooltip_x3f_402_);
lean_ctor_set(v_reuseFailAlloc_420_, 2, v___x_417_);
v___x_419_ = v_reuseFailAlloc_420_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
v___y_410_ = v___x_419_;
goto v___jp_409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4___boxed(lean_object* v_hintMod_447_, lean_object* v_range_448_, lean_object* v_byteOffset_449_, lean_object* v_sz_450_, lean_object* v_i_451_, lean_object* v_bs_452_){
_start:
{
size_t v_sz_boxed_453_; size_t v_i_boxed_454_; lean_object* v_res_455_; 
v_sz_boxed_453_ = lean_unbox_usize(v_sz_450_);
lean_dec(v_sz_450_);
v_i_boxed_454_ = lean_unbox_usize(v_i_451_);
lean_dec(v_i_451_);
v_res_455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_447_, v_range_448_, v_byteOffset_449_, v_sz_boxed_453_, v_i_boxed_454_, v_bs_452_);
lean_dec(v_byteOffset_449_);
lean_dec(v_hintMod_447_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(lean_object* v_hintMod_456_, lean_object* v_range_457_, lean_object* v_byteOffset_458_, size_t v_sz_459_, size_t v_i_460_, lean_object* v_bs_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = lean_usize_dec_lt(v_i_460_, v_sz_459_);
if (v___x_462_ == 0)
{
lean_dec_ref(v_range_457_);
return v_bs_461_;
}
else
{
lean_object* v_v_463_; lean_object* v_value_464_; lean_object* v_tooltip_x3f_465_; lean_object* v_location_x3f_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_509_; 
v_v_463_ = lean_array_uget(v_bs_461_, v_i_460_);
v_value_464_ = lean_ctor_get(v_v_463_, 0);
v_tooltip_x3f_465_ = lean_ctor_get(v_v_463_, 1);
v_location_x3f_466_ = lean_ctor_get(v_v_463_, 2);
v_isSharedCheck_509_ = !lean_is_exclusive(v_v_463_);
if (v_isSharedCheck_509_ == 0)
{
v___x_468_ = v_v_463_;
v_isShared_469_ = v_isSharedCheck_509_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_location_x3f_466_);
lean_inc(v_tooltip_x3f_465_);
lean_inc(v_value_464_);
lean_dec(v_v_463_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_509_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v_bs_x27_471_; lean_object* v___y_473_; lean_object* v___y_479_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v_bs_x27_471_ = lean_array_uset(v_bs_461_, v_i_460_, v___x_470_);
if (lean_obj_tag(v_location_x3f_466_) == 0)
{
lean_object* v___x_484_; 
lean_del_object(v___x_468_);
v___x_484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_484_, 0, v_value_464_);
lean_ctor_set(v___x_484_, 1, v_tooltip_x3f_465_);
lean_ctor_set(v___x_484_, 2, v_location_x3f_466_);
v___y_473_ = v___x_484_;
goto v___jp_472_;
}
else
{
lean_object* v_val_485_; lean_object* v_module_486_; lean_object* v_range_487_; uint8_t v___x_488_; 
v_val_485_ = lean_ctor_get(v_location_x3f_466_, 0);
lean_inc(v_val_485_);
lean_dec_ref_known(v_location_x3f_466_, 1);
v_module_486_ = lean_ctor_get(v_val_485_, 0);
v_range_487_ = lean_ctor_get(v_val_485_, 1);
lean_inc_ref(v_range_487_);
v___x_488_ = lean_name_eq(v_module_486_, v_hintMod_456_);
if (v___x_488_ == 0)
{
lean_dec_ref(v_range_487_);
v___y_479_ = v_val_485_;
goto v___jp_478_;
}
else
{
lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_506_; 
lean_inc(v_module_486_);
v_isSharedCheck_506_ = !lean_is_exclusive(v_val_485_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; lean_object* v_unused_508_; 
v_unused_507_ = lean_ctor_get(v_val_485_, 1);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_val_485_, 0);
lean_dec(v_unused_508_);
v___x_490_ = v_val_485_;
v_isShared_491_ = v_isSharedCheck_506_;
goto v_resetjp_489_;
}
else
{
lean_dec(v_val_485_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_506_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v_start_492_; lean_object* v_stop_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_505_; 
v_start_492_ = lean_ctor_get(v_range_487_, 0);
v_stop_493_ = lean_ctor_get(v_range_487_, 1);
v_isSharedCheck_505_ = !lean_is_exclusive(v_range_487_);
if (v_isSharedCheck_505_ == 0)
{
v___x_495_ = v_range_487_;
v_isShared_496_ = v_isSharedCheck_505_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_stop_493_);
lean_inc(v_start_492_);
lean_dec(v_range_487_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_505_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
lean_inc_ref_n(v_range_457_, 2);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_457_, v_byteOffset_458_, v_start_492_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_457_, v_byteOffset_458_, v_stop_493_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 1, v___x_498_);
lean_ctor_set(v___x_495_, 0, v___x_497_);
v___x_500_ = v___x_495_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_504_, 1, v___x_498_);
v___x_500_ = v_reuseFailAlloc_504_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v___x_500_);
v___x_502_ = v___x_490_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_module_486_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
v___y_479_ = v___x_502_;
goto v___jp_478_;
}
}
}
}
}
}
v___jp_472_:
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_460_, v___x_474_);
v___x_476_ = lean_array_uset(v_bs_x27_471_, v_i_460_, v___y_473_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_456_, v_range_457_, v_byteOffset_458_, v_sz_459_, v___x_475_, v___x_476_);
return v___x_477_;
}
v___jp_478_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_480_, 0, v___y_479_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 2, v___x_480_);
v___x_482_ = v___x_468_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_483_; 
v_reuseFailAlloc_483_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_483_, 0, v_value_464_);
lean_ctor_set(v_reuseFailAlloc_483_, 1, v_tooltip_x3f_465_);
lean_ctor_set(v_reuseFailAlloc_483_, 2, v___x_480_);
v___x_482_ = v_reuseFailAlloc_483_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
v___y_473_ = v___x_482_;
goto v___jp_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3___boxed(lean_object* v_hintMod_510_, lean_object* v_range_511_, lean_object* v_byteOffset_512_, lean_object* v_sz_513_, lean_object* v_i_514_, lean_object* v_bs_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_513_);
lean_dec(v_sz_513_);
v_i_boxed_517_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_510_, v_range_511_, v_byteOffset_512_, v_sz_boxed_516_, v_i_boxed_517_, v_bs_515_);
lean_dec(v_byteOffset_512_);
lean_dec(v_hintMod_510_);
return v_res_518_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(lean_object* v_hintMod_519_, lean_object* v_range_520_, lean_object* v_as_521_, size_t v_i_522_, size_t v_stop_523_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_eq(v_i_522_, v_stop_523_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v_location_x3f_526_; uint8_t v___x_527_; uint8_t v___y_529_; 
v___x_525_ = lean_array_uget_borrowed(v_as_521_, v_i_522_);
v_location_x3f_526_ = lean_ctor_get(v___x_525_, 2);
v___x_527_ = 1;
if (lean_obj_tag(v_location_x3f_526_) == 0)
{
v___y_529_ = v___x_524_;
goto v___jp_528_;
}
else
{
lean_object* v_val_533_; lean_object* v_module_534_; lean_object* v_range_535_; uint8_t v___x_536_; 
v_val_533_ = lean_ctor_get(v_location_x3f_526_, 0);
v_module_534_ = lean_ctor_get(v_val_533_, 0);
v_range_535_ = lean_ctor_get(v_val_533_, 1);
v___x_536_ = lean_name_eq(v_module_534_, v_hintMod_519_);
if (v___x_536_ == 0)
{
v___y_529_ = v___x_536_;
goto v___jp_528_;
}
else
{
uint8_t v___x_537_; 
v___x_537_ = l_Lean_Syntax_Range_overlaps(v_range_520_, v_range_535_, v___x_536_, v___x_524_);
v___y_529_ = v___x_537_;
goto v___jp_528_;
}
}
v___jp_528_:
{
if (v___y_529_ == 0)
{
size_t v___x_530_; size_t v___x_531_; 
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_add(v_i_522_, v___x_530_);
v_i_522_ = v___x_531_;
goto _start;
}
else
{
return v___x_527_;
}
}
}
else
{
uint8_t v___x_538_; 
v___x_538_ = 0;
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5___boxed(lean_object* v_hintMod_539_, lean_object* v_range_540_, lean_object* v_as_541_, lean_object* v_i_542_, lean_object* v_stop_543_){
_start:
{
size_t v_i_boxed_544_; size_t v_stop_boxed_545_; uint8_t v_res_546_; lean_object* v_r_547_; 
v_i_boxed_544_ = lean_unbox_usize(v_i_542_);
lean_dec(v_i_542_);
v_stop_boxed_545_ = lean_unbox_usize(v_stop_543_);
lean_dec(v_stop_543_);
v_res_546_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_539_, v_range_540_, v_as_541_, v_i_boxed_544_, v_stop_boxed_545_);
lean_dec_ref(v_as_541_);
lean_dec_ref(v_range_540_);
lean_dec(v_hintMod_539_);
v_r_547_ = lean_box(v_res_546_);
return v_r_547_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(lean_object* v_range_548_, uint8_t v___x_549_, lean_object* v_as_550_, size_t v_i_551_, size_t v_stop_552_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = lean_usize_dec_eq(v_i_551_, v_stop_552_);
if (v___x_553_ == 0)
{
lean_object* v___x_554_; lean_object* v_range_555_; uint8_t v___x_556_; uint8_t v___x_557_; 
v___x_554_ = lean_array_uget_borrowed(v_as_550_, v_i_551_);
v_range_555_ = lean_ctor_get(v___x_554_, 0);
v___x_556_ = 1;
v___x_557_ = l_Lean_Syntax_Range_overlaps(v_range_548_, v_range_555_, v___x_556_, v___x_549_);
if (v___x_557_ == 0)
{
size_t v___x_558_; size_t v___x_559_; 
v___x_558_ = ((size_t)1ULL);
v___x_559_ = lean_usize_add(v_i_551_, v___x_558_);
v_i_551_ = v___x_559_;
goto _start;
}
else
{
return v___x_556_;
}
}
else
{
uint8_t v___x_561_; 
v___x_561_ = 0;
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4___boxed(lean_object* v_range_562_, lean_object* v___x_563_, lean_object* v_as_564_, lean_object* v_i_565_, lean_object* v_stop_566_){
_start:
{
uint8_t v___x_2648__boxed_567_; size_t v_i_boxed_568_; size_t v_stop_boxed_569_; uint8_t v_res_570_; lean_object* v_r_571_; 
v___x_2648__boxed_567_ = lean_unbox(v___x_563_);
v_i_boxed_568_ = lean_unbox_usize(v_i_565_);
lean_dec(v_i_565_);
v_stop_boxed_569_ = lean_unbox_usize(v_stop_566_);
lean_dec(v_stop_566_);
v_res_570_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_562_, v___x_2648__boxed_567_, v_as_564_, v_i_boxed_568_, v_stop_boxed_569_);
lean_dec_ref(v_as_564_);
lean_dec_ref(v_range_562_);
v_r_571_ = lean_box(v_res_570_);
return v_r_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f(lean_object* v_hintMod_572_, lean_object* v_ihi_573_, lean_object* v_range_574_, lean_object* v_newText_575_){
_start:
{
lean_object* v_position_576_; lean_object* v_label_577_; lean_object* v_kind_x3f_578_; lean_object* v_textEdits_579_; lean_object* v_tooltip_x3f_580_; uint8_t v_paddingLeft_581_; uint8_t v_paddingRight_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_663_; 
v_position_576_ = lean_ctor_get(v_ihi_573_, 0);
v_label_577_ = lean_ctor_get(v_ihi_573_, 1);
v_kind_x3f_578_ = lean_ctor_get(v_ihi_573_, 2);
v_textEdits_579_ = lean_ctor_get(v_ihi_573_, 3);
v_tooltip_x3f_580_ = lean_ctor_get(v_ihi_573_, 4);
v_paddingLeft_581_ = lean_ctor_get_uint8(v_ihi_573_, sizeof(void*)*5);
v_paddingRight_582_ = lean_ctor_get_uint8(v_ihi_573_, sizeof(void*)*5 + 1);
v_isSharedCheck_663_ = !lean_is_exclusive(v_ihi_573_);
if (v_isSharedCheck_663_ == 0)
{
v___x_584_ = v_ihi_573_;
v_isShared_585_ = v_isSharedCheck_663_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_tooltip_x3f_580_);
lean_inc(v_textEdits_579_);
lean_inc(v_kind_x3f_578_);
lean_inc(v_label_577_);
lean_inc(v_position_576_);
lean_dec(v_ihi_573_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_663_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___y_587_; lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_598_; lean_object* v___y_599_; uint8_t v___y_612_; uint8_t v___y_613_; uint8_t v___y_646_; 
if (lean_obj_tag(v_label_577_) == 0)
{
uint8_t v___x_655_; 
v___x_655_ = 0;
v___y_646_ = v___x_655_;
goto v___jp_645_;
}
else
{
lean_object* v_p_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v_p_656_ = lean_ctor_get(v_label_577_, 0);
v___x_657_ = lean_unsigned_to_nat(0u);
v___x_658_ = lean_array_get_size(v_p_656_);
v___x_659_ = lean_nat_dec_lt(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
v___y_646_ = v___x_659_;
goto v___jp_645_;
}
else
{
if (v___x_659_ == 0)
{
v___y_646_ = v___x_659_;
goto v___jp_645_;
}
else
{
size_t v___x_660_; size_t v___x_661_; uint8_t v___x_662_; 
v___x_660_ = ((size_t)0ULL);
v___x_661_ = lean_usize_of_nat(v___x_658_);
v___x_662_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_572_, v_range_574_, v_p_656_, v___x_660_, v___x_661_);
v___y_646_ = v___x_662_;
goto v___jp_645_;
}
}
}
v___jp_586_:
{
size_t v_sz_590_; size_t v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v_sz_590_ = lean_array_size(v_textEdits_579_);
v___x_591_ = ((size_t)0ULL);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_574_, v___y_587_, v_sz_590_, v___x_591_, v_textEdits_579_);
lean_dec(v___y_587_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 3, v___x_592_);
lean_ctor_set(v___x_584_, 1, v___y_589_);
lean_ctor_set(v___x_584_, 0, v___y_588_);
v___x_594_ = v___x_584_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___y_588_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___y_589_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_kind_x3f_578_);
lean_ctor_set(v_reuseFailAlloc_596_, 3, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_596_, 4, v_tooltip_x3f_580_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*5, v_paddingLeft_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*5 + 1, v_paddingRight_582_);
v___x_594_ = v_reuseFailAlloc_596_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
return v___x_595_;
}
}
v___jp_597_:
{
if (lean_obj_tag(v_label_577_) == 0)
{
v___y_587_ = v___y_598_;
v___y_588_ = v___y_599_;
v___y_589_ = v_label_577_;
goto v___jp_586_;
}
else
{
lean_object* v_p_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_610_; 
v_p_600_ = lean_ctor_get(v_label_577_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_label_577_);
if (v_isSharedCheck_610_ == 0)
{
v___x_602_ = v_label_577_;
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_p_600_);
lean_dec(v_label_577_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
size_t v_sz_604_; size_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v_sz_604_ = lean_array_size(v_p_600_);
v___x_605_ = ((size_t)0ULL);
lean_inc_ref(v_range_574_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_572_, v_range_574_, v___y_598_, v_sz_604_, v___x_605_, v_p_600_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_606_);
v___x_608_ = v___x_602_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
v___y_587_ = v___y_598_;
v___y_588_ = v___y_599_;
v___y_589_ = v___x_608_;
goto v___jp_586_;
}
}
}
}
v___jp_611_:
{
if (v___y_613_ == 0)
{
if (v___y_612_ == 0)
{
lean_object* v_start_614_; lean_object* v_stop_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_byteOffset_620_; uint8_t v___x_621_; 
v_start_614_ = lean_ctor_get(v_range_574_, 0);
v_stop_615_ = lean_ctor_get(v_range_574_, 1);
v___x_616_ = lean_string_utf8_byte_size(v_newText_575_);
v___x_617_ = lean_nat_to_int(v___x_616_);
v___x_618_ = l_Lean_Syntax_Range_bsize(v_range_574_);
v___x_619_ = lean_nat_to_int(v___x_618_);
v_byteOffset_620_ = lean_int_sub(v___x_617_, v___x_619_);
lean_dec(v___x_619_);
lean_dec(v___x_617_);
v___x_621_ = lean_nat_dec_lt(v_stop_615_, v_position_576_);
if (v___x_621_ == 0)
{
uint8_t v___x_622_; 
v___x_622_ = lean_nat_dec_lt(v_position_576_, v_start_614_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_623_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1));
v___x_625_ = lean_unsigned_to_nat(87u);
v___x_626_ = lean_unsigned_to_nat(6u);
v___x_627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2));
v___x_628_ = l_Nat_reprFast(v_position_576_);
v___x_629_ = lean_string_append(v___x_627_, v___x_628_);
lean_dec_ref(v___x_628_);
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3));
v___x_631_ = lean_string_append(v___x_629_, v___x_630_);
lean_inc(v_start_614_);
v___x_632_ = l_Nat_reprFast(v_start_614_);
v___x_633_ = lean_string_append(v___x_631_, v___x_632_);
lean_dec_ref(v___x_632_);
v___x_634_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4));
v___x_635_ = lean_string_append(v___x_633_, v___x_634_);
lean_inc(v_stop_615_);
v___x_636_ = l_Nat_reprFast(v_stop_615_);
v___x_637_ = lean_string_append(v___x_635_, v___x_636_);
lean_dec_ref(v___x_636_);
v___x_638_ = l_mkPanicMessageWithDecl(v___x_623_, v___x_624_, v___x_625_, v___x_626_, v___x_637_);
lean_dec_ref(v___x_637_);
v___x_639_ = l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(v___x_638_);
v___y_598_ = v_byteOffset_620_;
v___y_599_ = v___x_639_;
goto v___jp_597_;
}
else
{
v___y_598_ = v_byteOffset_620_;
v___y_599_ = v_position_576_;
goto v___jp_597_;
}
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = lean_nat_to_int(v_position_576_);
v___x_641_ = lean_int_add(v___x_640_, v_byteOffset_620_);
lean_dec(v___x_640_);
v___x_642_ = l_Int_toNat(v___x_641_);
lean_dec(v___x_641_);
v___y_598_ = v_byteOffset_620_;
v___y_599_ = v___x_642_;
goto v___jp_597_;
}
}
else
{
lean_object* v___x_643_; 
lean_del_object(v___x_584_);
lean_dec(v_tooltip_x3f_580_);
lean_dec_ref(v_textEdits_579_);
lean_dec(v_kind_x3f_578_);
lean_dec_ref(v_label_577_);
lean_dec(v_position_576_);
lean_dec_ref(v_range_574_);
v___x_643_ = lean_box(0);
return v___x_643_;
}
}
else
{
lean_object* v___x_644_; 
lean_del_object(v___x_584_);
lean_dec(v_tooltip_x3f_580_);
lean_dec_ref(v_textEdits_579_);
lean_dec(v_kind_x3f_578_);
lean_dec_ref(v_label_577_);
lean_dec(v_position_576_);
lean_dec_ref(v_range_574_);
v___x_644_ = lean_box(0);
return v___x_644_;
}
}
v___jp_645_:
{
uint8_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 1;
v___x_648_ = l_Lean_Syntax_Range_contains(v_range_574_, v_position_576_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_array_get_size(v_textEdits_579_);
v___x_651_ = lean_nat_dec_lt(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
v___y_612_ = v___y_646_;
v___y_613_ = v___x_648_;
goto v___jp_611_;
}
else
{
if (v___x_651_ == 0)
{
v___y_612_ = v___y_646_;
v___y_613_ = v___x_648_;
goto v___jp_611_;
}
else
{
size_t v___x_652_; size_t v___x_653_; uint8_t v___x_654_; 
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_650_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_574_, v___x_648_, v_textEdits_579_, v___x_652_, v___x_653_);
v___y_612_ = v___y_646_;
v___y_613_ = v___x_654_;
goto v___jp_611_;
}
}
}
else
{
v___y_612_ = v___y_646_;
v___y_613_ = v___x_648_;
goto v___jp_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___boxed(lean_object* v_hintMod_664_, lean_object* v_ihi_665_, lean_object* v_range_666_, lean_object* v_newText_667_){
_start:
{
lean_object* v_res_668_; 
v_res_668_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(v_hintMod_664_, v_ihi_665_, v_range_666_, v_newText_667_);
lean_dec_ref(v_newText_667_);
lean_dec(v_hintMod_664_);
return v_res_668_;
}
}
static lean_object* _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_698_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_698_, 0, lean_box(0));
lean_closure_set(v___x_698_, 1, lean_box(0));
lean_closure_set(v___x_698_, 2, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(lean_object* v_msg_699_, lean_object* v___y_700_){
_start:
{
lean_object* v___x_702_; lean_object* v___f_703_; lean_object* v___x_17537__overap_704_; lean_object* v___x_705_; 
v___x_702_ = lean_obj_once(&l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0, &l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0_once, _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0);
v___f_703_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_703_, 0, v___x_702_);
v___x_17537__overap_704_ = lean_panic_fn_borrowed(v___f_703_, v_msg_699_);
lean_dec_ref(v___f_703_);
lean_inc_ref(v___y_700_);
v___x_705_ = lean_apply_2(v___x_17537__overap_704_, v___y_700_, lean_box(0));
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___boxed(lean_object* v_msg_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v_msg_706_, v___y_707_);
lean_dec_ref(v___y_707_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(lean_object* v___x_710_, lean_object* v_as_711_, size_t v_i_712_, size_t v_stop_713_, lean_object* v_b_714_){
_start:
{
lean_object* v___y_716_; uint8_t v___x_720_; 
v___x_720_ = lean_usize_dec_eq(v_i_712_, v_stop_713_);
if (v___x_720_ == 0)
{
lean_object* v___x_721_; lean_object* v_position_722_; uint8_t v___x_723_; uint8_t v___x_724_; 
v___x_721_ = lean_array_uget_borrowed(v_as_711_, v_i_712_);
v_position_722_ = lean_ctor_get(v___x_721_, 0);
v___x_723_ = 1;
v___x_724_ = l_Lean_Syntax_Range_contains(v___x_710_, v_position_722_, v___x_723_);
if (v___x_724_ == 0)
{
v___y_716_ = v_b_714_;
goto v___jp_715_;
}
else
{
lean_object* v___x_725_; 
lean_inc(v___x_721_);
v___x_725_ = lean_array_push(v_b_714_, v___x_721_);
v___y_716_ = v___x_725_;
goto v___jp_715_;
}
}
else
{
return v_b_714_;
}
v___jp_715_:
{
size_t v___x_717_; size_t v___x_718_; 
v___x_717_ = ((size_t)1ULL);
v___x_718_ = lean_usize_add(v_i_712_, v___x_717_);
v_i_712_ = v___x_718_;
v_b_714_ = v___y_716_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___boxed(lean_object* v___x_726_, lean_object* v_as_727_, lean_object* v_i_728_, lean_object* v_stop_729_, lean_object* v_b_730_){
_start:
{
size_t v_i_boxed_731_; size_t v_stop_boxed_732_; lean_object* v_res_733_; 
v_i_boxed_731_ = lean_unbox_usize(v_i_728_);
lean_dec(v_i_728_);
v_stop_boxed_732_ = lean_unbox_usize(v_stop_729_);
lean_dec(v_stop_729_);
v_res_733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_726_, v_as_727_, v_i_boxed_731_, v_stop_boxed_732_, v_b_730_);
lean_dec_ref(v_as_727_);
lean_dec_ref(v___x_726_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(uint8_t v___x_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_box(v___x_734_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___y_738_);
v___x_743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed(lean_object* v___x_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
uint8_t v___x_20502__boxed_751_; lean_object* v_res_752_; 
v___x_20502__boxed_751_ = lean_unbox(v___x_744_);
v_res_752_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(v___x_20502__boxed_751_, v_x_745_, v_x_746_, v_x_747_, v___y_748_, v___y_749_);
lean_dec_ref(v___y_749_);
lean_dec_ref(v_x_747_);
lean_dec_ref(v_x_746_);
lean_dec_ref(v_x_745_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(lean_object* v_ci_753_, lean_object* v_i_754_, lean_object* v_x_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
if (lean_obj_tag(v_i_754_) == 10)
{
lean_object* v_i_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_794_; 
v_i_759_ = lean_ctor_get(v_i_754_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_i_754_);
if (v_isSharedCheck_794_ == 0)
{
v___x_761_ = v_i_754_;
v_isShared_762_ = v_isSharedCheck_794_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_i_759_);
lean_dec(v_i_754_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_794_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_Elab_InlayHint_ofCustomInfo_x3f(v_i_759_);
lean_dec_ref(v_i_759_);
if (lean_obj_tag(v___x_763_) == 1)
{
lean_object* v_val_764_; lean_object* v_lctx_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
lean_del_object(v___x_761_);
v_val_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_val_764_);
lean_dec_ref_known(v___x_763_, 1);
v_lctx_765_ = lean_ctor_get(v_val_764_, 1);
lean_inc_ref(v_lctx_765_);
v___x_766_ = lean_alloc_closure((void*)(l_Lean_Elab_InlayHint_resolveDeferred___boxed), 6, 1);
lean_closure_set(v___x_766_, 0, v_val_764_);
v___x_767_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_753_, v_lctx_765_, v___x_766_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_779_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_779_ == 0)
{
v___x_770_ = v___x_767_;
v_isShared_771_ = v_isSharedCheck_779_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_767_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_779_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v_toInlayHintInfo_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
v_toInlayHintInfo_772_ = lean_ctor_get(v_a_768_, 0);
lean_inc_ref(v_toInlayHintInfo_772_);
lean_dec(v_a_768_);
v___x_773_ = lean_box(0);
v___x_774_ = lean_array_push(v___y_756_, v_toInlayHintInfo_772_);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_773_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
if (v_isShared_771_ == 0)
{
lean_ctor_set(v___x_770_, 0, v___x_775_);
v___x_777_ = v___x_770_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v___y_756_);
v_a_780_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v___x_767_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_767_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = l_Lean_Server_RequestError_ofIoError(v_a_780_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_784_);
v___x_786_ = v___x_782_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_792_; 
lean_dec(v___x_763_);
lean_dec_ref(v_ci_753_);
v___x_789_ = lean_box(0);
v___x_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_790_, 0, v___x_789_);
lean_ctor_set(v___x_790_, 1, v___y_756_);
if (v_isShared_762_ == 0)
{
lean_ctor_set_tag(v___x_761_, 0);
lean_ctor_set(v___x_761_, 0, v___x_790_);
v___x_792_ = v___x_761_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_790_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_dec_ref(v_i_754_);
lean_dec_ref(v_ci_753_);
v___x_795_ = lean_box(0);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_795_);
lean_ctor_set(v___x_796_, 1, v___y_756_);
v___x_797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_797_, 0, v___x_796_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed(lean_object* v_ci_798_, lean_object* v_i_799_, lean_object* v_x_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(v_ci_798_, v_i_799_, v_x_800_, v___y_801_, v___y_802_);
lean_dec_ref(v___y_802_);
lean_dec_ref(v_x_800_);
return v_res_804_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l_instMonadEIO(lean_box(0));
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(lean_object* v_msg_806_, lean_object* v___y_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___f_812_; lean_object* v___f_813_; lean_object* v___f_814_; lean_object* v___f_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_19898__overap_824_; lean_object* v___x_825_; 
v___x_810_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_811_ = l_ReaderT_instMonad___redArg(v___x_810_);
lean_inc_ref_n(v___x_811_, 6);
v___f_812_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_812_, 0, v___x_811_);
v___f_813_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_813_, 0, v___x_811_);
v___f_814_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_814_, 0, v___x_811_);
v___f_815_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_815_, 0, v___x_811_);
v___x_816_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_816_, 0, lean_box(0));
lean_closure_set(v___x_816_, 1, lean_box(0));
lean_closure_set(v___x_816_, 2, v___x_811_);
v___x_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_817_, 0, v___x_816_);
lean_ctor_set(v___x_817_, 1, v___f_812_);
v___x_818_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_818_, 0, lean_box(0));
lean_closure_set(v___x_818_, 1, lean_box(0));
lean_closure_set(v___x_818_, 2, v___x_811_);
v___x_819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
lean_ctor_set(v___x_819_, 2, v___f_813_);
lean_ctor_set(v___x_819_, 3, v___f_814_);
lean_ctor_set(v___x_819_, 4, v___f_815_);
v___x_820_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_820_, 0, lean_box(0));
lean_closure_set(v___x_820_, 1, lean_box(0));
lean_closure_set(v___x_820_, 2, v___x_811_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_819_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = lean_box(0);
v___x_823_ = l_instInhabitedOfMonad___redArg(v___x_821_, v___x_822_);
v___x_19898__overap_824_ = lean_panic_fn_borrowed(v___x_823_, v_msg_806_);
lean_dec(v___x_823_);
lean_inc_ref(v___y_808_);
v___x_825_ = lean_apply_3(v___x_19898__overap_824_, v___y_807_, v___y_808_, lean_box(0));
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_826_, v___y_827_, v___y_828_);
lean_dec_ref(v___y_828_);
return v_res_830_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_834_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2));
v___x_835_ = lean_unsigned_to_nat(21u);
v___x_836_ = lean_unsigned_to_nat(65u);
v___x_837_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1));
v___x_838_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0));
v___x_839_ = l_mkPanicMessageWithDecl(v___x_838_, v___x_837_, v___x_836_, v___x_835_, v___x_834_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(lean_object* v_preNode_840_, lean_object* v_postNode_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
switch(lean_obj_tag(v_x_843_))
{
case 0:
{
lean_object* v_i_847_; lean_object* v_t_848_; lean_object* v___x_849_; 
v_i_847_ = lean_ctor_get(v_x_843_, 0);
lean_inc_ref(v_i_847_);
v_t_848_ = lean_ctor_get(v_x_843_, 1);
lean_inc_ref(v_t_848_);
lean_dec_ref_known(v_x_843_, 2);
v___x_849_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_847_, v_x_842_);
v_x_842_ = v___x_849_;
v_x_843_ = v_t_848_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_842_) == 0)
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_dec_ref_known(v_x_843_, 2);
lean_dec_ref(v_postNode_841_);
lean_dec_ref(v_preNode_840_);
v___x_851_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3);
v___x_852_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v___x_851_, v___y_844_, v___y_845_);
return v___x_852_;
}
else
{
lean_object* v_i_853_; lean_object* v_children_854_; lean_object* v_val_855_; lean_object* v___x_856_; 
v_i_853_ = lean_ctor_get(v_x_843_, 0);
lean_inc_ref_n(v_i_853_, 2);
v_children_854_ = lean_ctor_get(v_x_843_, 1);
lean_inc_ref_n(v_children_854_, 2);
lean_dec_ref_known(v_x_843_, 2);
v_val_855_ = lean_ctor_get(v_x_842_, 0);
lean_inc_n(v_val_855_, 2);
lean_inc_ref(v_preNode_840_);
lean_inc_ref(v___y_845_);
v___x_856_ = lean_apply_6(v_preNode_840_, v_val_855_, v_i_853_, v_children_854_, v___y_844_, v___y_845_, lean_box(0));
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v_fst_858_; uint8_t v___x_859_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
v_fst_858_ = lean_ctor_get(v_a_857_, 0);
v___x_859_ = lean_unbox(v_fst_858_);
if (v___x_859_ == 0)
{
lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_894_; 
lean_dec_ref(v_preNode_840_);
v_isSharedCheck_894_ = !lean_is_exclusive(v_x_842_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_x_842_, 0);
lean_dec(v_unused_895_);
v___x_861_ = v_x_842_;
v_isShared_862_ = v_isSharedCheck_894_;
goto v_resetjp_860_;
}
else
{
lean_dec(v_x_842_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_894_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_snd_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v_snd_863_ = lean_ctor_get(v_a_857_, 1);
lean_inc(v_snd_863_);
lean_dec(v_a_857_);
v___x_864_ = lean_box(0);
lean_inc_ref(v___y_845_);
v___x_865_ = lean_apply_7(v_postNode_841_, v_val_855_, v_i_853_, v_children_854_, v___x_864_, v_snd_863_, v___y_845_, lean_box(0));
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_885_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_885_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_885_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_885_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_fst_870_; lean_object* v_snd_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_884_; 
v_fst_870_ = lean_ctor_get(v_a_866_, 0);
v_snd_871_ = lean_ctor_get(v_a_866_, 1);
v_isSharedCheck_884_ = !lean_is_exclusive(v_a_866_);
if (v_isSharedCheck_884_ == 0)
{
v___x_873_ = v_a_866_;
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_snd_871_);
lean_inc(v_fst_870_);
lean_dec(v_a_866_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_884_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v_fst_870_);
v___x_876_ = v___x_861_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_fst_870_);
v___x_876_ = v_reuseFailAlloc_883_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_878_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 0, v___x_876_);
v___x_878_ = v___x_873_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_snd_871_);
v___x_878_ = v_reuseFailAlloc_882_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_880_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_878_);
v___x_880_ = v___x_868_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v___x_878_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_del_object(v___x_861_);
v_a_886_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_865_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_865_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
else
{
lean_object* v_snd_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_snd_896_ = lean_ctor_get(v_a_857_, 1);
lean_inc(v_snd_896_);
lean_dec(v_a_857_);
v___x_897_ = l_Lean_Elab_Info_updateContext_x3f(v_x_842_, v_i_853_);
v___x_898_ = l_Lean_PersistentArray_toList___redArg(v_children_854_);
v___x_899_ = lean_box(0);
lean_inc_ref(v_postNode_841_);
v___x_900_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_840_, v_postNode_841_, v___x_897_, v___x_898_, v___x_899_, v_snd_896_, v___y_845_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; lean_object* v_fst_902_; lean_object* v_snd_903_; lean_object* v___x_904_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v_fst_902_ = lean_ctor_get(v_a_901_, 0);
lean_inc(v_fst_902_);
v_snd_903_ = lean_ctor_get(v_a_901_, 1);
lean_inc(v_snd_903_);
lean_dec(v_a_901_);
lean_inc_ref(v___y_845_);
v___x_904_ = lean_apply_7(v_postNode_841_, v_val_855_, v_i_853_, v_children_854_, v_fst_902_, v_snd_903_, v___y_845_, lean_box(0));
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_922_; 
v_a_905_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_922_ == 0)
{
v___x_907_ = v___x_904_;
v_isShared_908_ = v_isSharedCheck_922_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_922_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_fst_909_; lean_object* v_snd_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_921_; 
v_fst_909_ = lean_ctor_get(v_a_905_, 0);
v_snd_910_ = lean_ctor_get(v_a_905_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_a_905_);
if (v_isSharedCheck_921_ == 0)
{
v___x_912_ = v_a_905_;
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_snd_910_);
lean_inc(v_fst_909_);
lean_dec(v_a_905_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_921_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_914_, 0, v_fst_909_);
if (v_isShared_913_ == 0)
{
lean_ctor_set(v___x_912_, 0, v___x_914_);
v___x_916_ = v___x_912_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_snd_910_);
v___x_916_ = v_reuseFailAlloc_920_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
lean_object* v___x_918_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 0, v___x_916_);
v___x_918_ = v___x_907_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_904_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_904_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v_val_855_);
lean_dec_ref(v_children_854_);
lean_dec_ref(v_i_853_);
lean_dec_ref(v_postNode_841_);
v_a_931_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_900_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_900_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v_val_855_);
lean_dec_ref(v_children_854_);
lean_dec_ref(v_i_853_);
lean_dec_ref_known(v_x_842_, 1);
lean_dec_ref(v_postNode_841_);
lean_dec_ref(v_preNode_840_);
v_a_939_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_856_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_856_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
}
default: 
{
lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_955_; 
lean_dec(v_x_842_);
lean_dec_ref(v_postNode_841_);
lean_dec_ref(v_preNode_840_);
v_isSharedCheck_955_ = !lean_is_exclusive(v_x_843_);
if (v_isSharedCheck_955_ == 0)
{
lean_object* v_unused_956_; 
v_unused_956_ = lean_ctor_get(v_x_843_, 0);
lean_dec(v_unused_956_);
v___x_948_ = v_x_843_;
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
else
{
lean_dec(v_x_843_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_955_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
v___x_950_ = lean_box(0);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___y_844_);
if (v_isShared_949_ == 0)
{
lean_ctor_set_tag(v___x_948_, 0);
lean_ctor_set(v___x_948_, 0, v___x_951_);
v___x_953_ = v___x_948_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(lean_object* v_preNode_957_, lean_object* v_postNode_958_, lean_object* v___x_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
if (lean_obj_tag(v_x_960_) == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v___x_959_);
lean_dec_ref(v_postNode_958_);
lean_dec_ref(v_preNode_957_);
v___x_965_ = l_List_reverse___redArg(v_x_961_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___y_962_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
else
{
lean_object* v_head_968_; lean_object* v_tail_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_989_; 
v_head_968_ = lean_ctor_get(v_x_960_, 0);
v_tail_969_ = lean_ctor_get(v_x_960_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_960_);
if (v_isSharedCheck_989_ == 0)
{
v___x_971_ = v_x_960_;
v_isShared_972_ = v_isSharedCheck_989_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_tail_969_);
lean_inc(v_head_968_);
lean_dec(v_x_960_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_989_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_973_; 
lean_inc(v___x_959_);
lean_inc_ref(v_postNode_958_);
lean_inc_ref(v_preNode_957_);
v___x_973_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_957_, v_postNode_958_, v___x_959_, v_head_968_, v___y_962_, v___y_963_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v_fst_975_; lean_object* v_snd_976_; lean_object* v___x_978_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v_fst_975_ = lean_ctor_get(v_a_974_, 0);
lean_inc(v_fst_975_);
v_snd_976_ = lean_ctor_get(v_a_974_, 1);
lean_inc(v_snd_976_);
lean_dec(v_a_974_);
if (v_isShared_972_ == 0)
{
lean_ctor_set(v___x_971_, 1, v_x_961_);
lean_ctor_set(v___x_971_, 0, v_fst_975_);
v___x_978_ = v___x_971_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_fst_975_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_x_961_);
v___x_978_ = v_reuseFailAlloc_980_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
v_x_960_ = v_tail_969_;
v_x_961_ = v___x_978_;
v___y_962_ = v_snd_976_;
goto _start;
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_del_object(v___x_971_);
lean_dec(v_tail_969_);
lean_dec(v_x_961_);
lean_dec(v___x_959_);
lean_dec_ref(v_postNode_958_);
lean_dec_ref(v_preNode_957_);
v_a_981_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_973_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_973_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_preNode_990_, lean_object* v_postNode_991_, lean_object* v___x_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_990_, v_postNode_991_, v___x_992_, v_x_993_, v_x_994_, v___y_995_, v___y_996_);
lean_dec_ref(v___y_996_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___boxed(lean_object* v_preNode_999_, lean_object* v_postNode_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_999_, v_postNode_1000_, v_x_1001_, v_x_1002_, v___y_1003_, v___y_1004_);
lean_dec_ref(v___y_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(lean_object* v_postNode_1007_, lean_object* v_ci_1008_, lean_object* v_i_1009_, lean_object* v_cs_1010_, lean_object* v_x_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v___x_1015_; 
lean_inc_ref(v___y_1013_);
v___x_1015_ = lean_apply_6(v_postNode_1007_, v_ci_1008_, v_i_1009_, v_cs_1010_, v___y_1012_, v___y_1013_, lean_box(0));
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed(lean_object* v_postNode_1016_, lean_object* v_ci_1017_, lean_object* v_i_1018_, lean_object* v_cs_1019_, lean_object* v_x_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(v_postNode_1016_, v_ci_1017_, v_i_1018_, v_cs_1019_, v_x_1020_, v___y_1021_, v___y_1022_);
lean_dec_ref(v___y_1022_);
lean_dec(v_x_1020_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(lean_object* v_preNode_1025_, lean_object* v_postNode_1026_, lean_object* v_ctx_x3f_1027_, lean_object* v_t_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_){
_start:
{
lean_object* v___f_1032_; lean_object* v___x_1033_; 
v___f_1032_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1032_, 0, v_postNode_1026_);
v___x_1033_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_1025_, v___f_1032_, v_ctx_x3f_1027_, v_t_1028_, v___y_1029_, v___y_1030_);
if (lean_obj_tag(v___x_1033_) == 0)
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1051_; 
v_a_1034_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1036_ = v___x_1033_;
v_isShared_1037_ = v_isSharedCheck_1051_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1033_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1051_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1049_; 
v_snd_1038_ = lean_ctor_get(v_a_1034_, 1);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_a_1034_);
if (v_isSharedCheck_1049_ == 0)
{
lean_object* v_unused_1050_; 
v_unused_1050_ = lean_ctor_get(v_a_1034_, 0);
lean_dec(v_unused_1050_);
v___x_1040_ = v_a_1034_;
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_dec(v_a_1034_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1049_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1042_; lean_object* v___x_1044_; 
v___x_1042_ = lean_box(0);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 0, v___x_1042_);
v___x_1044_ = v___x_1040_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1042_);
lean_ctor_set(v_reuseFailAlloc_1048_, 1, v_snd_1038_);
v___x_1044_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
lean_object* v___x_1046_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 0, v___x_1044_);
v___x_1046_ = v___x_1036_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
v_a_1052_ = lean_ctor_get(v___x_1033_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1033_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1033_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1033_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___boxed(lean_object* v_preNode_1060_, lean_object* v_postNode_1061_, lean_object* v_ctx_x3f_1062_, lean_object* v_t_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v_preNode_1060_, v_postNode_1061_, v_ctx_x3f_1062_, v_t_1063_, v___y_1064_, v___y_1065_);
lean_dec_ref(v___y_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(lean_object* v_a_1069_, lean_object* v_b_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_array_1074_; lean_object* v_start_1075_; lean_object* v_stop_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1099_; 
v_array_1074_ = lean_ctor_get(v_a_1069_, 0);
v_start_1075_ = lean_ctor_get(v_a_1069_, 1);
v_stop_1076_ = lean_ctor_get(v_a_1069_, 2);
v_isSharedCheck_1099_ = !lean_is_exclusive(v_a_1069_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1078_ = v_a_1069_;
v_isShared_1079_ = v_isSharedCheck_1099_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_stop_1076_);
lean_inc(v_start_1075_);
lean_inc(v_array_1074_);
lean_dec(v_a_1069_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1099_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
uint8_t v___x_1080_; 
v___x_1080_ = lean_nat_dec_lt(v_start_1075_, v_stop_1076_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_del_object(v___x_1078_);
lean_dec(v_stop_1076_);
lean_dec(v_start_1075_);
lean_dec_ref(v_array_1074_);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v_b_1070_);
lean_ctor_set(v___x_1081_, 1, v___y_1071_);
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
else
{
lean_object* v___f_1083_; lean_object* v___x_1084_; lean_object* v___f_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___f_1083_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0));
v___x_1084_ = lean_box(v___x_1080_);
v___f_1085_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1085_, 0, v___x_1084_);
v___x_1086_ = lean_array_fget_borrowed(v_array_1074_, v_start_1075_);
v___x_1087_ = lean_box(0);
lean_inc(v___x_1086_);
v___x_1088_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v___x_1086_);
v___x_1089_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v___f_1085_, v___f_1083_, v___x_1087_, v___x_1088_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v_snd_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v_snd_1091_ = lean_ctor_get(v_a_1090_, 1);
lean_inc(v_snd_1091_);
lean_dec(v_a_1090_);
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_start_1075_, v___x_1093_);
lean_dec(v_start_1075_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 1, v___x_1094_);
v___x_1096_ = v___x_1078_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_array_1074_);
lean_ctor_set(v_reuseFailAlloc_1098_, 1, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1098_, 2, v_stop_1076_);
v___x_1096_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
v_a_1069_ = v___x_1096_;
v_b_1070_ = v___x_1092_;
v___y_1071_ = v_snd_1091_;
goto _start;
}
}
else
{
lean_del_object(v___x_1078_);
lean_dec(v_stop_1076_);
lean_dec(v_start_1075_);
lean_dec_ref(v_array_1074_);
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___boxed(lean_object* v_a_1100_, lean_object* v_b_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_1100_, v_b_1101_, v___y_1102_, v___y_1103_);
lean_dec_ref(v___y_1103_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(lean_object* v___x_1106_, uint8_t v_val_1107_, lean_object* v_as_1108_, size_t v_i_1109_, size_t v_stop_1110_, lean_object* v_b_1111_){
_start:
{
lean_object* v___y_1113_; uint8_t v___x_1117_; 
v___x_1117_ = lean_usize_dec_eq(v_i_1109_, v_stop_1110_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v_position_1119_; uint8_t v___x_1120_; 
v___x_1118_ = lean_array_uget_borrowed(v_as_1108_, v_i_1109_);
v_position_1119_ = lean_ctor_get(v___x_1118_, 0);
v___x_1120_ = l_Lean_Syntax_Range_contains(v___x_1106_, v_position_1119_, v_val_1107_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_inc(v___x_1118_);
v___x_1121_ = lean_array_push(v_b_1111_, v___x_1118_);
v___y_1113_ = v___x_1121_;
goto v___jp_1112_;
}
else
{
v___y_1113_ = v_b_1111_;
goto v___jp_1112_;
}
}
else
{
return v_b_1111_;
}
v___jp_1112_:
{
size_t v___x_1114_; size_t v___x_1115_; 
v___x_1114_ = ((size_t)1ULL);
v___x_1115_ = lean_usize_add(v_i_1109_, v___x_1114_);
v_i_1109_ = v___x_1115_;
v_b_1111_ = v___y_1113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5___boxed(lean_object* v___x_1122_, lean_object* v_val_1123_, lean_object* v_as_1124_, lean_object* v_i_1125_, lean_object* v_stop_1126_, lean_object* v_b_1127_){
_start:
{
uint8_t v_val_21129__boxed_1128_; size_t v_i_boxed_1129_; size_t v_stop_boxed_1130_; lean_object* v_res_1131_; 
v_val_21129__boxed_1128_ = lean_unbox(v_val_1123_);
v_i_boxed_1129_ = lean_unbox_usize(v_i_1125_);
lean_dec(v_i_1125_);
v_stop_boxed_1130_ = lean_unbox_usize(v_stop_1126_);
lean_dec(v_stop_1126_);
v_res_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1122_, v_val_21129__boxed_1128_, v_as_1124_, v_i_boxed_1129_, v_stop_boxed_1130_, v_b_1127_);
lean_dec_ref(v_as_1124_);
lean_dec_ref(v___x_1122_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(lean_object* v___x_1132_, size_t v_sz_1133_, size_t v_i_1134_, lean_object* v_bs_1135_){
_start:
{
uint8_t v___x_1137_; 
v___x_1137_ = lean_usize_dec_lt(v_i_1134_, v_sz_1133_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec_ref(v___x_1132_);
v___x_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_bs_1135_);
return v___x_1138_;
}
else
{
lean_object* v_v_1139_; lean_object* v___x_1140_; 
v_v_1139_ = lean_array_uget_borrowed(v_bs_1135_, v_i_1134_);
lean_inc(v_v_1139_);
lean_inc_ref(v___x_1132_);
v___x_1140_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v___x_1132_, v_v_1139_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; lean_object* v_bs_x27_1143_; size_t v___x_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = lean_unsigned_to_nat(0u);
v_bs_x27_1143_ = lean_array_uset(v_bs_1135_, v_i_1134_, v___x_1142_);
v___x_1144_ = ((size_t)1ULL);
v___x_1145_ = lean_usize_add(v_i_1134_, v___x_1144_);
v___x_1146_ = lean_array_uset(v_bs_x27_1143_, v_i_1134_, v_a_1141_);
v_i_1134_ = v___x_1145_;
v_bs_1135_ = v___x_1146_;
goto _start;
}
else
{
lean_object* v_a_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1156_; 
lean_dec_ref(v_bs_1135_);
lean_dec_ref(v___x_1132_);
v_a_1148_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1150_ = v___x_1140_;
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_a_1148_);
lean_dec(v___x_1140_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1156_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
v___x_1152_ = l_Lean_Server_RequestError_ofIoError(v_a_1148_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v___x_1152_);
v___x_1154_ = v___x_1150_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg___boxed(lean_object* v___x_1157_, lean_object* v_sz_1158_, lean_object* v_i_1159_, lean_object* v_bs_1160_, lean_object* v___y_1161_){
_start:
{
size_t v_sz_boxed_1162_; size_t v_i_boxed_1163_; lean_object* v_res_1164_; 
v_sz_boxed_1162_ = lean_unbox_usize(v_sz_1158_);
lean_dec(v_sz_1158_);
v_i_boxed_1163_ = lean_unbox_usize(v_i_1159_);
lean_dec(v_i_1159_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_1157_, v_sz_boxed_1162_, v_i_boxed_1163_, v_bs_1160_);
return v_res_1164_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2(void){
_start:
{
lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
v___x_1167_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__1));
v___x_1168_ = lean_unsigned_to_nat(2u);
v___x_1169_ = lean_unsigned_to_nat(162u);
v___x_1170_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__0));
v___x_1171_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_1172_ = l_mkPanicMessageWithDecl(v___x_1171_, v___x_1170_, v___x_1169_, v___x_1168_, v___x_1167_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints(lean_object* v_p_1173_, lean_object* v_s_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v_doc_1177_; lean_object* v_toEditableDocumentCore_1178_; lean_object* v_meta_1179_; lean_object* v_cancelTk_1180_; lean_object* v_cmdSnaps_1181_; lean_object* v_text_1182_; lean_object* v_oldInlayHints_1183_; lean_object* v_oldFinishedSnaps_1184_; lean_object* v_lastEditTimestamp_x3f_1185_; uint8_t v_isFirstRequestAfterEdit_1186_; uint8_t v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; 
v_doc_1177_ = lean_ctor_get(v_a_1175_, 1);
v_toEditableDocumentCore_1178_ = lean_ctor_get(v_doc_1177_, 0);
v_meta_1179_ = lean_ctor_get(v_toEditableDocumentCore_1178_, 0);
v_cancelTk_1180_ = lean_ctor_get(v_a_1175_, 4);
v_cmdSnaps_1181_ = lean_ctor_get(v_toEditableDocumentCore_1178_, 2);
v_text_1182_ = lean_ctor_get(v_meta_1179_, 3);
v_oldInlayHints_1183_ = lean_ctor_get(v_s_1174_, 0);
v_oldFinishedSnaps_1184_ = lean_ctor_get(v_s_1174_, 1);
v_lastEditTimestamp_x3f_1185_ = lean_ctor_get(v_s_1174_, 2);
v_isFirstRequestAfterEdit_1186_ = lean_ctor_get_uint8(v_s_1174_, sizeof(void*)*3);
if (v_isFirstRequestAfterEdit_1186_ == 0)
{
lean_object* v___x_1214_; lean_object* v_range_1215_; lean_object* v___x_1216_; lean_object* v___y_1218_; lean_object* v___y_1219_; uint8_t v___y_1220_; lean_object* v___y_1221_; lean_object* v_snd_1222_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; uint8_t v___y_1238_; lean_object* v___y_1239_; lean_object* v_lower_1240_; lean_object* v_upper_1241_; lean_object* v___y_1259_; lean_object* v___y_1260_; uint8_t v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1266_; uint8_t v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; uint8_t v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1285_; uint8_t v___y_1286_; uint8_t v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1297_; 
v___x_1214_ = lean_io_mono_ms_now();
v_range_1215_ = lean_ctor_get(v_p_1173_, 2);
lean_inc_ref(v_range_1215_);
lean_dec_ref(v_p_1173_);
v___x_1216_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_1182_, v_range_1215_);
if (lean_obj_tag(v_lastEditTimestamp_x3f_1185_) == 0)
{
lean_object* v___x_1346_; 
lean_dec(v___x_1214_);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___y_1297_ = v___x_1346_;
goto v___jp_1296_;
}
else
{
lean_object* v_val_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v_val_1347_ = lean_ctor_get(v_lastEditTimestamp_x3f_1185_, 0);
v___x_1348_ = lean_unsigned_to_nat(3000u);
v___x_1349_ = lean_nat_sub(v___x_1214_, v_val_1347_);
lean_dec(v___x_1214_);
v___x_1350_ = lean_nat_sub(v___x_1348_, v___x_1349_);
lean_dec(v___x_1349_);
v___y_1297_ = v___x_1350_;
goto v___jp_1296_;
}
v___jp_1217_:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1223_ = l_Array_append___redArg(v_snd_1222_, v___y_1218_);
lean_dec_ref(v___y_1218_);
v___x_1224_ = lean_array_get_size(v___x_1223_);
v___x_1225_ = lean_mk_empty_array_with_capacity(v___y_1219_);
v___x_1226_ = lean_nat_dec_lt(v___y_1219_, v___x_1224_);
lean_dec(v___y_1219_);
if (v___x_1226_ == 0)
{
lean_dec_ref(v___x_1216_);
v___y_1188_ = v___y_1220_;
v___y_1189_ = v___x_1223_;
v___y_1190_ = v___y_1221_;
v___y_1191_ = v___x_1225_;
goto v___jp_1187_;
}
else
{
uint8_t v___x_1227_; 
v___x_1227_ = lean_nat_dec_le(v___x_1224_, v___x_1224_);
if (v___x_1227_ == 0)
{
if (v___x_1226_ == 0)
{
lean_dec_ref(v___x_1216_);
v___y_1188_ = v___y_1220_;
v___y_1189_ = v___x_1223_;
v___y_1190_ = v___y_1221_;
v___y_1191_ = v___x_1225_;
goto v___jp_1187_;
}
else
{
size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v___x_1228_ = ((size_t)0ULL);
v___x_1229_ = lean_usize_of_nat(v___x_1224_);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1216_, v___x_1223_, v___x_1228_, v___x_1229_, v___x_1225_);
lean_dec_ref(v___x_1216_);
v___y_1188_ = v___y_1220_;
v___y_1189_ = v___x_1223_;
v___y_1190_ = v___y_1221_;
v___y_1191_ = v___x_1230_;
goto v___jp_1187_;
}
}
else
{
size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; 
v___x_1231_ = ((size_t)0ULL);
v___x_1232_ = lean_usize_of_nat(v___x_1224_);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1216_, v___x_1223_, v___x_1231_, v___x_1232_, v___x_1225_);
lean_dec_ref(v___x_1216_);
v___y_1188_ = v___y_1220_;
v___y_1189_ = v___x_1223_;
v___y_1190_ = v___y_1221_;
v___y_1191_ = v___x_1233_;
goto v___jp_1187_;
}
}
}
v___jp_1234_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = l_Array_toSubarray___redArg(v___y_1235_, v_lower_1240_, v_upper_1241_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_mk_empty_array_with_capacity(v___y_1236_);
v___x_1245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v___x_1242_, v___x_1243_, v___x_1244_, v_a_1175_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; lean_object* v_snd_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v_snd_1247_ = lean_ctor_get(v_a_1246_, 1);
lean_inc(v_snd_1247_);
lean_dec(v_a_1246_);
v___y_1218_ = v___y_1237_;
v___y_1219_ = v___y_1236_;
v___y_1220_ = v___y_1238_;
v___y_1221_ = v___y_1239_;
v_snd_1222_ = v_snd_1247_;
goto v___jp_1217_;
}
else
{
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1248_; lean_object* v_snd_1249_; 
v_a_1248_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1248_);
lean_dec_ref_known(v___x_1245_, 1);
v_snd_1249_ = lean_ctor_get(v_a_1248_, 1);
lean_inc(v_snd_1249_);
lean_dec(v_a_1248_);
v___y_1218_ = v___y_1237_;
v___y_1219_ = v___y_1236_;
v___y_1220_ = v___y_1238_;
v___y_1221_ = v___y_1239_;
v_snd_1222_ = v_snd_1249_;
goto v___jp_1217_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___x_1216_);
lean_dec(v_lastEditTimestamp_x3f_1185_);
v_a_1250_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1245_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1245_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
v___jp_1258_:
{
uint8_t v___x_1264_; 
v___x_1264_ = lean_nat_dec_le(v_oldFinishedSnaps_1184_, v___y_1260_);
if (v___x_1264_ == 0)
{
lean_inc(v___y_1262_);
v___y_1235_ = v___y_1259_;
v___y_1236_ = v___y_1260_;
v___y_1237_ = v___y_1263_;
v___y_1238_ = v___y_1261_;
v___y_1239_ = v___y_1262_;
v_lower_1240_ = v_oldFinishedSnaps_1184_;
v_upper_1241_ = v___y_1262_;
goto v___jp_1234_;
}
else
{
lean_dec(v_oldFinishedSnaps_1184_);
lean_inc(v___y_1262_);
lean_inc(v___y_1260_);
v___y_1235_ = v___y_1259_;
v___y_1236_ = v___y_1260_;
v___y_1237_ = v___y_1263_;
v___y_1238_ = v___y_1261_;
v___y_1239_ = v___y_1262_;
v_lower_1240_ = v___y_1260_;
v_upper_1241_ = v___y_1262_;
goto v___jp_1234_;
}
}
v___jp_1265_:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v___x_1272_ = lean_unsigned_to_nat(0u);
v___x_1273_ = lean_array_get_size(v_oldInlayHints_1183_);
v___x_1274_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init___closed__0));
v___x_1275_ = lean_nat_dec_lt(v___x_1272_, v___x_1273_);
if (v___x_1275_ == 0)
{
lean_dec(v___y_1271_);
lean_dec(v___y_1268_);
lean_dec_ref(v_oldInlayHints_1183_);
v___y_1259_ = v___y_1266_;
v___y_1260_ = v___x_1272_;
v___y_1261_ = v___y_1267_;
v___y_1262_ = v___y_1269_;
v___y_1263_ = v___x_1274_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___y_1268_);
lean_ctor_set(v___x_1276_, 1, v___y_1271_);
v___x_1277_ = lean_nat_dec_le(v___x_1273_, v___x_1273_);
if (v___x_1277_ == 0)
{
if (v___x_1275_ == 0)
{
lean_dec_ref_known(v___x_1276_, 2);
lean_dec_ref(v_oldInlayHints_1183_);
v___y_1259_ = v___y_1266_;
v___y_1260_ = v___x_1272_;
v___y_1261_ = v___y_1267_;
v___y_1262_ = v___y_1269_;
v___y_1263_ = v___x_1274_;
goto v___jp_1258_;
}
else
{
size_t v___x_1278_; size_t v___x_1279_; lean_object* v___x_1280_; 
v___x_1278_ = ((size_t)0ULL);
v___x_1279_ = lean_usize_of_nat(v___x_1273_);
v___x_1280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1276_, v___y_1270_, v_oldInlayHints_1183_, v___x_1278_, v___x_1279_, v___x_1274_);
lean_dec_ref(v_oldInlayHints_1183_);
lean_dec_ref_known(v___x_1276_, 2);
v___y_1259_ = v___y_1266_;
v___y_1260_ = v___x_1272_;
v___y_1261_ = v___y_1267_;
v___y_1262_ = v___y_1269_;
v___y_1263_ = v___x_1280_;
goto v___jp_1258_;
}
}
else
{
size_t v___x_1281_; size_t v___x_1282_; lean_object* v___x_1283_; 
v___x_1281_ = ((size_t)0ULL);
v___x_1282_ = lean_usize_of_nat(v___x_1273_);
v___x_1283_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1276_, v___y_1270_, v_oldInlayHints_1183_, v___x_1281_, v___x_1282_, v___x_1274_);
lean_dec_ref(v_oldInlayHints_1183_);
lean_dec_ref_known(v___x_1276_, 2);
v___y_1259_ = v___y_1266_;
v___y_1260_ = v___x_1272_;
v___y_1261_ = v___y_1267_;
v___y_1262_ = v___y_1269_;
v___y_1263_ = v___x_1283_;
goto v___jp_1258_;
}
}
}
v___jp_1284_:
{
lean_object* v___x_1291_; uint8_t v___x_1292_; 
v___x_1291_ = lean_nat_sub(v___y_1288_, v___y_1289_);
v___x_1292_ = lean_nat_dec_lt(v___x_1291_, v___y_1288_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
lean_dec(v___x_1291_);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___y_1266_ = v___y_1285_;
v___y_1267_ = v___y_1286_;
v___y_1268_ = v___y_1290_;
v___y_1269_ = v___y_1288_;
v___y_1270_ = v___y_1287_;
v___y_1271_ = v___x_1293_;
goto v___jp_1265_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_array_fget_borrowed(v___y_1285_, v___x_1291_);
lean_dec(v___x_1291_);
v___x_1295_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1294_);
v___y_1266_ = v___y_1285_;
v___y_1267_ = v___y_1286_;
v___y_1268_ = v___y_1290_;
v___y_1269_ = v___y_1288_;
v___y_1270_ = v___y_1287_;
v___y_1271_ = v___x_1295_;
goto v___jp_1265_;
}
}
v___jp_1296_:
{
uint32_t v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v_snd_1301_; lean_object* v_fst_1302_; lean_object* v_snd_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1344_; 
v___x_1298_ = lean_uint32_of_nat(v___y_1297_);
lean_dec(v___y_1297_);
v___x_1299_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_1180_);
lean_inc(v_cmdSnaps_1181_);
v___x_1300_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_cmdSnaps_1181_, v___x_1298_, v___x_1299_);
v_snd_1301_ = lean_ctor_get(v___x_1300_, 1);
lean_inc(v_snd_1301_);
v_fst_1302_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_fst_1302_);
lean_dec_ref(v___x_1300_);
v_snd_1303_ = lean_ctor_get(v_snd_1301_, 1);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_snd_1301_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v_snd_1301_, 0);
lean_dec(v_unused_1345_);
v___x_1305_ = v_snd_1301_;
v_isShared_1306_ = v_isSharedCheck_1344_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_snd_1303_);
lean_dec(v_snd_1301_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1344_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
uint8_t v___x_1307_; 
v___x_1307_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_cancelTk_1180_);
if (v___x_1307_ == 0)
{
lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
lean_inc(v_lastEditTimestamp_x3f_1185_);
lean_inc(v_oldFinishedSnaps_1184_);
lean_inc_ref(v_oldInlayHints_1183_);
lean_del_object(v___x_1305_);
lean_dec_ref(v_s_1174_);
v___x_1308_ = lean_array_mk(v_fst_1302_);
v___x_1309_ = lean_array_get_size(v___x_1308_);
v___x_1310_ = lean_nat_dec_le(v_oldFinishedSnaps_1184_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
lean_dec_ref(v___x_1308_);
lean_dec(v_snd_1303_);
lean_dec_ref(v___x_1216_);
lean_dec(v_lastEditTimestamp_x3f_1185_);
lean_dec(v_oldFinishedSnaps_1184_);
lean_dec_ref(v_oldInlayHints_1183_);
v___x_1311_ = lean_obj_once(&l_Lean_Server_FileWorker_handleInlayHints___closed__2, &l_Lean_Server_FileWorker_handleInlayHints___closed__2_once, _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2);
v___x_1312_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v___x_1311_, v_a_1175_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = lean_nat_sub(v_oldFinishedSnaps_1184_, v___x_1313_);
v___x_1315_ = lean_nat_dec_lt(v___x_1314_, v___x_1309_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; uint8_t v___x_1317_; 
lean_dec(v___x_1314_);
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_unbox(v_snd_1303_);
lean_dec(v_snd_1303_);
v___y_1285_ = v___x_1308_;
v___y_1286_ = v___x_1317_;
v___y_1287_ = v___x_1307_;
v___y_1288_ = v___x_1309_;
v___y_1289_ = v___x_1313_;
v___y_1290_ = v___x_1316_;
goto v___jp_1284_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1318_ = lean_array_fget(v___x_1308_, v___x_1314_);
lean_dec(v___x_1314_);
v___x_1319_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1318_);
lean_dec(v___x_1318_);
v___x_1320_ = lean_unbox(v_snd_1303_);
lean_dec(v_snd_1303_);
v___y_1285_ = v___x_1308_;
v___y_1286_ = v___x_1320_;
v___y_1287_ = v___x_1307_;
v___y_1288_ = v___x_1309_;
v___y_1289_ = v___x_1313_;
v___y_1290_ = v___x_1319_;
goto v___jp_1284_;
}
}
}
else
{
size_t v_sz_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v_snd_1303_);
lean_dec(v_fst_1302_);
lean_dec_ref(v___x_1216_);
v_sz_1321_ = lean_array_size(v_oldInlayHints_1183_);
v___x_1322_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1183_);
lean_inc_ref(v_text_1182_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1182_, v_sz_1321_, v___x_1322_, v_oldInlayHints_1183_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1335_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1335_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1335_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1328_, 0, v_a_1324_);
lean_ctor_set_uint8(v___x_1328_, sizeof(void*)*1, v_isFirstRequestAfterEdit_1186_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 1, v_s_1174_);
lean_ctor_set(v___x_1305_, 0, v___x_1328_);
v___x_1330_ = v___x_1305_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_s_1174_);
v___x_1330_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1332_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1330_);
v___x_1332_ = v___x_1326_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1330_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_del_object(v___x_1305_);
lean_dec_ref(v_s_1174_);
v_a_1336_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1323_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1323_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1379_; 
lean_inc(v_lastEditTimestamp_x3f_1185_);
lean_inc(v_oldFinishedSnaps_1184_);
lean_inc_ref(v_oldInlayHints_1183_);
lean_dec_ref(v_p_1173_);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_s_1174_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; lean_object* v_unused_1381_; lean_object* v_unused_1382_; 
v_unused_1380_ = lean_ctor_get(v_s_1174_, 2);
lean_dec(v_unused_1380_);
v_unused_1381_ = lean_ctor_get(v_s_1174_, 1);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_s_1174_, 0);
lean_dec(v_unused_1382_);
v___x_1352_ = v_s_1174_;
v_isShared_1353_ = v_isSharedCheck_1379_;
goto v_resetjp_1351_;
}
else
{
lean_dec(v_s_1174_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1379_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
size_t v_sz_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v_sz_1354_ = lean_array_size(v_oldInlayHints_1183_);
v___x_1355_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1183_);
lean_inc_ref(v_text_1182_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1182_, v_sz_1354_, v___x_1355_, v_oldInlayHints_1183_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1370_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1370_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1370_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
uint8_t v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1361_ = 0;
v___x_1362_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1362_, 0, v_a_1357_);
lean_ctor_set_uint8(v___x_1362_, sizeof(void*)*1, v___x_1361_);
if (v_isShared_1353_ == 0)
{
v___x_1364_ = v___x_1352_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_oldInlayHints_1183_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_oldFinishedSnaps_1184_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_lastEditTimestamp_x3f_1185_);
v___x_1364_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
lean_ctor_set_uint8(v___x_1364_, sizeof(void*)*3, v___x_1361_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1362_);
lean_ctor_set(v___x_1365_, 1, v___x_1364_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1365_);
v___x_1367_ = v___x_1359_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_del_object(v___x_1352_);
lean_dec(v_lastEditTimestamp_x3f_1185_);
lean_dec(v_oldFinishedSnaps_1184_);
lean_dec_ref(v_oldInlayHints_1183_);
v_a_1371_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1356_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1356_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
v___jp_1187_:
{
size_t v_sz_1192_; size_t v___x_1193_; lean_object* v___x_1194_; 
v_sz_1192_ = lean_array_size(v___y_1191_);
v___x_1193_ = ((size_t)0ULL);
lean_inc_ref(v_text_1182_);
v___x_1194_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1182_, v_sz_1192_, v___x_1193_, v___y_1191_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1205_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1197_ = v___x_1194_;
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_a_1195_);
lean_dec(v___x_1194_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1205_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
v___x_1199_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1199_, 0, v_a_1195_);
lean_ctor_set_uint8(v___x_1199_, sizeof(void*)*1, v___y_1188_);
v___x_1200_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1200_, 0, v___y_1189_);
lean_ctor_set(v___x_1200_, 1, v___y_1190_);
lean_ctor_set(v___x_1200_, 2, v_lastEditTimestamp_x3f_1185_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*3, v_isFirstRequestAfterEdit_1186_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___x_1199_);
lean_ctor_set(v___x_1201_, 1, v___x_1200_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1201_);
v___x_1203_ = v___x_1197_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1201_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v_lastEditTimestamp_x3f_1185_);
v_a_1206_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1194_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1194_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints___boxed(lean_object* v_p_1383_, lean_object* v_s_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lean_Server_FileWorker_handleInlayHints(v_p_1383_, v_s_1384_, v_a_1385_);
lean_dec_ref(v_a_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(lean_object* v___x_1388_, size_t v_sz_1389_, size_t v_i_1390_, lean_object* v_bs_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_1388_, v_sz_1389_, v_i_1390_, v_bs_1391_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___boxed(lean_object* v___x_1395_, lean_object* v_sz_1396_, lean_object* v_i_1397_, lean_object* v_bs_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
size_t v_sz_boxed_1401_; size_t v_i_boxed_1402_; lean_object* v_res_1403_; 
v_sz_boxed_1401_ = lean_unbox_usize(v_sz_1396_);
lean_dec(v_sz_1396_);
v_i_boxed_1402_ = lean_unbox_usize(v_i_1397_);
lean_dec(v_i_1397_);
v_res_1403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(v___x_1395_, v_sz_boxed_1401_, v_i_boxed_1402_, v_bs_1398_, v___y_1399_);
lean_dec_ref(v___y_1399_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(lean_object* v_inst_1404_, lean_object* v_R_1405_, lean_object* v_a_1406_, lean_object* v_b_1407_, lean_object* v_c_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_1406_, v_b_1407_, v___y_1409_, v___y_1410_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___boxed(lean_object* v_inst_1413_, lean_object* v_R_1414_, lean_object* v_a_1415_, lean_object* v_b_1416_, lean_object* v_c_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(v_inst_1413_, v_R_1414_, v_a_1415_, v_b_1416_, v_c_1417_, v___y_1418_, v___y_1419_);
lean_dec_ref(v___y_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_1422_, lean_object* v_msg_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_1423_, v___y_1424_, v___y_1425_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1428_, lean_object* v_msg_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(v_00_u03b1_1428_, v_msg_1429_, v___y_1430_, v___y_1431_);
lean_dec_ref(v___y_1431_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(lean_object* v_00_u03b1_1434_, lean_object* v_preNode_1435_, lean_object* v_postNode_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_1435_, v_postNode_1436_, v_x_1437_, v_x_1438_, v___y_1439_, v___y_1440_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1443_, lean_object* v_preNode_1444_, lean_object* v_postNode_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(v_00_u03b1_1443_, v_preNode_1444_, v_postNode_1445_, v_x_1446_, v_x_1447_, v___y_1448_, v___y_1449_);
lean_dec_ref(v___y_1449_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(lean_object* v_00_u03b1_1452_, lean_object* v_preNode_1453_, lean_object* v_postNode_1454_, lean_object* v___x_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_1453_, v_postNode_1454_, v___x_1455_, v_x_1456_, v_x_1457_, v___y_1458_, v___y_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1462_, lean_object* v_preNode_1463_, lean_object* v_postNode_1464_, lean_object* v___x_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(v_00_u03b1_1462_, v_preNode_1463_, v_postNode_1464_, v___x_1465_, v_x_1466_, v_x_1467_, v___y_1468_, v___y_1469_);
lean_dec_ref(v___y_1469_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(lean_object* v___x_1474_, lean_object* v___x_1475_, lean_object* v_as_1476_, size_t v_sz_1477_, size_t v_i_1478_, lean_object* v_b_1479_){
_start:
{
uint8_t v___x_1481_; 
v___x_1481_ = lean_usize_dec_lt(v_i_1478_, v_sz_1477_);
if (v___x_1481_ == 0)
{
lean_object* v___x_1482_; 
v___x_1482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1482_, 0, v_b_1479_);
return v___x_1482_;
}
else
{
lean_object* v_snd_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1526_; 
v_snd_1483_ = lean_ctor_get(v_b_1479_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_b_1479_);
if (v_isSharedCheck_1526_ == 0)
{
lean_object* v_unused_1527_; 
v_unused_1527_ = lean_ctor_get(v_b_1479_, 0);
lean_dec(v_unused_1527_);
v___x_1485_ = v_b_1479_;
v_isShared_1486_ = v_isSharedCheck_1526_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_snd_1483_);
lean_dec(v_b_1479_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1526_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v_fst_1487_; lean_object* v_snd_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1525_; 
v_fst_1487_ = lean_ctor_get(v_snd_1483_, 0);
v_snd_1488_ = lean_ctor_get(v_snd_1483_, 1);
v_isSharedCheck_1525_ = !lean_is_exclusive(v_snd_1483_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1490_ = v_snd_1483_;
v_isShared_1491_ = v_isSharedCheck_1525_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_snd_1488_);
lean_inc(v_fst_1487_);
lean_dec(v_snd_1483_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1525_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v_a_1492_; 
v_a_1492_ = lean_array_uget_borrowed(v_as_1476_, v_i_1478_);
if (lean_obj_tag(v_a_1492_) == 0)
{
lean_object* v_range_1493_; lean_object* v_text_1494_; lean_object* v_mod_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; 
v_range_1493_ = lean_ctor_get(v_a_1492_, 0);
v_text_1494_ = lean_ctor_get(v_a_1492_, 1);
v_mod_1495_ = lean_ctor_get(v___x_1475_, 1);
v___x_1496_ = lean_box(0);
lean_inc_ref(v_range_1493_);
v___x_1497_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1474_, v_range_1493_);
lean_inc(v_fst_1487_);
v___x_1498_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(v_mod_1495_, v_fst_1487_, v___x_1497_, v_text_1494_);
if (lean_obj_tag(v___x_1498_) == 1)
{
lean_object* v_val_1499_; lean_object* v___x_1501_; 
lean_dec(v_fst_1487_);
v_val_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_val_1499_);
lean_dec_ref_known(v___x_1498_, 1);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 0, v_val_1499_);
v___x_1501_ = v___x_1490_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_val_1499_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_snd_1488_);
v___x_1501_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1503_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1501_);
lean_ctor_set(v___x_1485_, 0, v___x_1496_);
v___x_1503_ = v___x_1485_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1507_; 
v_reuseFailAlloc_1507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1507_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1507_, 1, v___x_1501_);
v___x_1503_ = v_reuseFailAlloc_1507_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
size_t v___x_1504_; size_t v___x_1505_; 
v___x_1504_ = ((size_t)1ULL);
v___x_1505_ = lean_usize_add(v_i_1478_, v___x_1504_);
v_i_1478_ = v___x_1505_;
v_b_1479_ = v___x_1503_;
goto _start;
}
}
}
else
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
lean_dec(v___x_1498_);
lean_dec(v_snd_1488_);
v___x_1509_ = lean_box(v___x_1481_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1509_);
v___x_1511_ = v___x_1490_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_fst_1487_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1509_);
v___x_1511_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
lean_object* v___x_1513_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1511_);
lean_ctor_set(v___x_1485_, 0, v___x_1496_);
v___x_1513_ = v___x_1485_;
goto v_reusejp_1512_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v___x_1496_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v___x_1511_);
v___x_1513_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1512_;
}
v_reusejp_1512_:
{
lean_object* v___x_1514_; 
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
}
}
else
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0));
if (v_isShared_1491_ == 0)
{
v___x_1519_ = v___x_1490_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_fst_1487_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_snd_1488_);
v___x_1519_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1521_; 
if (v_isShared_1486_ == 0)
{
lean_ctor_set(v___x_1485_, 1, v___x_1519_);
lean_ctor_set(v___x_1485_, 0, v___x_1517_);
v___x_1521_ = v___x_1485_;
goto v_reusejp_1520_;
}
else
{
lean_object* v_reuseFailAlloc_1523_; 
v_reuseFailAlloc_1523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1523_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1523_, 1, v___x_1519_);
v___x_1521_ = v_reuseFailAlloc_1523_;
goto v_reusejp_1520_;
}
v_reusejp_1520_:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___boxed(lean_object* v___x_1528_, lean_object* v___x_1529_, lean_object* v_as_1530_, lean_object* v_sz_1531_, lean_object* v_i_1532_, lean_object* v_b_1533_, lean_object* v___y_1534_){
_start:
{
size_t v_sz_boxed_1535_; size_t v_i_boxed_1536_; lean_object* v_res_1537_; 
v_sz_boxed_1535_ = lean_unbox_usize(v_sz_1531_);
lean_dec(v_sz_1531_);
v_i_boxed_1536_ = lean_unbox_usize(v_i_1532_);
lean_dec(v_i_1532_);
v_res_1537_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1528_, v___x_1529_, v_as_1530_, v_sz_boxed_1535_, v_i_boxed_1536_, v_b_1533_);
lean_dec_ref(v_as_1530_);
lean_dec_ref(v___x_1529_);
lean_dec_ref(v___x_1528_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(lean_object* v_p_1538_, lean_object* v___x_1539_, lean_object* v___x_1540_, lean_object* v_as_1541_, size_t v_sz_1542_, size_t v_i_1543_, lean_object* v_b_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_a_1548_; uint8_t v___x_1552_; 
v___x_1552_ = lean_usize_dec_lt(v_i_1543_, v_sz_1542_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
v___x_1553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_b_1544_);
return v___x_1553_;
}
else
{
lean_object* v_contentChanges_1554_; lean_object* v___x_1555_; lean_object* v_a_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; size_t v_sz_1561_; size_t v___x_1562_; lean_object* v___x_1563_; 
v_contentChanges_1554_ = lean_ctor_get(v_p_1538_, 1);
v___x_1555_ = lean_box(0);
v_a_1556_ = lean_array_uget_borrowed(v_as_1541_, v_i_1543_);
v___x_1557_ = 0;
v___x_1558_ = lean_box(v___x_1557_);
lean_inc(v_a_1556_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_a_1556_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1555_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v_sz_1561_ = lean_array_size(v_contentChanges_1554_);
v___x_1562_ = ((size_t)0ULL);
v___x_1563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1539_, v___x_1540_, v_contentChanges_1554_, v_sz_1561_, v___x_1562_, v___x_1560_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1606_; 
v_a_1564_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1566_ = v___x_1563_;
v_isShared_1567_ = v_isSharedCheck_1606_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1563_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1606_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v_fst_1568_; 
v_fst_1568_ = lean_ctor_get(v_a_1564_, 0);
if (lean_obj_tag(v_fst_1568_) == 0)
{
lean_object* v_snd_1569_; lean_object* v_snd_1570_; uint8_t v___x_1571_; 
lean_del_object(v___x_1566_);
v_snd_1569_ = lean_ctor_get(v_a_1564_, 1);
lean_inc(v_snd_1569_);
lean_dec(v_a_1564_);
v_snd_1570_ = lean_ctor_get(v_snd_1569_, 1);
v___x_1571_ = lean_unbox(v_snd_1570_);
if (v___x_1571_ == 0)
{
lean_object* v_snd_1572_; lean_object* v_fst_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1581_; 
v_snd_1572_ = lean_ctor_get(v_b_1544_, 1);
lean_inc(v_snd_1572_);
lean_dec_ref(v_b_1544_);
v_fst_1573_ = lean_ctor_get(v_snd_1569_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_snd_1569_);
if (v_isSharedCheck_1581_ == 0)
{
lean_object* v_unused_1582_; 
v_unused_1582_ = lean_ctor_get(v_snd_1569_, 1);
lean_dec(v_unused_1582_);
v___x_1575_ = v_snd_1569_;
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_fst_1573_);
lean_dec(v_snd_1569_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = lean_array_push(v_snd_1572_, v_fst_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v___x_1577_);
lean_ctor_set(v___x_1575_, 0, v___x_1555_);
v___x_1579_ = v___x_1575_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
v_a_1548_ = v___x_1579_;
goto v___jp_1547_;
}
}
}
else
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1590_; 
v_isSharedCheck_1590_ = !lean_is_exclusive(v_snd_1569_);
if (v_isSharedCheck_1590_ == 0)
{
lean_object* v_unused_1591_; lean_object* v_unused_1592_; 
v_unused_1591_ = lean_ctor_get(v_snd_1569_, 1);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_snd_1569_, 0);
lean_dec(v_unused_1592_);
v___x_1584_ = v_snd_1569_;
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v_snd_1569_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1590_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_snd_1586_; lean_object* v___x_1588_; 
v_snd_1586_ = lean_ctor_get(v_b_1544_, 1);
lean_inc(v_snd_1586_);
lean_dec_ref(v_b_1544_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 1, v_snd_1586_);
lean_ctor_set(v___x_1584_, 0, v___x_1555_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1555_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_snd_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
v_a_1548_ = v___x_1588_;
goto v___jp_1547_;
}
}
}
}
else
{
lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1603_; 
lean_inc_ref(v_fst_1568_);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_a_1564_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; lean_object* v_unused_1605_; 
v_unused_1604_ = lean_ctor_get(v_a_1564_, 1);
lean_dec(v_unused_1604_);
v_unused_1605_ = lean_ctor_get(v_a_1564_, 0);
lean_dec(v_unused_1605_);
v___x_1594_ = v_a_1564_;
v_isShared_1595_ = v_isSharedCheck_1603_;
goto v_resetjp_1593_;
}
else
{
lean_dec(v_a_1564_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1603_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v_snd_1596_; lean_object* v___x_1598_; 
v_snd_1596_ = lean_ctor_get(v_b_1544_, 1);
lean_inc(v_snd_1596_);
lean_dec_ref(v_b_1544_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 1, v_snd_1596_);
v___x_1598_ = v___x_1594_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_fst_1568_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_snd_1596_);
v___x_1598_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1600_; 
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 0, v___x_1598_);
v___x_1600_ = v___x_1566_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
}
}
}
else
{
lean_object* v_a_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1614_; 
lean_dec_ref(v_b_1544_);
v_a_1607_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1609_ = v___x_1563_;
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_a_1607_);
lean_dec(v___x_1563_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1614_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
lean_object* v___x_1612_; 
if (v_isShared_1610_ == 0)
{
v___x_1612_ = v___x_1609_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_a_1607_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
}
v___jp_1547_:
{
size_t v___x_1549_; size_t v___x_1550_; 
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_add(v_i_1543_, v___x_1549_);
v_i_1543_ = v___x_1550_;
v_b_1544_ = v_a_1548_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1___boxed(lean_object* v_p_1615_, lean_object* v___x_1616_, lean_object* v___x_1617_, lean_object* v_as_1618_, lean_object* v_sz_1619_, lean_object* v_i_1620_, lean_object* v_b_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
size_t v_sz_boxed_1624_; size_t v_i_boxed_1625_; lean_object* v_res_1626_; 
v_sz_boxed_1624_ = lean_unbox_usize(v_sz_1619_);
lean_dec(v_sz_1619_);
v_i_boxed_1625_ = lean_unbox_usize(v_i_1620_);
lean_dec(v_i_1620_);
v_res_1626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1615_, v___x_1616_, v___x_1617_, v_as_1618_, v_sz_boxed_1624_, v_i_boxed_1625_, v_b_1621_, v___y_1622_);
lean_dec_ref(v___y_1622_);
lean_dec_ref(v_as_1618_);
lean_dec_ref(v___x_1617_);
lean_dec_ref(v___x_1616_);
lean_dec_ref(v_p_1615_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(lean_object* v_p_1630_, lean_object* v_oldInlayHints_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_doc_1634_; lean_object* v_toEditableDocumentCore_1635_; lean_object* v_meta_1636_; lean_object* v_text_1637_; lean_object* v___x_1638_; size_t v_sz_1639_; size_t v___x_1640_; lean_object* v___x_1641_; 
v_doc_1634_ = lean_ctor_get(v_a_1632_, 1);
v_toEditableDocumentCore_1635_ = lean_ctor_get(v_doc_1634_, 0);
v_meta_1636_ = lean_ctor_get(v_toEditableDocumentCore_1635_, 0);
v_text_1637_ = lean_ctor_get(v_meta_1636_, 3);
v___x_1638_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0));
v_sz_1639_ = lean_array_size(v_oldInlayHints_1631_);
v___x_1640_ = ((size_t)0ULL);
v___x_1641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1630_, v_text_1637_, v_meta_1636_, v_oldInlayHints_1631_, v_sz_1639_, v___x_1640_, v___x_1638_, v_a_1632_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v___x_1644_; uint8_t v_isShared_1645_; uint8_t v_isSharedCheck_1655_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1644_ = v___x_1641_;
v_isShared_1645_ = v_isSharedCheck_1655_;
goto v_resetjp_1643_;
}
else
{
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1644_ = lean_box(0);
v_isShared_1645_ = v_isSharedCheck_1655_;
goto v_resetjp_1643_;
}
v_resetjp_1643_:
{
lean_object* v_fst_1646_; 
v_fst_1646_ = lean_ctor_get(v_a_1642_, 0);
if (lean_obj_tag(v_fst_1646_) == 0)
{
lean_object* v_snd_1647_; lean_object* v___x_1649_; 
v_snd_1647_ = lean_ctor_get(v_a_1642_, 1);
lean_inc(v_snd_1647_);
lean_dec(v_a_1642_);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v_snd_1647_);
v___x_1649_ = v___x_1644_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1650_; 
v_reuseFailAlloc_1650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_snd_1647_);
v___x_1649_ = v_reuseFailAlloc_1650_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
return v___x_1649_;
}
}
else
{
lean_object* v_val_1651_; lean_object* v___x_1653_; 
lean_inc_ref(v_fst_1646_);
lean_dec(v_a_1642_);
v_val_1651_ = lean_ctor_get(v_fst_1646_, 0);
lean_inc(v_val_1651_);
lean_dec_ref_known(v_fst_1646_, 1);
if (v_isShared_1645_ == 0)
{
lean_ctor_set(v___x_1644_, 0, v_val_1651_);
v___x_1653_ = v___x_1644_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_val_1651_);
v___x_1653_ = v_reuseFailAlloc_1654_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
return v___x_1653_;
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
v_a_1656_ = lean_ctor_get(v___x_1641_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1641_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1641_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___boxed(lean_object* v_p_1664_, lean_object* v_oldInlayHints_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1664_, v_oldInlayHints_1665_, v_a_1666_);
lean_dec_ref(v_a_1666_);
lean_dec_ref(v_oldInlayHints_1665_);
lean_dec_ref(v_p_1664_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(lean_object* v___x_1669_, lean_object* v___x_1670_, lean_object* v_as_1671_, size_t v_sz_1672_, size_t v_i_1673_, lean_object* v_b_1674_, lean_object* v___y_1675_){
_start:
{
lean_object* v___x_1677_; 
v___x_1677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1669_, v___x_1670_, v_as_1671_, v_sz_1672_, v_i_1673_, v_b_1674_);
return v___x_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___boxed(lean_object* v___x_1678_, lean_object* v___x_1679_, lean_object* v_as_1680_, lean_object* v_sz_1681_, lean_object* v_i_1682_, lean_object* v_b_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_){
_start:
{
size_t v_sz_boxed_1686_; size_t v_i_boxed_1687_; lean_object* v_res_1688_; 
v_sz_boxed_1686_ = lean_unbox_usize(v_sz_1681_);
lean_dec(v_sz_1681_);
v_i_boxed_1687_ = lean_unbox_usize(v_i_1682_);
lean_dec(v_i_1682_);
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(v___x_1678_, v___x_1679_, v_as_1680_, v_sz_boxed_1686_, v_i_boxed_1687_, v_b_1683_, v___y_1684_);
lean_dec_ref(v___y_1684_);
lean_dec_ref(v_as_1680_);
lean_dec_ref(v___x_1679_);
lean_dec_ref(v___x_1678_);
return v_res_1688_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(lean_object* v_a_1689_, lean_object* v_as_1690_, size_t v_i_1691_, size_t v_stop_1692_){
_start:
{
uint8_t v___x_1693_; 
v___x_1693_ = lean_usize_dec_eq(v_i_1691_, v_stop_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1694_ = lean_array_uget_borrowed(v_as_1690_, v_i_1691_);
v___x_1695_ = l_Lean_Elab_instBEqInlayHintTextEdit_beq(v_a_1689_, v___x_1694_);
if (v___x_1695_ == 0)
{
size_t v___x_1696_; size_t v___x_1697_; 
v___x_1696_ = ((size_t)1ULL);
v___x_1697_ = lean_usize_add(v_i_1691_, v___x_1696_);
v_i_1691_ = v___x_1697_;
goto _start;
}
else
{
return v___x_1695_;
}
}
else
{
uint8_t v___x_1699_; 
v___x_1699_ = 0;
return v___x_1699_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0___boxed(lean_object* v_a_1700_, lean_object* v_as_1701_, lean_object* v_i_1702_, lean_object* v_stop_1703_){
_start:
{
size_t v_i_boxed_1704_; size_t v_stop_boxed_1705_; uint8_t v_res_1706_; lean_object* v_r_1707_; 
v_i_boxed_1704_ = lean_unbox_usize(v_i_1702_);
lean_dec(v_i_1702_);
v_stop_boxed_1705_ = lean_unbox_usize(v_stop_1703_);
lean_dec(v_stop_1703_);
v_res_1706_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1700_, v_as_1701_, v_i_boxed_1704_, v_stop_boxed_1705_);
lean_dec_ref(v_as_1701_);
lean_dec_ref(v_a_1700_);
v_r_1707_ = lean_box(v_res_1706_);
return v_r_1707_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(lean_object* v_as_1708_, lean_object* v_a_1709_){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_array_get_size(v_as_1708_);
v___x_1712_ = lean_nat_dec_lt(v___x_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
return v___x_1712_;
}
else
{
if (v___x_1712_ == 0)
{
return v___x_1712_;
}
else
{
size_t v___x_1713_; size_t v___x_1714_; uint8_t v___x_1715_; 
v___x_1713_ = ((size_t)0ULL);
v___x_1714_ = lean_usize_of_nat(v___x_1711_);
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1709_, v_as_1708_, v___x_1713_, v___x_1714_);
return v___x_1715_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0___boxed(lean_object* v_as_1716_, lean_object* v_a_1717_){
_start:
{
uint8_t v_res_1718_; lean_object* v_r_1719_; 
v_res_1718_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_as_1716_, v_a_1717_);
lean_dec_ref(v_a_1717_);
lean_dec_ref(v_as_1716_);
v_r_1719_ = lean_box(v_res_1718_);
return v_r_1719_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(lean_object* v___x_1720_, lean_object* v_as_1721_, size_t v_i_1722_, size_t v_stop_1723_){
_start:
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_usize_dec_eq(v_i_1722_, v_stop_1723_);
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; lean_object* v_textEdits_1726_; uint8_t v___x_1727_; 
v___x_1725_ = lean_array_uget_borrowed(v_as_1721_, v_i_1722_);
v_textEdits_1726_ = lean_ctor_get(v___x_1725_, 3);
v___x_1727_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_textEdits_1726_, v___x_1720_);
if (v___x_1727_ == 0)
{
size_t v___x_1728_; size_t v___x_1729_; 
v___x_1728_ = ((size_t)1ULL);
v___x_1729_ = lean_usize_add(v_i_1722_, v___x_1728_);
v_i_1722_ = v___x_1729_;
goto _start;
}
else
{
return v___x_1727_;
}
}
else
{
uint8_t v___x_1731_; 
v___x_1731_ = 0;
return v___x_1731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1___boxed(lean_object* v___x_1732_, lean_object* v_as_1733_, lean_object* v_i_1734_, lean_object* v_stop_1735_){
_start:
{
size_t v_i_boxed_1736_; size_t v_stop_boxed_1737_; uint8_t v_res_1738_; lean_object* v_r_1739_; 
v_i_boxed_1736_ = lean_unbox_usize(v_i_1734_);
lean_dec(v_i_1734_);
v_stop_boxed_1737_ = lean_unbox_usize(v_stop_1735_);
lean_dec(v_stop_1735_);
v_res_1738_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1732_, v_as_1733_, v_i_boxed_1736_, v_stop_boxed_1737_);
lean_dec_ref(v_as_1733_);
lean_dec_ref(v___x_1732_);
v_r_1739_ = lean_box(v_res_1738_);
return v_r_1739_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(lean_object* v_oldInlayHints_1740_, lean_object* v___x_1741_, lean_object* v_as_1742_, size_t v_i_1743_, size_t v_stop_1744_){
_start:
{
uint8_t v___x_1745_; 
v___x_1745_ = lean_usize_dec_eq(v_i_1743_, v_stop_1744_);
if (v___x_1745_ == 0)
{
uint8_t v___x_1746_; lean_object* v___x_1747_; 
v___x_1746_ = 1;
v___x_1747_ = lean_array_uget(v_as_1742_, v_i_1743_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_range_1748_; lean_object* v_text_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1766_; 
v_range_1748_ = lean_ctor_get(v___x_1747_, 0);
v_text_1749_ = lean_ctor_get(v___x_1747_, 1);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1751_ = v___x_1747_;
v_isShared_1752_ = v_isSharedCheck_1766_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_text_1749_);
lean_inc(v_range_1748_);
lean_dec(v___x_1747_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1766_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; uint8_t v___x_1755_; 
v___x_1753_ = lean_unsigned_to_nat(0u);
v___x_1754_ = lean_array_get_size(v_oldInlayHints_1740_);
v___x_1755_ = lean_nat_dec_lt(v___x_1753_, v___x_1754_);
if (v___x_1755_ == 0)
{
lean_del_object(v___x_1751_);
lean_dec_ref(v_text_1749_);
lean_dec_ref(v_range_1748_);
return v___x_1746_;
}
else
{
if (v___x_1755_ == 0)
{
lean_del_object(v___x_1751_);
lean_dec_ref(v_text_1749_);
lean_dec_ref(v_range_1748_);
return v___x_1746_;
}
else
{
lean_object* v___x_1756_; lean_object* v___x_1758_; 
v___x_1756_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1741_, v_range_1748_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1756_);
v___x_1758_ = v___x_1751_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1756_);
lean_ctor_set(v_reuseFailAlloc_1765_, 1, v_text_1749_);
v___x_1758_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
size_t v___x_1759_; size_t v___x_1760_; uint8_t v___x_1761_; 
v___x_1759_ = ((size_t)0ULL);
v___x_1760_ = lean_usize_of_nat(v___x_1754_);
v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1758_, v_oldInlayHints_1740_, v___x_1759_, v___x_1760_);
lean_dec_ref(v___x_1758_);
if (v___x_1761_ == 0)
{
return v___x_1746_;
}
else
{
if (v___x_1745_ == 0)
{
size_t v___x_1762_; size_t v___x_1763_; 
v___x_1762_ = ((size_t)1ULL);
v___x_1763_ = lean_usize_add(v_i_1743_, v___x_1762_);
v_i_1743_ = v___x_1763_;
goto _start;
}
else
{
return v___x_1746_;
}
}
}
}
}
}
}
else
{
lean_dec(v___x_1747_);
return v___x_1746_;
}
}
else
{
uint8_t v___x_1767_; 
v___x_1767_ = 0;
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2___boxed(lean_object* v_oldInlayHints_1768_, lean_object* v___x_1769_, lean_object* v_as_1770_, lean_object* v_i_1771_, lean_object* v_stop_1772_){
_start:
{
size_t v_i_boxed_1773_; size_t v_stop_boxed_1774_; uint8_t v_res_1775_; lean_object* v_r_1776_; 
v_i_boxed_1773_ = lean_unbox_usize(v_i_1771_);
lean_dec(v_i_1771_);
v_stop_boxed_1774_ = lean_unbox_usize(v_stop_1772_);
lean_dec(v_stop_1772_);
v_res_1775_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1768_, v___x_1769_, v_as_1770_, v_i_boxed_1773_, v_stop_boxed_1774_);
lean_dec_ref(v_as_1770_);
lean_dec_ref(v___x_1769_);
lean_dec_ref(v_oldInlayHints_1768_);
v_r_1776_ = lean_box(v_res_1775_);
return v_r_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(lean_object* v_p_1777_, lean_object* v_oldInlayHints_1778_, lean_object* v_a_1779_){
_start:
{
uint8_t v___y_1782_; lean_object* v_contentChanges_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_contentChanges_1788_ = lean_ctor_get(v_p_1777_, 1);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = lean_array_get_size(v_contentChanges_1788_);
v___x_1791_ = lean_nat_dec_lt(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
uint8_t v___x_1792_; 
v___x_1792_ = 1;
v___y_1782_ = v___x_1792_;
goto v___jp_1781_;
}
else
{
if (v___x_1791_ == 0)
{
v___y_1782_ = v___x_1791_;
goto v___jp_1781_;
}
else
{
lean_object* v_doc_1793_; lean_object* v_toEditableDocumentCore_1794_; lean_object* v_meta_1795_; lean_object* v_text_1796_; size_t v___x_1797_; size_t v___x_1798_; uint8_t v___x_1799_; 
v_doc_1793_ = lean_ctor_get(v_a_1779_, 1);
v_toEditableDocumentCore_1794_ = lean_ctor_get(v_doc_1793_, 0);
v_meta_1795_ = lean_ctor_get(v_toEditableDocumentCore_1794_, 0);
v_text_1796_ = lean_ctor_get(v_meta_1795_, 3);
v___x_1797_ = ((size_t)0ULL);
v___x_1798_ = lean_usize_of_nat(v___x_1790_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1778_, v_text_1796_, v_contentChanges_1788_, v___x_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
v___y_1782_ = v___x_1791_;
goto v___jp_1781_;
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = 0;
v___y_1782_ = v___x_1800_;
goto v___jp_1781_;
}
}
}
v___jp_1781_:
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_io_mono_ms_now();
if (v___y_1782_ == 0)
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
v___x_1785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
return v___x_1785_;
}
else
{
lean_object* v___x_1786_; lean_object* v___x_1787_; 
lean_dec(v___x_1783_);
v___x_1786_ = lean_box(0);
v___x_1787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1786_);
return v___x_1787_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___boxed(lean_object* v_p_1801_, lean_object* v_oldInlayHints_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1801_, v_oldInlayHints_1802_, v_a_1803_);
lean_dec_ref(v_a_1803_);
lean_dec_ref(v_oldInlayHints_1802_);
lean_dec_ref(v_p_1801_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange(lean_object* v_p_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_){
_start:
{
lean_object* v_oldInlayHints_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1840_; 
v_oldInlayHints_1810_ = lean_ctor_get(v_a_1807_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_a_1807_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; lean_object* v_unused_1842_; 
v_unused_1841_ = lean_ctor_get(v_a_1807_, 2);
lean_dec(v_unused_1841_);
v_unused_1842_ = lean_ctor_get(v_a_1807_, 1);
lean_dec(v_unused_1842_);
v___x_1812_ = v_a_1807_;
v_isShared_1813_ = v_isSharedCheck_1840_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_oldInlayHints_1810_);
lean_dec(v_a_1807_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1840_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1814_; 
v___x_1814_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1806_, v_oldInlayHints_1810_, v_a_1808_);
if (lean_obj_tag(v___x_1814_) == 0)
{
lean_object* v_a_1815_; lean_object* v___x_1816_; lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1831_; 
v_a_1815_ = lean_ctor_get(v___x_1814_, 0);
lean_inc(v_a_1815_);
lean_dec_ref_known(v___x_1814_, 1);
v___x_1816_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1806_, v_oldInlayHints_1810_, v_a_1808_);
lean_dec_ref(v_oldInlayHints_1810_);
v_a_1817_ = lean_ctor_get(v___x_1816_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1816_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1819_ = v___x_1816_;
v_isShared_1820_ = v_isSharedCheck_1831_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1816_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1831_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1821_; uint8_t v___x_1822_; lean_object* v___x_1824_; 
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = 1;
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 2, v_a_1817_);
lean_ctor_set(v___x_1812_, 1, v___x_1821_);
lean_ctor_set(v___x_1812_, 0, v_a_1815_);
v___x_1824_ = v___x_1812_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1815_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1821_);
lean_ctor_set(v_reuseFailAlloc_1830_, 2, v_a_1817_);
v___x_1824_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1828_; 
lean_ctor_set_uint8(v___x_1824_, sizeof(void*)*3, v___x_1822_);
v___x_1825_ = lean_box(0);
v___x_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
lean_ctor_set(v___x_1826_, 1, v___x_1824_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1826_);
v___x_1828_ = v___x_1819_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_del_object(v___x_1812_);
lean_dec_ref(v_oldInlayHints_1810_);
v_a_1832_ = lean_ctor_get(v___x_1814_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1814_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1814_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1814_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed(lean_object* v_p_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Server_FileWorker_handleInlayHintsDidChange(v_p_1843_, v_a_1844_, v_a_1845_);
lean_dec_ref(v_a_1845_);
lean_dec_ref(v_p_1843_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(lean_object* v___x_1848_, lean_object* v_x_1849_){
_start:
{
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed(lean_object* v___x_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(v___x_1850_, v_x_1851_);
lean_dec_ref(v_x_1851_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v_ks_1857_; lean_object* v_vs_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1882_; 
v_ks_1857_ = lean_ctor_get(v_x_1853_, 0);
v_vs_1858_ = lean_ctor_get(v_x_1853_, 1);
v_isSharedCheck_1882_ = !lean_is_exclusive(v_x_1853_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1860_ = v_x_1853_;
v_isShared_1861_ = v_isSharedCheck_1882_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_vs_1858_);
lean_inc(v_ks_1857_);
lean_dec(v_x_1853_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1882_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1862_; uint8_t v___x_1863_; 
v___x_1862_ = lean_array_get_size(v_ks_1857_);
v___x_1863_ = lean_nat_dec_lt(v_x_1854_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
lean_dec(v_x_1854_);
v___x_1864_ = lean_array_push(v_ks_1857_, v_x_1855_);
v___x_1865_ = lean_array_push(v_vs_1858_, v_x_1856_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v___x_1865_);
lean_ctor_set(v___x_1860_, 0, v___x_1864_);
v___x_1867_ = v___x_1860_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1864_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_object* v_k_x27_1869_; uint8_t v___x_1870_; 
v_k_x27_1869_ = lean_array_fget_borrowed(v_ks_1857_, v_x_1854_);
v___x_1870_ = lean_string_dec_eq(v_x_1855_, v_k_x27_1869_);
if (v___x_1870_ == 0)
{
lean_object* v___x_1872_; 
if (v_isShared_1861_ == 0)
{
v___x_1872_ = v___x_1860_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1876_; 
v_reuseFailAlloc_1876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1876_, 0, v_ks_1857_);
lean_ctor_set(v_reuseFailAlloc_1876_, 1, v_vs_1858_);
v___x_1872_ = v_reuseFailAlloc_1876_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = lean_nat_add(v_x_1854_, v___x_1873_);
lean_dec(v_x_1854_);
v_x_1853_ = v___x_1872_;
v_x_1854_ = v___x_1874_;
goto _start;
}
}
else
{
lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1880_; 
v___x_1877_ = lean_array_fset(v_ks_1857_, v_x_1854_, v_x_1855_);
v___x_1878_ = lean_array_fset(v_vs_1858_, v_x_1854_, v_x_1856_);
lean_dec(v_x_1854_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 1, v___x_1878_);
lean_ctor_set(v___x_1860_, 0, v___x_1877_);
v___x_1880_ = v___x_1860_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v___x_1877_);
lean_ctor_set(v_reuseFailAlloc_1881_, 1, v___x_1878_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(lean_object* v_n_1883_, lean_object* v_k_1884_, lean_object* v_v_1885_){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_n_1883_, v___x_1886_, v_k_1884_, v_v_1885_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(lean_object* v_x_1889_, size_t v_x_1890_, size_t v_x_1891_, lean_object* v_x_1892_, lean_object* v_x_1893_){
_start:
{
if (lean_obj_tag(v_x_1889_) == 0)
{
lean_object* v_es_1894_; size_t v___x_1895_; size_t v___x_1896_; lean_object* v_j_1897_; lean_object* v___x_1898_; uint8_t v___x_1899_; 
v_es_1894_ = lean_ctor_get(v_x_1889_, 0);
v___x_1895_ = ((size_t)31ULL);
v___x_1896_ = lean_usize_land(v_x_1890_, v___x_1895_);
v_j_1897_ = lean_usize_to_nat(v___x_1896_);
v___x_1898_ = lean_array_get_size(v_es_1894_);
v___x_1899_ = lean_nat_dec_lt(v_j_1897_, v___x_1898_);
if (v___x_1899_ == 0)
{
lean_dec(v_j_1897_);
lean_dec(v_x_1893_);
lean_dec_ref(v_x_1892_);
return v_x_1889_;
}
else
{
lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1938_; 
lean_inc_ref(v_es_1894_);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_x_1889_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v_x_1889_, 0);
lean_dec(v_unused_1939_);
v___x_1901_ = v_x_1889_;
v_isShared_1902_ = v_isSharedCheck_1938_;
goto v_resetjp_1900_;
}
else
{
lean_dec(v_x_1889_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1938_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v_v_1903_; lean_object* v___x_1904_; lean_object* v_xs_x27_1905_; lean_object* v___y_1907_; 
v_v_1903_ = lean_array_fget(v_es_1894_, v_j_1897_);
v___x_1904_ = lean_box(0);
v_xs_x27_1905_ = lean_array_fset(v_es_1894_, v_j_1897_, v___x_1904_);
switch(lean_obj_tag(v_v_1903_))
{
case 0:
{
lean_object* v_key_1912_; lean_object* v_val_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1923_; 
v_key_1912_ = lean_ctor_get(v_v_1903_, 0);
v_val_1913_ = lean_ctor_get(v_v_1903_, 1);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_v_1903_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1915_ = v_v_1903_;
v_isShared_1916_ = v_isSharedCheck_1923_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_val_1913_);
lean_inc(v_key_1912_);
lean_dec(v_v_1903_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1923_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
uint8_t v___x_1917_; 
v___x_1917_ = lean_string_dec_eq(v_x_1892_, v_key_1912_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
lean_del_object(v___x_1915_);
v___x_1918_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1912_, v_val_1913_, v_x_1892_, v_x_1893_);
v___x_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
v___y_1907_ = v___x_1919_;
goto v___jp_1906_;
}
else
{
lean_object* v___x_1921_; 
lean_dec(v_val_1913_);
lean_dec(v_key_1912_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v_x_1893_);
lean_ctor_set(v___x_1915_, 0, v_x_1892_);
v___x_1921_ = v___x_1915_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_x_1892_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_x_1893_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
v___y_1907_ = v___x_1921_;
goto v___jp_1906_;
}
}
}
}
case 1:
{
lean_object* v_node_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1936_; 
v_node_1924_ = lean_ctor_get(v_v_1903_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_v_1903_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1926_ = v_v_1903_;
v_isShared_1927_ = v_isSharedCheck_1936_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_node_1924_);
lean_dec(v_v_1903_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1936_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
size_t v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1928_ = ((size_t)5ULL);
v___x_1929_ = lean_usize_shift_right(v_x_1890_, v___x_1928_);
v___x_1930_ = ((size_t)1ULL);
v___x_1931_ = lean_usize_add(v_x_1891_, v___x_1930_);
v___x_1932_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_node_1924_, v___x_1929_, v___x_1931_, v_x_1892_, v_x_1893_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1932_);
v___x_1934_ = v___x_1926_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
v___y_1907_ = v___x_1934_;
goto v___jp_1906_;
}
}
}
default: 
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v_x_1892_);
lean_ctor_set(v___x_1937_, 1, v_x_1893_);
v___y_1907_ = v___x_1937_;
goto v___jp_1906_;
}
}
v___jp_1906_:
{
lean_object* v___x_1908_; lean_object* v___x_1910_; 
v___x_1908_ = lean_array_fset(v_xs_x27_1905_, v_j_1897_, v___y_1907_);
lean_dec(v_j_1897_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1908_);
v___x_1910_ = v___x_1901_;
goto v_reusejp_1909_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1908_);
v___x_1910_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1909_;
}
v_reusejp_1909_:
{
return v___x_1910_;
}
}
}
}
}
else
{
lean_object* v_ks_1940_; lean_object* v_vs_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1961_; 
v_ks_1940_ = lean_ctor_get(v_x_1889_, 0);
v_vs_1941_ = lean_ctor_get(v_x_1889_, 1);
v_isSharedCheck_1961_ = !lean_is_exclusive(v_x_1889_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1943_ = v_x_1889_;
v_isShared_1944_ = v_isSharedCheck_1961_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_vs_1941_);
lean_inc(v_ks_1940_);
lean_dec(v_x_1889_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1961_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1944_ == 0)
{
v___x_1946_ = v___x_1943_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_ks_1940_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v_vs_1941_);
v___x_1946_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v_newNode_1947_; uint8_t v___y_1949_; size_t v___x_1955_; uint8_t v___x_1956_; 
v_newNode_1947_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v___x_1946_, v_x_1892_, v_x_1893_);
v___x_1955_ = ((size_t)7ULL);
v___x_1956_ = lean_usize_dec_le(v___x_1955_, v_x_1891_);
if (v___x_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1957_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1947_);
v___x_1958_ = lean_unsigned_to_nat(4u);
v___x_1959_ = lean_nat_dec_lt(v___x_1957_, v___x_1958_);
lean_dec(v___x_1957_);
v___y_1949_ = v___x_1959_;
goto v___jp_1948_;
}
else
{
v___y_1949_ = v___x_1956_;
goto v___jp_1948_;
}
v___jp_1948_:
{
if (v___y_1949_ == 0)
{
lean_object* v_ks_1950_; lean_object* v_vs_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_ks_1950_ = lean_ctor_get(v_newNode_1947_, 0);
lean_inc_ref(v_ks_1950_);
v_vs_1951_ = lean_ctor_get(v_newNode_1947_, 1);
lean_inc_ref(v_vs_1951_);
lean_dec_ref(v_newNode_1947_);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0);
v___x_1954_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_x_1891_, v_ks_1950_, v_vs_1951_, v___x_1952_, v___x_1953_);
lean_dec_ref(v_vs_1951_);
lean_dec_ref(v_ks_1950_);
return v___x_1954_;
}
else
{
return v_newNode_1947_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(size_t v_depth_1962_, lean_object* v_keys_1963_, lean_object* v_vals_1964_, lean_object* v_i_1965_, lean_object* v_entries_1966_){
_start:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_array_get_size(v_keys_1963_);
v___x_1968_ = lean_nat_dec_lt(v_i_1965_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_dec(v_i_1965_);
return v_entries_1966_;
}
else
{
lean_object* v_k_1969_; lean_object* v_v_1970_; uint64_t v___x_1971_; size_t v_h_1972_; size_t v___x_1973_; lean_object* v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; size_t v___x_1977_; size_t v_h_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v_k_1969_ = lean_array_fget_borrowed(v_keys_1963_, v_i_1965_);
v_v_1970_ = lean_array_fget_borrowed(v_vals_1964_, v_i_1965_);
v___x_1971_ = lean_string_hash(v_k_1969_);
v_h_1972_ = lean_uint64_to_usize(v___x_1971_);
v___x_1973_ = ((size_t)5ULL);
v___x_1974_ = lean_unsigned_to_nat(1u);
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_sub(v_depth_1962_, v___x_1975_);
v___x_1977_ = lean_usize_mul(v___x_1973_, v___x_1976_);
v_h_1978_ = lean_usize_shift_right(v_h_1972_, v___x_1977_);
v___x_1979_ = lean_nat_add(v_i_1965_, v___x_1974_);
lean_dec(v_i_1965_);
lean_inc(v_v_1970_);
lean_inc(v_k_1969_);
v___x_1980_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_entries_1966_, v_h_1978_, v_depth_1962_, v_k_1969_, v_v_1970_);
v_i_1965_ = v___x_1979_;
v_entries_1966_ = v___x_1980_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_depth_1982_, lean_object* v_keys_1983_, lean_object* v_vals_1984_, lean_object* v_i_1985_, lean_object* v_entries_1986_){
_start:
{
size_t v_depth_boxed_1987_; lean_object* v_res_1988_; 
v_depth_boxed_1987_ = lean_unbox_usize(v_depth_1982_);
lean_dec(v_depth_1982_);
v_res_1988_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_boxed_1987_, v_keys_1983_, v_vals_1984_, v_i_1985_, v_entries_1986_);
lean_dec_ref(v_vals_1984_);
lean_dec_ref(v_keys_1983_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_){
_start:
{
size_t v_x_2350__boxed_1994_; size_t v_x_2351__boxed_1995_; lean_object* v_res_1996_; 
v_x_2350__boxed_1994_ = lean_unbox_usize(v_x_1990_);
lean_dec(v_x_1990_);
v_x_2351__boxed_1995_ = lean_unbox_usize(v_x_1991_);
lean_dec(v_x_1991_);
v_res_1996_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_1989_, v_x_2350__boxed_1994_, v_x_2351__boxed_1995_, v_x_1992_, v_x_1993_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(lean_object* v_x_1997_, lean_object* v_x_1998_, lean_object* v_x_1999_){
_start:
{
uint64_t v___x_2000_; size_t v___x_2001_; size_t v___x_2002_; lean_object* v___x_2003_; 
v___x_2000_ = lean_string_hash(v_x_1998_);
v___x_2001_ = lean_uint64_to_usize(v___x_2000_);
v___x_2002_ = ((size_t)1ULL);
v___x_2003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_1997_, v___x_2001_, v___x_2002_, v_x_1998_, v_x_1999_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(lean_object* v_val_2004_, lean_object* v___f_2005_, lean_object* v_param_2006_, lean_object* v___x_2007_, lean_object* v_x_2008_, lean_object* v___y_2009_){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2011_ = lean_st_ref_get(v_val_2004_);
lean_inc_ref(v___y_2009_);
v___x_2012_ = lean_apply_4(v___f_2005_, v_param_2006_, v___x_2011_, v___y_2009_, lean_box(0));
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2022_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2022_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2022_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2022_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_snd_2017_; lean_object* v___x_2018_; lean_object* v___x_2020_; 
v_snd_2017_ = lean_ctor_get(v_a_2013_, 1);
lean_inc(v_snd_2017_);
lean_dec(v_a_2013_);
v___x_2018_ = lean_st_ref_swap(v_val_2004_, v_snd_2017_);
lean_dec(v___x_2018_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 0, v___x_2007_);
v___x_2020_ = v___x_2015_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v___x_2007_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
else
{
lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2030_; 
v_a_2023_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2030_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2025_ = v___x_2012_;
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_dec(v___x_2012_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2030_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2028_; 
if (v_isShared_2026_ == 0)
{
v___x_2028_ = v___x_2025_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_a_2023_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed(lean_object* v_val_2031_, lean_object* v___f_2032_, lean_object* v_param_2033_, lean_object* v___x_2034_, lean_object* v_x_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(v_val_2031_, v___f_2032_, v_param_2033_, v___x_2034_, v_x_2035_, v___y_2036_);
lean_dec_ref(v___y_2036_);
lean_dec(v_val_2031_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(lean_object* v_mutex_2039_, lean_object* v_a_x3f_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_io_basemutex_unlock(v_mutex_2039_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0___boxed(lean_object* v_mutex_2044_, lean_object* v_a_x3f_2045_, lean_object* v___y_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2044_, v_a_x3f_2045_);
lean_dec(v_a_x3f_2045_);
lean_dec(v_mutex_2044_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_mutex_2048_, lean_object* v_k_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_ref_2052_; lean_object* v_mutex_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v_ref_2052_ = lean_ctor_get(v_mutex_2048_, 0);
lean_inc(v_ref_2052_);
v_mutex_2053_ = lean_ctor_get(v_mutex_2048_, 1);
lean_inc(v_mutex_2053_);
lean_dec_ref(v_mutex_2048_);
v___x_2054_ = lean_io_basemutex_lock(v_mutex_2053_);
lean_inc_ref(v___y_2050_);
v___x_2055_ = lean_apply_3(v_k_2049_, v_ref_2052_, v___y_2050_, lean_box(0));
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2072_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2058_ = v___x_2055_;
v_isShared_2059_ = v_isSharedCheck_2072_;
goto v_resetjp_2057_;
}
else
{
lean_inc(v_a_2056_);
lean_dec(v___x_2055_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2072_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2061_; 
lean_inc(v_a_2056_);
if (v_isShared_2059_ == 0)
{
lean_ctor_set_tag(v___x_2058_, 1);
v___x_2061_ = v___x_2058_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2056_);
v___x_2061_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2069_; 
v___x_2062_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2053_, v___x_2061_);
lean_dec_ref(v___x_2061_);
lean_dec(v_mutex_2053_);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2069_ == 0)
{
lean_object* v_unused_2070_; 
v_unused_2070_ = lean_ctor_get(v___x_2062_, 0);
lean_dec(v_unused_2070_);
v___x_2064_ = v___x_2062_;
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
else
{
lean_dec(v___x_2062_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2069_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2067_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 0, v_a_2056_);
v___x_2067_ = v___x_2064_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2056_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
v_a_2073_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2055_, 1);
v___x_2074_ = lean_box(0);
v___x_2075_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2053_, v___x_2074_);
lean_dec(v_mutex_2053_);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2082_ == 0)
{
lean_object* v_unused_2083_; 
v_unused_2083_ = lean_ctor_get(v___x_2075_, 0);
lean_dec(v_unused_2083_);
v___x_2077_ = v___x_2075_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_dec(v___x_2075_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
lean_ctor_set_tag(v___x_2077_, 1);
lean_ctor_set(v___x_2077_, 0, v_a_2073_);
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2073_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_mutex_2084_, lean_object* v_k_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2084_, v_k_2085_, v___y_2086_);
lean_dec_ref(v___y_2086_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(lean_object* v___f_2089_, lean_object* v___f_2090_, lean_object* v___x_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___x_2095_ = lean_st_ref_get(v___y_2092_);
v___x_2096_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_2095_, v___f_2089_, v___y_2093_);
if (lean_obj_tag(v___x_2096_) == 0)
{
lean_object* v_a_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2106_; 
v_a_2097_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2099_ = v___x_2096_;
v_isShared_2100_ = v_isSharedCheck_2106_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_a_2097_);
lean_dec(v___x_2096_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2106_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2104_; 
v___x_2101_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2090_, v_a_2097_);
v___x_2102_ = lean_st_ref_swap(v___y_2092_, v___x_2101_);
lean_dec(v___x_2102_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 0, v___x_2091_);
v___x_2104_ = v___x_2099_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2091_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
lean_dec_ref(v___f_2090_);
v_a_2107_ = lean_ctor_get(v___x_2096_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2096_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2096_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2096_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed(lean_object* v___f_2115_, lean_object* v___f_2116_, lean_object* v___x_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(v___f_2115_, v___f_2116_, v___x_2117_, v___y_2118_, v___y_2119_);
lean_dec_ref(v___y_2119_);
lean_dec(v___y_2118_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(lean_object* v_val_2122_, lean_object* v___f_2123_, lean_object* v___x_2124_, lean_object* v___f_2125_, lean_object* v_val_2126_, lean_object* v_param_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___f_2130_; lean_object* v___f_2131_; lean_object* v___x_2132_; 
v___f_2130_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_2130_, 0, v_val_2122_);
lean_closure_set(v___f_2130_, 1, v___f_2123_);
lean_closure_set(v___f_2130_, 2, v_param_2127_);
lean_closure_set(v___f_2130_, 3, v___x_2124_);
v___f_2131_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_2131_, 0, v___f_2130_);
lean_closure_set(v___f_2131_, 1, v___f_2125_);
lean_closure_set(v___f_2131_, 2, v___x_2124_);
v___x_2132_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_2126_, v___f_2131_, v___y_2128_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed(lean_object* v_val_2133_, lean_object* v___f_2134_, lean_object* v___x_2135_, lean_object* v___f_2136_, lean_object* v_val_2137_, lean_object* v_param_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(v_val_2133_, v___f_2134_, v___x_2135_, v___f_2136_, v_val_2137_, v_param_2138_, v___y_2139_);
lean_dec_ref(v___y_2139_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(lean_object* v___x_2142_, lean_object* v_x_2143_){
_start:
{
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed(lean_object* v___x_2144_, lean_object* v_x_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(v___x_2144_, v_x_2145_);
lean_dec_ref(v_x_2145_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(lean_object* v_params_2149_){
_start:
{
lean_object* v___x_2150_; 
lean_inc(v_params_2149_);
v___x_2150_ = l_Lean_Lsp_instFromJsonInlayHintParams_fromJson(v_params_2149_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2166_; 
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2166_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2166_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
uint8_t v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
v___x_2155_ = 3;
v___x_2156_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2157_ = l_Lean_Json_compress(v_params_2149_);
v___x_2158_ = lean_string_append(v___x_2156_, v___x_2157_);
lean_dec_ref(v___x_2157_);
v___x_2159_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1));
v___x_2160_ = lean_string_append(v___x_2158_, v___x_2159_);
v___x_2161_ = lean_string_append(v___x_2160_, v_a_2151_);
lean_dec(v_a_2151_);
v___x_2162_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set_uint8(v___x_2162_, sizeof(void*)*1, v___x_2155_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 0, v___x_2162_);
v___x_2164_ = v___x_2153_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_params_2149_);
v_a_2167_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2150_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2150_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_j_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_j_2175_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2184_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2184_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2184_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2184_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2182_; 
if (v_isShared_2180_ == 0)
{
v___x_2182_ = v___x_2179_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
v___x_2182_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
return v___x_2182_;
}
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2193_; 
v_a_2185_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2187_ = v___x_2176_;
v_isShared_2188_ = v_isSharedCheck_2193_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2176_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2193_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v_textDocument_2189_; lean_object* v___x_2191_; 
v_textDocument_2189_ = lean_ctor_get(v_a_2185_, 1);
lean_inc_ref(v_textDocument_2189_);
lean_dec(v_a_2185_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 0, v_textDocument_2189_);
v___x_2191_ = v___x_2187_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_textDocument_2189_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(lean_object* v_method_2194_, lean_object* v_inst_2195_, lean_object* v_onDidChange_2196_, lean_object* v_param_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; 
v___x_2201_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2194_, v___y_2198_, lean_box(0), v_inst_2195_, v___y_2199_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; lean_object* v___x_2203_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
lean_dec_ref_known(v___x_2201_, 1);
lean_inc_ref(v___y_2199_);
v___x_2203_ = lean_apply_4(v_onDidChange_2196_, v_param_2197_, v_a_2202_, v___y_2199_, lean_box(0));
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2222_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2206_ = v___x_2203_;
v_isShared_2207_ = v_isSharedCheck_2222_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_dec(v___x_2203_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2222_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v_snd_2208_; lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2220_; 
v_snd_2208_ = lean_ctor_get(v_a_2204_, 1);
v_isSharedCheck_2220_ = !lean_is_exclusive(v_a_2204_);
if (v_isSharedCheck_2220_ == 0)
{
lean_object* v_unused_2221_; 
v_unused_2221_ = lean_ctor_get(v_a_2204_, 0);
lean_dec(v_unused_2221_);
v___x_2210_ = v_a_2204_;
v_isShared_2211_ = v_isSharedCheck_2220_;
goto v_resetjp_2209_;
}
else
{
lean_inc(v_snd_2208_);
lean_dec(v_a_2204_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2220_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2213_; 
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 0, v_inst_2195_);
v___x_2213_ = v___x_2210_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_inst_2195_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_snd_2208_);
v___x_2213_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2214_ = lean_box(0);
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
lean_ctor_set(v___x_2215_, 1, v___x_2213_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2215_);
v___x_2217_ = v___x_2206_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_inst_2195_);
v_a_2223_ = lean_ctor_get(v___x_2203_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2203_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2203_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2203_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec_ref(v_param_2197_);
lean_dec_ref(v_onDidChange_2196_);
lean_dec(v_inst_2195_);
v_a_2231_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2201_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2201_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed(lean_object* v_method_2239_, lean_object* v_inst_2240_, lean_object* v_onDidChange_2241_, lean_object* v_param_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(v_method_2239_, v_inst_2240_, v_onDidChange_2241_, v_param_2242_, v___y_2243_, v___y_2244_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v_method_2239_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(size_t v_sz_2247_, size_t v_i_2248_, lean_object* v_bs_2249_){
_start:
{
uint8_t v___x_2250_; 
v___x_2250_ = lean_usize_dec_lt(v_i_2248_, v_sz_2247_);
if (v___x_2250_ == 0)
{
return v_bs_2249_;
}
else
{
lean_object* v_v_2251_; lean_object* v___x_2252_; lean_object* v_bs_x27_2253_; lean_object* v___x_2254_; size_t v___x_2255_; size_t v___x_2256_; lean_object* v___x_2257_; 
v_v_2251_ = lean_array_uget(v_bs_2249_, v_i_2248_);
v___x_2252_ = lean_unsigned_to_nat(0u);
v_bs_x27_2253_ = lean_array_uset(v_bs_2249_, v_i_2248_, v___x_2252_);
v___x_2254_ = l_Lean_Lsp_instToJsonInlayHint_toJson(v_v_2251_);
v___x_2255_ = ((size_t)1ULL);
v___x_2256_ = lean_usize_add(v_i_2248_, v___x_2255_);
v___x_2257_ = lean_array_uset(v_bs_x27_2253_, v_i_2248_, v___x_2254_);
v_i_2248_ = v___x_2256_;
v_bs_2249_ = v___x_2257_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8___boxed(lean_object* v_sz_2259_, lean_object* v_i_2260_, lean_object* v_bs_2261_){
_start:
{
size_t v_sz_boxed_2262_; size_t v_i_boxed_2263_; lean_object* v_res_2264_; 
v_sz_boxed_2262_ = lean_unbox_usize(v_sz_2259_);
lean_dec(v_sz_2259_);
v_i_boxed_2263_ = lean_unbox_usize(v_i_2260_);
lean_dec(v_i_2260_);
v_res_2264_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_boxed_2262_, v_i_boxed_2263_, v_bs_2261_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object* v_a_2265_){
_start:
{
size_t v_sz_2266_; size_t v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_sz_2266_ = lean_array_size(v_a_2265_);
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_2266_, v___x_2267_, v_a_2265_);
v___x_2269_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_params_2270_){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_params_2270_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2272_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2272_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
lean_ctor_set_tag(v___x_2275_, 1);
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
else
{
lean_object* v_a_2281_; lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2288_; 
v_a_2281_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2272_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2272_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2286_; 
if (v_isShared_2284_ == 0)
{
lean_ctor_set_tag(v___x_2283_, 0);
v___x_2286_ = v___x_2283_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_a_2281_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_params_2289_, lean_object* v_a_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2289_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(lean_object* v_method_2292_, lean_object* v_inst_2293_, lean_object* v_handler_2294_, lean_object* v_param_2295_, lean_object* v_state_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_param_2295_);
if (lean_obj_tag(v___x_2299_) == 0)
{
lean_object* v_a_2300_; lean_object* v___x_2301_; 
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
lean_inc(v_a_2300_);
lean_dec_ref_known(v___x_2299_, 1);
v___x_2301_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2292_, v_state_2296_, lean_box(0), v_inst_2293_, v___y_2297_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v___x_2303_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
lean_inc_ref(v___y_2297_);
v___x_2303_ = lean_apply_4(v_handler_2294_, v_a_2300_, v_a_2302_, v___y_2297_, lean_box(0));
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2327_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2327_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2327_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_fst_2308_; lean_object* v_snd_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2326_; 
v_fst_2308_ = lean_ctor_get(v_a_2304_, 0);
v_snd_2309_ = lean_ctor_get(v_a_2304_, 1);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_a_2304_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2311_ = v_a_2304_;
v_isShared_2312_ = v_isSharedCheck_2326_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_snd_2309_);
lean_inc(v_fst_2308_);
lean_dec(v_a_2304_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2326_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v_response_2313_; uint8_t v_isComplete_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v_response_2313_ = lean_ctor_get(v_fst_2308_, 0);
lean_inc(v_response_2313_);
v_isComplete_2314_ = lean_ctor_get_uint8(v_fst_2308_, sizeof(void*)*1);
lean_dec(v_fst_2308_);
v___x_2315_ = l_Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(v_response_2313_);
lean_inc(v___x_2315_);
v___x_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
v___x_2317_ = l_Lean_Json_compress(v___x_2315_);
v___x_2318_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
lean_ctor_set_uint8(v___x_2318_, sizeof(void*)*2, v_isComplete_2314_);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v_inst_2293_);
v___x_2320_ = v___x_2311_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_inst_2293_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_snd_2309_);
v___x_2320_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2318_);
lean_ctor_set(v___x_2321_, 1, v___x_2320_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2321_);
v___x_2323_ = v___x_2306_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
else
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_inst_2293_);
v_a_2328_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2303_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2303_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_a_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
else
{
lean_object* v_a_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2343_; 
lean_dec(v_a_2300_);
lean_dec_ref(v_handler_2294_);
lean_dec(v_inst_2293_);
v_a_2336_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2338_ = v___x_2301_;
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_a_2336_);
lean_dec(v___x_2301_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2343_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2341_; 
if (v_isShared_2339_ == 0)
{
v___x_2341_ = v___x_2338_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_a_2336_);
v___x_2341_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
return v___x_2341_;
}
}
}
}
else
{
lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec_ref(v_handler_2294_);
lean_dec(v_inst_2293_);
v_a_2344_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2299_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_dec(v___x_2299_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed(lean_object* v_method_2352_, lean_object* v_inst_2353_, lean_object* v_handler_2354_, lean_object* v_param_2355_, lean_object* v_state_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(v_method_2352_, v_inst_2353_, v_handler_2354_, v_param_2355_, v_state_2356_, v___y_2357_);
lean_dec_ref(v___y_2357_);
lean_dec(v_state_2356_);
lean_dec_ref(v_method_2352_);
return v_res_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(lean_object* v___f_2360_, lean_object* v___f_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2365_ = lean_st_ref_get(v___y_2362_);
v___x_2366_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_2365_, v___f_2360_, v___y_2363_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2376_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
lean_inc(v_a_2367_);
v___x_2371_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2361_, v_a_2367_);
v___x_2372_ = lean_st_ref_swap(v___y_2362_, v___x_2371_);
lean_dec(v___x_2372_);
if (v_isShared_2370_ == 0)
{
v___x_2374_ = v___x_2369_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2367_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
else
{
lean_dec_ref(v___f_2361_);
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed(lean_object* v___f_2377_, lean_object* v___f_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(v___f_2377_, v___f_2378_, v___y_2379_, v___y_2380_);
lean_dec_ref(v___y_2380_);
lean_dec(v___y_2379_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(lean_object* v_val_2383_, lean_object* v___f_2384_, lean_object* v_param_2385_, lean_object* v_x_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = lean_st_ref_get(v_val_2383_);
lean_inc_ref(v___y_2387_);
v___x_2390_ = lean_apply_4(v___f_2384_, v_param_2385_, v___x_2389_, v___y_2387_, lean_box(0));
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2401_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2401_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v_fst_2395_; lean_object* v_snd_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v_fst_2395_ = lean_ctor_get(v_a_2391_, 0);
lean_inc(v_fst_2395_);
v_snd_2396_ = lean_ctor_get(v_a_2391_, 1);
lean_inc(v_snd_2396_);
lean_dec(v_a_2391_);
v___x_2397_ = lean_st_ref_swap(v_val_2383_, v_snd_2396_);
lean_dec(v___x_2397_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v_fst_2395_);
v___x_2399_ = v___x_2393_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_fst_2395_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
v_a_2402_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2390_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2390_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed(lean_object* v_val_2410_, lean_object* v___f_2411_, lean_object* v_param_2412_, lean_object* v_x_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v_res_2416_; 
v_res_2416_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(v_val_2410_, v___f_2411_, v_param_2412_, v_x_2413_, v___y_2414_);
lean_dec_ref(v___y_2414_);
lean_dec(v_val_2410_);
return v_res_2416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(lean_object* v_val_2417_, lean_object* v___f_2418_, lean_object* v___f_2419_, lean_object* v_val_2420_, lean_object* v_param_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___f_2424_; lean_object* v___f_2425_; lean_object* v___x_2426_; 
v___f_2424_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_2424_, 0, v_val_2417_);
lean_closure_set(v___f_2424_, 1, v___f_2418_);
lean_closure_set(v___f_2424_, 2, v_param_2421_);
v___f_2425_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_2425_, 0, v___f_2424_);
lean_closure_set(v___f_2425_, 1, v___f_2419_);
v___x_2426_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_2420_, v___f_2425_, v___y_2422_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed(lean_object* v_val_2427_, lean_object* v___f_2428_, lean_object* v___f_2429_, lean_object* v_val_2430_, lean_object* v_param_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(v_val_2427_, v___f_2428_, v___f_2429_, v_val_2430_, v_param_2431_, v___y_2432_);
lean_dec_ref(v___y_2432_);
return v_res_2434_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_box(0);
v___x_2438_ = lean_task_pure(v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_method_2444_, lean_object* v_completeness_2445_, lean_object* v_inst_2446_, lean_object* v_initState_2447_, lean_object* v_handler_2448_, lean_object* v_onDidChange_2449_){
_start:
{
uint8_t v___x_2451_; 
v___x_2451_ = l_Lean_initializing();
if (v___x_2451_ == 0)
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; 
lean_dec_ref(v_onDidChange_2449_);
lean_dec_ref(v_handler_2448_);
lean_dec(v_initState_2447_);
lean_dec(v_inst_2446_);
lean_dec(v_completeness_2445_);
v___x_2452_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0));
v___x_2453_ = lean_string_append(v___x_2452_, v_method_2444_);
lean_dec_ref(v_method_2444_);
v___x_2454_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2455_ = lean_string_append(v___x_2453_, v___x_2454_);
v___x_2456_ = lean_mk_io_user_error(v___x_2455_);
v___x_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
return v___x_2457_;
}
else
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___f_2465_; lean_object* v___f_2466_; lean_object* v___f_2467_; lean_object* v___f_2468_; lean_object* v___f_2469_; lean_object* v___f_2470_; lean_object* v___f_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2458_ = lean_box(0);
v___x_2459_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2);
v___x_2460_ = l_Std_Mutex_new___redArg(v___x_2459_);
lean_inc_n(v_inst_2446_, 2);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_inst_2446_);
lean_ctor_set(v___x_2461_, 1, v_initState_2447_);
lean_inc_ref(v___x_2461_);
v___x_2462_ = lean_st_mk_ref(v___x_2461_);
v___x_2463_ = l_Lean_Server_statefulRequestHandlers;
v___x_2464_ = lean_st_ref_take(v___x_2463_);
v___f_2465_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3));
lean_inc_ref_n(v_method_2444_, 2);
v___f_2466_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_2466_, 0, v_method_2444_);
lean_closure_set(v___f_2466_, 1, v_inst_2446_);
lean_closure_set(v___f_2466_, 2, v_handler_2448_);
v___f_2467_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_2467_, 0, v_method_2444_);
lean_closure_set(v___f_2467_, 1, v_inst_2446_);
lean_closure_set(v___f_2467_, 2, v_onDidChange_2449_);
v___f_2468_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4));
v___f_2469_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5));
lean_inc_ref_n(v___x_2460_, 2);
lean_inc_ref(v___f_2466_);
lean_inc_n(v___x_2462_, 2);
v___f_2470_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2470_, 0, v___x_2462_);
lean_closure_set(v___f_2470_, 1, v___f_2466_);
lean_closure_set(v___f_2470_, 2, v___f_2468_);
lean_closure_set(v___f_2470_, 3, v___x_2460_);
lean_inc_ref(v___f_2467_);
v___f_2471_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_2471_, 0, v___x_2462_);
lean_closure_set(v___f_2471_, 1, v___f_2467_);
lean_closure_set(v___f_2471_, 2, v___x_2458_);
lean_closure_set(v___f_2471_, 3, v___f_2469_);
lean_closure_set(v___f_2471_, 4, v___x_2460_);
v___x_2472_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2472_, 0, v___f_2465_);
lean_ctor_set(v___x_2472_, 1, v___f_2466_);
lean_ctor_set(v___x_2472_, 2, v___f_2470_);
lean_ctor_set(v___x_2472_, 3, v___f_2467_);
lean_ctor_set(v___x_2472_, 4, v___f_2471_);
lean_ctor_set(v___x_2472_, 5, v___x_2460_);
lean_ctor_set(v___x_2472_, 6, v___x_2461_);
lean_ctor_set(v___x_2472_, 7, v___x_2462_);
lean_ctor_set(v___x_2472_, 8, v_completeness_2445_);
v___x_2473_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v___x_2464_, v_method_2444_, v___x_2472_);
v___x_2474_ = lean_st_ref_put(v___x_2463_, v___x_2473_);
v___x_2475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
return v___x_2475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_method_2476_, lean_object* v_completeness_2477_, lean_object* v_inst_2478_, lean_object* v_initState_2479_, lean_object* v_handler_2480_, lean_object* v_onDidChange_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2476_, v_completeness_2477_, v_inst_2478_, v_initState_2479_, v_handler_2480_, v_onDidChange_2481_);
return v_res_2483_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_2484_, lean_object* v_i_2485_, lean_object* v_k_2486_){
_start:
{
lean_object* v___x_2487_; uint8_t v___x_2488_; 
v___x_2487_ = lean_array_get_size(v_keys_2484_);
v___x_2488_ = lean_nat_dec_lt(v_i_2485_, v___x_2487_);
if (v___x_2488_ == 0)
{
lean_dec(v_i_2485_);
return v___x_2488_;
}
else
{
lean_object* v_k_x27_2489_; uint8_t v___x_2490_; 
v_k_x27_2489_ = lean_array_fget_borrowed(v_keys_2484_, v_i_2485_);
v___x_2490_ = lean_string_dec_eq(v_k_2486_, v_k_x27_2489_);
if (v___x_2490_ == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_unsigned_to_nat(1u);
v___x_2492_ = lean_nat_add(v_i_2485_, v___x_2491_);
lean_dec(v_i_2485_);
v_i_2485_ = v___x_2492_;
goto _start;
}
else
{
lean_dec(v_i_2485_);
return v___x_2490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_2494_, lean_object* v_i_2495_, lean_object* v_k_2496_){
_start:
{
uint8_t v_res_2497_; lean_object* v_r_2498_; 
v_res_2497_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2494_, v_i_2495_, v_k_2496_);
lean_dec_ref(v_k_2496_);
lean_dec_ref(v_keys_2494_);
v_r_2498_ = lean_box(v_res_2497_);
return v_r_2498_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2499_, size_t v_x_2500_, lean_object* v_x_2501_){
_start:
{
if (lean_obj_tag(v_x_2499_) == 0)
{
lean_object* v_es_2502_; lean_object* v___x_2503_; size_t v___x_2504_; size_t v___x_2505_; lean_object* v_j_2506_; lean_object* v___x_2507_; 
v_es_2502_ = lean_ctor_get(v_x_2499_, 0);
v___x_2503_ = lean_box(2);
v___x_2504_ = ((size_t)31ULL);
v___x_2505_ = lean_usize_land(v_x_2500_, v___x_2504_);
v_j_2506_ = lean_usize_to_nat(v___x_2505_);
v___x_2507_ = lean_array_get_borrowed(v___x_2503_, v_es_2502_, v_j_2506_);
lean_dec(v_j_2506_);
switch(lean_obj_tag(v___x_2507_))
{
case 0:
{
lean_object* v_key_2508_; uint8_t v___x_2509_; 
v_key_2508_ = lean_ctor_get(v___x_2507_, 0);
v___x_2509_ = lean_string_dec_eq(v_x_2501_, v_key_2508_);
return v___x_2509_;
}
case 1:
{
lean_object* v_node_2510_; size_t v___x_2511_; size_t v___x_2512_; 
v_node_2510_ = lean_ctor_get(v___x_2507_, 0);
v___x_2511_ = ((size_t)5ULL);
v___x_2512_ = lean_usize_shift_right(v_x_2500_, v___x_2511_);
v_x_2499_ = v_node_2510_;
v_x_2500_ = v___x_2512_;
goto _start;
}
default: 
{
uint8_t v___x_2514_; 
v___x_2514_ = 0;
return v___x_2514_;
}
}
}
else
{
lean_object* v_ks_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; 
v_ks_2515_ = lean_ctor_get(v_x_2499_, 0);
v___x_2516_ = lean_unsigned_to_nat(0u);
v___x_2517_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_2515_, v___x_2516_, v_x_2501_);
return v___x_2517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_2518_, lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
size_t v_x_3310__boxed_2521_; uint8_t v_res_2522_; lean_object* v_r_2523_; 
v_x_3310__boxed_2521_ = lean_unbox_usize(v_x_2519_);
lean_dec(v_x_2519_);
v_res_2522_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2518_, v_x_3310__boxed_2521_, v_x_2520_);
lean_dec_ref(v_x_2520_);
lean_dec_ref(v_x_2518_);
v_r_2523_ = lean_box(v_res_2522_);
return v_r_2523_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_2524_, lean_object* v_x_2525_){
_start:
{
uint64_t v___x_2526_; size_t v___x_2527_; uint8_t v___x_2528_; 
v___x_2526_ = lean_string_hash(v_x_2525_);
v___x_2527_ = lean_uint64_to_usize(v___x_2526_);
v___x_2528_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2524_, v___x_2527_, v_x_2525_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2529_, lean_object* v_x_2530_){
_start:
{
uint8_t v_res_2531_; lean_object* v_r_2532_; 
v_res_2531_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2529_, v_x_2530_);
lean_dec_ref(v_x_2530_);
lean_dec_ref(v_x_2529_);
v_r_2532_ = lean_box(v_res_2531_);
return v_r_2532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_method_2534_, lean_object* v_completeness_2535_, lean_object* v_inst_2536_, lean_object* v_initState_2537_, lean_object* v_handler_2538_, lean_object* v_onDidChange_2539_){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v___x_2541_ = l_Lean_Server_requestHandlers;
v___x_2542_ = lean_st_ref_get(v___x_2541_);
v___x_2543_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_2542_, v_method_2534_);
lean_dec(v___x_2542_);
if (v___x_2543_ == 0)
{
lean_object* v___x_2544_; 
v___x_2544_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2534_, v_completeness_2535_, v_inst_2536_, v_initState_2537_, v_handler_2538_, v_onDidChange_2539_);
return v___x_2544_;
}
else
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
lean_dec_ref(v_onDidChange_2539_);
lean_dec_ref(v_handler_2538_);
lean_dec(v_initState_2537_);
lean_dec(v_inst_2536_);
lean_dec(v_completeness_2535_);
v___x_2545_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0));
v___x_2546_ = lean_string_append(v___x_2545_, v_method_2534_);
lean_dec_ref(v_method_2534_);
v___x_2547_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_2548_ = lean_string_append(v___x_2546_, v___x_2547_);
v___x_2549_ = lean_mk_io_user_error(v___x_2548_);
v___x_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_method_2551_, lean_object* v_completeness_2552_, lean_object* v_inst_2553_, lean_object* v_initState_2554_, lean_object* v_handler_2555_, lean_object* v_onDidChange_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2551_, v_completeness_2552_, v_inst_2553_, v_initState_2554_, v_handler_2555_, v_onDidChange_2556_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(lean_object* v_method_2559_, lean_object* v_refreshMethod_2560_, lean_object* v_refreshIntervalMs_2561_, lean_object* v_inst_2562_, lean_object* v_initState_2563_, lean_object* v_handler_2564_, lean_object* v_onDidChange_2565_){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v_refreshMethod_2560_);
lean_ctor_set(v___x_2567_, 1, v_refreshIntervalMs_2561_);
v___x_2568_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2559_, v___x_2567_, v_inst_2562_, v_initState_2563_, v_handler_2564_, v_onDidChange_2565_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_method_2569_, lean_object* v_refreshMethod_2570_, lean_object* v_refreshIntervalMs_2571_, lean_object* v_inst_2572_, lean_object* v_initState_2573_, lean_object* v_handler_2574_, lean_object* v_onDidChange_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2569_, v_refreshMethod_2570_, v_refreshIntervalMs_2571_, v_inst_2572_, v_initState_2573_, v_handler_2574_, v_onDidChange_2575_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v___x_2583_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_));
v___x_2584_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2585_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2586_ = lean_unsigned_to_nat(500u);
v___x_2587_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init));
v___x_2588_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2589_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2590_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v___x_2584_, v___x_2585_, v___x_2586_, v___x_2583_, v___x_2587_, v___x_2588_, v___x_2589_);
return v___x_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2____boxed(lean_object* v_a_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(lean_object* v_method_2593_, lean_object* v_refreshMethod_2594_, lean_object* v_refreshIntervalMs_2595_, lean_object* v_stateType_2596_, lean_object* v_inst_2597_, lean_object* v_initState_2598_, lean_object* v_handler_2599_, lean_object* v_onDidChange_2600_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2593_, v_refreshMethod_2594_, v_refreshIntervalMs_2595_, v_inst_2597_, v_initState_2598_, v_handler_2599_, v_onDidChange_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2603_, lean_object* v_refreshMethod_2604_, lean_object* v_refreshIntervalMs_2605_, lean_object* v_stateType_2606_, lean_object* v_inst_2607_, lean_object* v_initState_2608_, lean_object* v_handler_2609_, lean_object* v_onDidChange_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(v_method_2603_, v_refreshMethod_2604_, v_refreshIntervalMs_2605_, v_stateType_2606_, v_inst_2607_, v_initState_2608_, v_handler_2609_, v_onDidChange_2610_);
return v_res_2612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_2613_, lean_object* v_completeness_2614_, lean_object* v_stateType_2615_, lean_object* v_inst_2616_, lean_object* v_initState_2617_, lean_object* v_handler_2618_, lean_object* v_onDidChange_2619_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2613_, v_completeness_2614_, v_inst_2616_, v_initState_2617_, v_handler_2618_, v_onDidChange_2619_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_method_2622_, lean_object* v_completeness_2623_, lean_object* v_stateType_2624_, lean_object* v_inst_2625_, lean_object* v_initState_2626_, lean_object* v_handler_2627_, lean_object* v_onDidChange_2628_, lean_object* v_a_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(v_method_2622_, v_completeness_2623_, v_stateType_2624_, v_inst_2625_, v_initState_2626_, v_handler_2627_, v_onDidChange_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2631_, lean_object* v_x_2632_, lean_object* v_x_2633_){
_start:
{
uint8_t v___x_2634_; 
v___x_2634_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2632_, v_x_2633_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2635_, lean_object* v_x_2636_, lean_object* v_x_2637_){
_start:
{
uint8_t v_res_2638_; lean_object* v_r_2639_; 
v_res_2638_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2635_, v_x_2636_, v_x_2637_);
lean_dec_ref(v_x_2637_);
lean_dec_ref(v_x_2636_);
v_r_2639_ = lean_box(v_res_2638_);
return v_r_2639_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b1_2640_, lean_object* v_00_u03b2_2641_, lean_object* v_mutex_2642_, lean_object* v_k_2643_, lean_object* v___y_2644_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2642_, v_k_2643_, v___y_2644_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2647_, lean_object* v_00_u03b2_2648_, lean_object* v_mutex_2649_, lean_object* v_k_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(v_00_u03b1_2647_, v_00_u03b2_2648_, v_mutex_2649_, v_k_2650_, v___y_2651_);
lean_dec_ref(v___y_2651_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_method_2654_, lean_object* v_completeness_2655_, lean_object* v_stateType_2656_, lean_object* v_inst_2657_, lean_object* v_initState_2658_, lean_object* v_handler_2659_, lean_object* v_onDidChange_2660_){
_start:
{
lean_object* v___x_2662_; 
v___x_2662_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2654_, v_completeness_2655_, v_inst_2657_, v_initState_2658_, v_handler_2659_, v_onDidChange_2660_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_method_2663_, lean_object* v_completeness_2664_, lean_object* v_stateType_2665_, lean_object* v_inst_2666_, lean_object* v_initState_2667_, lean_object* v_handler_2668_, lean_object* v_onDidChange_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_method_2663_, v_completeness_2664_, v_stateType_2665_, v_inst_2666_, v_initState_2667_, v_handler_2668_, v_onDidChange_2669_);
return v_res_2671_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2672_, lean_object* v_x_2673_, size_t v_x_2674_, lean_object* v_x_2675_){
_start:
{
uint8_t v___x_2676_; 
v___x_2676_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2673_, v_x_2674_, v_x_2675_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2677_, lean_object* v_x_2678_, lean_object* v_x_2679_, lean_object* v_x_2680_){
_start:
{
size_t v_x_3474__boxed_2681_; uint8_t v_res_2682_; lean_object* v_r_2683_; 
v_x_3474__boxed_2681_ = lean_unbox_usize(v_x_2679_);
lean_dec(v_x_2679_);
v_res_2682_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2677_, v_x_2678_, v_x_3474__boxed_2681_, v_x_2680_);
lean_dec_ref(v_x_2680_);
lean_dec_ref(v_x_2678_);
v_r_2683_ = lean_box(v_res_2682_);
return v_r_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_params_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v___x_2687_; 
v___x_2687_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2684_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_params_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_params_2688_, v_a_2689_);
lean_dec_ref(v_a_2689_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_2692_, lean_object* v_x_2693_, lean_object* v_x_2694_, lean_object* v_x_2695_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v_x_2693_, v_x_2694_, v_x_2695_);
return v___x_2696_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2697_, lean_object* v_keys_2698_, lean_object* v_vals_2699_, lean_object* v_heq_2700_, lean_object* v_i_2701_, lean_object* v_k_2702_){
_start:
{
uint8_t v___x_2703_; 
v___x_2703_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2698_, v_i_2701_, v_k_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2704_, lean_object* v_keys_2705_, lean_object* v_vals_2706_, lean_object* v_heq_2707_, lean_object* v_i_2708_, lean_object* v_k_2709_){
_start:
{
uint8_t v_res_2710_; lean_object* v_r_2711_; 
v_res_2710_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_2704_, v_keys_2705_, v_vals_2706_, v_heq_2707_, v_i_2708_, v_k_2709_);
lean_dec_ref(v_k_2709_);
lean_dec_ref(v_vals_2706_);
lean_dec_ref(v_keys_2705_);
v_r_2711_ = lean_box(v_res_2710_);
return v_r_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_2712_, lean_object* v_x_2713_, size_t v_x_2714_, size_t v_x_2715_, lean_object* v_x_2716_, lean_object* v_x_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_2713_, v_x_2714_, v_x_2715_, v_x_2716_, v_x_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2719_, lean_object* v_x_2720_, lean_object* v_x_2721_, lean_object* v_x_2722_, lean_object* v_x_2723_, lean_object* v_x_2724_){
_start:
{
size_t v_x_3500__boxed_2725_; size_t v_x_3501__boxed_2726_; lean_object* v_res_2727_; 
v_x_3500__boxed_2725_ = lean_unbox_usize(v_x_2721_);
lean_dec(v_x_2721_);
v_x_3501__boxed_2726_ = lean_unbox_usize(v_x_2722_);
lean_dec(v_x_2722_);
v_res_2727_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(v_00_u03b2_2719_, v_x_2720_, v_x_3500__boxed_2725_, v_x_3501__boxed_2726_, v_x_2723_, v_x_2724_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_2728_, lean_object* v_n_2729_, lean_object* v_k_2730_, lean_object* v_v_2731_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v_n_2729_, v_k_2730_, v_v_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(lean_object* v_00_u03b2_2733_, size_t v_depth_2734_, lean_object* v_keys_2735_, lean_object* v_vals_2736_, lean_object* v_heq_2737_, lean_object* v_i_2738_, lean_object* v_entries_2739_){
_start:
{
lean_object* v___x_2740_; 
v___x_2740_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_2734_, v_keys_2735_, v_vals_2736_, v_i_2738_, v_entries_2739_);
return v___x_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___boxed(lean_object* v_00_u03b2_2741_, lean_object* v_depth_2742_, lean_object* v_keys_2743_, lean_object* v_vals_2744_, lean_object* v_heq_2745_, lean_object* v_i_2746_, lean_object* v_entries_2747_){
_start:
{
size_t v_depth_boxed_2748_; lean_object* v_res_2749_; 
v_depth_boxed_2748_ = lean_unbox_usize(v_depth_2742_);
lean_dec(v_depth_2742_);
v_res_2749_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(v_00_u03b2_2741_, v_depth_boxed_2748_, v_keys_2743_, v_vals_2744_, v_heq_2745_, v_i_2746_, v_entries_2747_);
lean_dec_ref(v_vals_2744_);
lean_dec_ref(v_keys_2743_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_2750_, lean_object* v_x_2751_, lean_object* v_x_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_x_2751_, v_x_2752_, v_x_2753_, v_x_2754_);
return v___x_2755_;
}
}
lean_object* runtime_initialize_Lean_Server_GoTo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_InlayHints(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Server_GoTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_InlayHints(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Server_GoTo(uint8_t builtin);
lean_object* initialize_Lean_Server_Requests(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_InlayHints(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_GoTo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Requests(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_InlayHints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_InlayHints(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_InlayHints(builtin);
}
#ifdef __cplusplus
}
#endif
