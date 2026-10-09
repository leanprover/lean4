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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t lean_string_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_instMonadEIO___redArg();
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
uint8_t l_Lean_Elab_instBEqInlayHintTextEdit_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_initializing();
lean_object* lean_mk_io_user_error(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
extern lean_object* l_Lean_Server_statefulRequestHandlers;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Server_instInhabitedRequestError_default;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Elab.InfoTree.Util.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Util"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4_value;
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5;
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
lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation(lean_object* v_text_1_, lean_object* v_l_2_){
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
LEAN_EXPORT void l_Lean_Elab_InlayHintLinkLocation_toLspLocation_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_1_ = stack[0].m_obj;
lean_object* v_l_2_ = stack[1].m_obj;
lean_object* v_res_43_;
v_res_43_ = l_Lean_Elab_InlayHintLinkLocation_toLspLocation(v_text_1_, v_l_2_);
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLinkLocation_toLspLocation___boxed(lean_object* v_text_44_, lean_object* v_l_45_, lean_object* v_a_46_){
_start:
{
lean_object* v_res_47_; 
v_res_47_ = l_Lean_Elab_InlayHintLinkLocation_toLspLocation(v_text_44_, v_l_45_);
return v_res_47_;
}
}
lean_object* l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(lean_object* v_text_48_, lean_object* v_p_49_){
_start:
{
lean_object* v_value_51_; lean_object* v_tooltip_x3f_52_; lean_object* v_location_x3f_53_; lean_object* v___y_55_; lean_object* v___y_56_; lean_object* v_a_61_; 
v_value_51_ = lean_ctor_get(v_p_49_, 0);
lean_inc_ref(v_value_51_);
v_tooltip_x3f_52_ = lean_ctor_get(v_p_49_, 1);
lean_inc(v_tooltip_x3f_52_);
v_location_x3f_53_ = lean_ctor_get(v_p_49_, 2);
lean_inc(v_location_x3f_53_);
lean_dec_ref(v_p_49_);
if (lean_obj_tag(v_location_x3f_53_) == 0)
{
lean_object* v___x_74_; 
lean_dec_ref(v_text_48_);
v___x_74_ = lean_box(0);
v_a_61_ = v___x_74_;
goto v___jp_60_;
}
else
{
lean_object* v_val_75_; lean_object* v___x_76_; 
v_val_75_ = lean_ctor_get(v_location_x3f_53_, 0);
lean_inc(v_val_75_);
lean_dec_ref_known(v_location_x3f_53_, 1);
v___x_76_ = l_Lean_Elab_InlayHintLinkLocation_toLspLocation(v_text_48_, v_val_75_);
if (lean_obj_tag(v___x_76_) == 0)
{
lean_object* v_a_77_; 
v_a_77_ = lean_ctor_get(v___x_76_, 0);
lean_inc(v_a_77_);
lean_dec_ref_known(v___x_76_, 1);
v_a_61_ = v_a_77_;
goto v___jp_60_;
}
else
{
lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_85_; 
lean_dec(v_tooltip_x3f_52_);
lean_dec_ref(v_value_51_);
v_a_78_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_85_ == 0)
{
v___x_80_ = v___x_76_;
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_76_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_85_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_83_; 
if (v_isShared_81_ == 0)
{
v___x_83_ = v___x_80_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_a_78_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
v___jp_54_:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_box(0);
v___x_58_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_58_, 0, v_value_51_);
lean_ctor_set(v___x_58_, 1, v___y_56_);
lean_ctor_set(v___x_58_, 2, v___y_55_);
lean_ctor_set(v___x_58_, 3, v___x_57_);
v___x_59_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_59_, 0, v___x_58_);
return v___x_59_;
}
v___jp_60_:
{
if (lean_obj_tag(v_tooltip_x3f_52_) == 0)
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
v___y_55_ = v_a_61_;
v___y_56_ = v___x_62_;
goto v___jp_54_;
}
else
{
lean_object* v_val_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_73_; 
v_val_63_ = lean_ctor_get(v_tooltip_x3f_52_, 0);
v_isSharedCheck_73_ = !lean_is_exclusive(v_tooltip_x3f_52_);
if (v_isSharedCheck_73_ == 0)
{
v___x_65_ = v_tooltip_x3f_52_;
v_isShared_66_ = v_isSharedCheck_73_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_val_63_);
lean_dec(v_tooltip_x3f_52_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_73_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
uint8_t v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_71_; 
v___x_67_ = 1;
v___x_68_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_68_, 0, v_val_63_);
lean_ctor_set_uint8(v___x_68_, sizeof(void*)*1, v___x_67_);
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v___x_69_);
v___x_71_ = v___x_65_;
goto v_reusejp_70_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_69_);
v___x_71_ = v_reuseFailAlloc_72_;
goto v_reusejp_70_;
}
v_reusejp_70_:
{
v___y_55_ = v_a_61_;
v___y_56_ = v___x_71_;
goto v___jp_54_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_48_ = stack[0].m_obj;
lean_object* v_p_49_ = stack[1].m_obj;
lean_object* v_res_86_;
v_res_86_ = l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(v_text_48_, v_p_49_);
stack->m_obj
 = v_res_86_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart___boxed(lean_object* v_text_87_, lean_object* v_p_88_, lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(v_text_87_, v_p_88_);
return v_res_90_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(lean_object* v_text_91_, size_t v_sz_92_, size_t v_i_93_, lean_object* v_bs_94_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = lean_usize_dec_lt(v_i_93_, v_sz_92_);
if (v___x_96_ == 0)
{
lean_object* v___x_97_; 
lean_dec_ref(v_text_91_);
v___x_97_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_97_, 0, v_bs_94_);
return v___x_97_;
}
else
{
lean_object* v_v_98_; lean_object* v___x_99_; lean_object* v_bs_x27_100_; lean_object* v___x_101_; 
v_v_98_ = lean_array_uget(v_bs_94_, v_i_93_);
v___x_99_ = lean_unsigned_to_nat(0u);
v_bs_x27_100_ = lean_array_uset(v_bs_94_, v_i_93_, v___x_99_);
lean_inc_ref(v_text_91_);
v___x_101_ = l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(v_text_91_, v_v_98_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_101_, 1);
v___x_103_ = ((size_t)1ULL);
v___x_104_ = lean_usize_add(v_i_93_, v___x_103_);
v___x_105_ = lean_array_uset(v_bs_x27_100_, v_i_93_, v_a_102_);
v_i_93_ = v___x_104_;
v_bs_94_ = v___x_105_;
goto _start;
}
else
{
lean_object* v_a_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_114_; 
lean_dec_ref(v_bs_x27_100_);
lean_dec_ref(v_text_91_);
v_a_107_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_114_ == 0)
{
v___x_109_ = v___x_101_;
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_a_107_);
lean_dec(v___x_101_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_114_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_112_; 
if (v_isShared_110_ == 0)
{
v___x_112_ = v___x_109_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_a_107_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_91_ = stack[0].m_obj;
size_t v_sz_92_ = stack[1].m_num;
size_t v_i_93_ = stack[2].m_num;
lean_object* v_bs_94_ = stack[3].m_obj;
lean_object* v_res_115_;
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(v_text_91_, v_sz_92_, v_i_93_, v_bs_94_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0___boxed(lean_object* v_text_116_, lean_object* v_sz_117_, lean_object* v_i_118_, lean_object* v_bs_119_, lean_object* v___y_120_){
_start:
{
size_t v_sz_boxed_121_; size_t v_i_boxed_122_; lean_object* v_res_123_; 
v_sz_boxed_121_ = lean_unbox_usize(v_sz_117_);
lean_dec(v_sz_117_);
v_i_boxed_122_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_res_123_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(v_text_116_, v_sz_boxed_121_, v_i_boxed_122_, v_bs_119_);
return v_res_123_;
}
}
lean_object* l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(lean_object* v_text_124_, lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_object* v_n_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_135_; 
lean_dec_ref(v_text_124_);
v_n_127_ = lean_ctor_get(v_x_125_, 0);
v_isSharedCheck_135_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_135_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_n_127_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_135_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_132_; 
if (v_isShared_130_ == 0)
{
v___x_132_ = v___x_129_;
goto v_reusejp_131_;
}
else
{
lean_object* v_reuseFailAlloc_134_; 
v_reuseFailAlloc_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_134_, 0, v_n_127_);
v___x_132_ = v_reuseFailAlloc_134_;
goto v_reusejp_131_;
}
v_reusejp_131_:
{
lean_object* v___x_133_; 
v___x_133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
return v___x_133_;
}
}
}
else
{
lean_object* v_p_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_162_; 
v_p_136_ = lean_ctor_get(v_x_125_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_162_ == 0)
{
v___x_138_ = v_x_125_;
v_isShared_139_ = v_isSharedCheck_162_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_p_136_);
lean_dec(v_x_125_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_162_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
size_t v_sz_140_; size_t v___x_141_; lean_object* v___x_142_; 
v_sz_140_ = lean_array_size(v_p_136_);
v___x_141_ = ((size_t)0ULL);
v___x_142_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintLabel_toLspInlayHintLabel_spec__0(v_text_124_, v_sz_140_, v___x_141_, v_p_136_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_153_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_153_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_153_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v_a_143_);
v___x_148_ = v___x_138_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_152_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_150_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 0, v___x_148_);
v___x_150_ = v___x_145_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_148_);
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
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_del_object(v___x_138_);
v_a_154_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_142_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_142_);
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
}
}
}
LEAN_EXPORT void l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_124_ = stack[0].m_obj;
lean_object* v_x_125_ = stack[1].m_obj;
lean_object* v_res_163_;
v_res_163_ = l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(v_text_124_, v_x_125_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel___boxed(lean_object* v_text_164_, lean_object* v_x_165_, lean_object* v_a_166_){
_start:
{
lean_object* v_res_167_; 
v_res_167_ = l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(v_text_164_, v_x_165_);
return v_res_167_;
}
}
uint8_t l_Lean_Elab_InlayHintKind_toLspInlayHintKind(uint8_t v_x_168_){
_start:
{
if (v_x_168_ == 0)
{
uint8_t v___x_169_; 
v___x_169_ = 0;
return v___x_169_;
}
else
{
uint8_t v___x_170_; 
v___x_170_ = 1;
return v___x_170_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_InlayHintKind_toLspInlayHintKind_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_168_ = stack[0].m_num;
uint8_t v_res_171_;
v_res_171_ = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(v_x_168_);
stack->m_num = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintKind_toLspInlayHintKind___boxed(lean_object* v_x_172_){
_start:
{
uint8_t v_x_18__boxed_173_; uint8_t v_res_174_; lean_object* v_r_175_; 
v_x_18__boxed_173_ = lean_unbox(v_x_172_);
v_res_174_ = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(v_x_18__boxed_173_);
v_r_175_ = lean_box(v_res_174_);
return v_r_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(lean_object* v_text_176_, lean_object* v_e_177_){
_start:
{
lean_object* v_range_178_; lean_object* v_newText_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_range_178_ = lean_ctor_get(v_e_177_, 0);
lean_inc_ref(v_range_178_);
v_newText_179_ = lean_ctor_get(v_e_177_, 1);
lean_inc_ref(v_newText_179_);
lean_dec_ref(v_e_177_);
v___x_180_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_176_, v_range_178_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_182_, 0, v___x_180_);
lean_ctor_set(v___x_182_, 1, v_newText_179_);
lean_ctor_set(v___x_182_, 2, v___x_181_);
lean_ctor_set(v___x_182_, 3, v___x_181_);
return v___x_182_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(lean_object* v_text_183_, size_t v_sz_184_, size_t v_i_185_, lean_object* v_bs_186_){
_start:
{
uint8_t v___x_187_; 
v___x_187_ = lean_usize_dec_lt(v_i_185_, v_sz_184_);
if (v___x_187_ == 0)
{
lean_dec_ref(v_text_183_);
return v_bs_186_;
}
else
{
lean_object* v_v_188_; lean_object* v___x_189_; lean_object* v_bs_x27_190_; lean_object* v___x_191_; size_t v___x_192_; size_t v___x_193_; lean_object* v___x_194_; 
v_v_188_ = lean_array_uget(v_bs_186_, v_i_185_);
v___x_189_ = lean_unsigned_to_nat(0u);
v_bs_x27_190_ = lean_array_uset(v_bs_186_, v_i_185_, v___x_189_);
lean_inc_ref(v_text_183_);
v___x_191_ = l_Lean_Elab_InlayHintTextEdit_toLspTextEdit(v_text_183_, v_v_188_);
v___x_192_ = ((size_t)1ULL);
v___x_193_ = lean_usize_add(v_i_185_, v___x_192_);
v___x_194_ = lean_array_uset(v_bs_x27_190_, v_i_185_, v___x_191_);
v_i_185_ = v___x_193_;
v_bs_186_ = v___x_194_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_183_ = stack[0].m_obj;
size_t v_sz_184_ = stack[1].m_num;
size_t v_i_185_ = stack[2].m_num;
lean_object* v_bs_186_ = stack[3].m_obj;
lean_object* v_res_196_;
v_res_196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(v_text_183_, v_sz_184_, v_i_185_, v_bs_186_);
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0___boxed(lean_object* v_text_197_, lean_object* v_sz_198_, lean_object* v_i_199_, lean_object* v_bs_200_){
_start:
{
size_t v_sz_boxed_201_; size_t v_i_boxed_202_; lean_object* v_res_203_; 
v_sz_boxed_201_ = lean_unbox_usize(v_sz_198_);
lean_dec(v_sz_198_);
v_i_boxed_202_ = lean_unbox_usize(v_i_199_);
lean_dec(v_i_199_);
v_res_203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(v_text_197_, v_sz_boxed_201_, v_i_boxed_202_, v_bs_200_);
return v_res_203_;
}
}
lean_object* l_Lean_Elab_InlayHintInfo_toLspInlayHint(lean_object* v_text_204_, lean_object* v_i_205_){
_start:
{
lean_object* v_position_207_; lean_object* v_label_208_; lean_object* v_kind_x3f_209_; lean_object* v_textEdits_210_; lean_object* v_tooltip_x3f_211_; uint8_t v_paddingLeft_212_; uint8_t v_paddingRight_213_; lean_object* v___x_214_; 
v_position_207_ = lean_ctor_get(v_i_205_, 0);
lean_inc(v_position_207_);
v_label_208_ = lean_ctor_get(v_i_205_, 1);
lean_inc_ref(v_label_208_);
v_kind_x3f_209_ = lean_ctor_get(v_i_205_, 2);
lean_inc(v_kind_x3f_209_);
v_textEdits_210_ = lean_ctor_get(v_i_205_, 3);
lean_inc_ref(v_textEdits_210_);
v_tooltip_x3f_211_ = lean_ctor_get(v_i_205_, 4);
lean_inc(v_tooltip_x3f_211_);
v_paddingLeft_212_ = lean_ctor_get_uint8(v_i_205_, sizeof(void*)*5);
v_paddingRight_213_ = lean_ctor_get_uint8(v_i_205_, sizeof(void*)*5 + 1);
lean_dec_ref(v_i_205_);
lean_inc_ref(v_text_204_);
v___x_214_ = l_Lean_Elab_InlayHintLabel_toLspInlayHintLabel(v_text_204_, v_label_208_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_263_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_263_ == 0)
{
v___x_217_ = v___x_214_;
v_isShared_218_ = v_isSharedCheck_263_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_214_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_263_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___y_221_; lean_object* v___y_222_; lean_object* v___y_223_; lean_object* v___y_234_; 
lean_inc_ref(v_text_204_);
v___x_219_ = l_Lean_FileMap_utf8PosToLspPos(v_text_204_, v_position_207_);
lean_dec(v_position_207_);
if (lean_obj_tag(v_kind_x3f_209_) == 0)
{
lean_object* v___x_251_; 
v___x_251_ = lean_box(0);
v___y_234_ = v___x_251_;
goto v___jp_233_;
}
else
{
lean_object* v_val_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_262_; 
v_val_252_ = lean_ctor_get(v_kind_x3f_209_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_kind_x3f_209_);
if (v_isSharedCheck_262_ == 0)
{
v___x_254_ = v_kind_x3f_209_;
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_val_252_);
lean_dec(v_kind_x3f_209_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_262_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
uint8_t v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_256_ = lean_unbox(v_val_252_);
lean_dec(v_val_252_);
v___x_257_ = l_Lean_Elab_InlayHintKind_toLspInlayHintKind(v___x_256_);
v___x_258_ = lean_box(v___x_257_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_258_);
v___x_260_ = v___x_254_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
v___y_234_ = v___x_260_;
goto v___jp_233_;
}
}
}
v___jp_220_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_224_ = lean_box(v_paddingLeft_212_);
v___x_225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
v___x_226_ = lean_box(v_paddingRight_213_);
v___x_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_227_, 0, v___x_226_);
v___x_228_ = lean_box(0);
v___x_229_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_229_, 0, v___x_219_);
lean_ctor_set(v___x_229_, 1, v_a_215_);
lean_ctor_set(v___x_229_, 2, v___y_221_);
lean_ctor_set(v___x_229_, 3, v___y_222_);
lean_ctor_set(v___x_229_, 4, v___y_223_);
lean_ctor_set(v___x_229_, 5, v___x_225_);
lean_ctor_set(v___x_229_, 6, v___x_227_);
lean_ctor_set(v___x_229_, 7, v___x_228_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 0, v___x_229_);
v___x_231_ = v___x_217_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v___x_229_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
v___jp_233_:
{
size_t v_sz_235_; size_t v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v_sz_235_ = lean_array_size(v_textEdits_210_);
v___x_236_ = ((size_t)0ULL);
v___x_237_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_InlayHintInfo_toLspInlayHint_spec__0(v_text_204_, v_sz_235_, v___x_236_, v_textEdits_210_);
v___x_238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
if (lean_obj_tag(v_tooltip_x3f_211_) == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_box(0);
v___y_221_ = v___y_234_;
v___y_222_ = v___x_238_;
v___y_223_ = v___x_239_;
goto v___jp_220_;
}
else
{
lean_object* v_val_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_250_; 
v_val_240_ = lean_ctor_get(v_tooltip_x3f_211_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_tooltip_x3f_211_);
if (v_isSharedCheck_250_ == 0)
{
v___x_242_ = v_tooltip_x3f_211_;
v_isShared_243_ = v_isSharedCheck_250_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_val_240_);
lean_dec(v_tooltip_x3f_211_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_250_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
uint8_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_244_ = 1;
v___x_245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_245_, 0, v_val_240_);
lean_ctor_set_uint8(v___x_245_, sizeof(void*)*1, v___x_244_);
v___x_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 0, v___x_246_);
v___x_248_ = v___x_242_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_246_);
v___x_248_ = v_reuseFailAlloc_249_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
v___y_221_ = v___y_234_;
v___y_222_ = v___x_238_;
v___y_223_ = v___x_248_;
goto v___jp_220_;
}
}
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_tooltip_x3f_211_);
lean_dec_ref(v_textEdits_210_);
lean_dec(v_kind_x3f_209_);
lean_dec(v_position_207_);
lean_dec_ref(v_text_204_);
v_a_264_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_214_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_214_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_InlayHintInfo_toLspInlayHint_0interp(lean_interpreter_value* stack)
{
lean_object* v_text_204_ = stack[0].m_obj;
lean_object* v_i_205_ = stack[1].m_obj;
lean_object* v_res_272_;
v_res_272_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v_text_204_, v_i_205_);
stack->m_obj
 = v_res_272_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InlayHintInfo_toLspInlayHint___boxed(lean_object* v_text_273_, lean_object* v_i_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v_text_273_, v_i_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__0(lean_object* v_a_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = lean_nat_to_int(v_a_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(lean_object* v_msg_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = lean_panic_fn_borrowed(v___x_280_, v_msg_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(lean_object* v_range_287_, lean_object* v_byteOffset_288_, lean_object* v_p_289_){
_start:
{
lean_object* v_start_290_; lean_object* v_stop_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
v_start_290_ = lean_ctor_get(v_range_287_, 0);
lean_inc(v_start_290_);
v_stop_291_ = lean_ctor_get(v_range_287_, 1);
lean_inc(v_stop_291_);
lean_dec_ref(v_range_287_);
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = lean_nat_add(v_stop_291_, v___x_292_);
v___x_294_ = lean_nat_dec_le(v___x_293_, v_p_289_);
lean_dec(v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; uint8_t v___x_296_; 
v___x_295_ = lean_nat_add(v_p_289_, v___x_292_);
v___x_296_ = lean_nat_dec_le(v___x_295_, v_start_290_);
lean_dec(v___x_295_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_298_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1));
v___x_299_ = lean_unsigned_to_nat(87u);
v___x_300_ = lean_unsigned_to_nat(6u);
v___x_301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2));
v___x_302_ = l_Nat_reprFast(v_p_289_);
v___x_303_ = lean_string_append(v___x_301_, v___x_302_);
lean_dec_ref(v___x_302_);
v___x_304_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3));
v___x_305_ = lean_string_append(v___x_303_, v___x_304_);
v___x_306_ = l_Nat_reprFast(v_start_290_);
v___x_307_ = lean_string_append(v___x_305_, v___x_306_);
lean_dec_ref(v___x_306_);
v___x_308_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4));
v___x_309_ = lean_string_append(v___x_307_, v___x_308_);
v___x_310_ = l_Nat_reprFast(v_stop_291_);
v___x_311_ = lean_string_append(v___x_309_, v___x_310_);
lean_dec_ref(v___x_310_);
v___x_312_ = l_mkPanicMessageWithDecl(v___x_297_, v___x_298_, v___x_299_, v___x_300_, v___x_311_);
lean_dec_ref(v___x_311_);
v___x_313_ = l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(v___x_312_);
return v___x_313_;
}
else
{
lean_dec(v_stop_291_);
lean_dec(v_start_290_);
return v_p_289_;
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_stop_291_);
lean_dec(v_start_290_);
v___x_314_ = lean_nat_to_int(v_p_289_);
v___x_315_ = lean_int_add(v___x_314_, v_byteOffset_288_);
lean_dec(v___x_314_);
v___x_316_ = l_Int_toNat(v___x_315_);
lean_dec(v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___boxed(lean_object* v_range_317_, lean_object* v_byteOffset_318_, lean_object* v_p_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_317_, v_byteOffset_318_, v_p_319_);
lean_dec(v_byteOffset_318_);
return v_res_320_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(lean_object* v_hintMod_321_, lean_object* v_range_322_, lean_object* v_byteOffset_323_, size_t v_sz_324_, size_t v_i_325_, lean_object* v_bs_326_){
_start:
{
uint8_t v___x_327_; 
v___x_327_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_327_ == 0)
{
lean_dec_ref(v_range_322_);
return v_bs_326_;
}
else
{
lean_object* v_v_328_; lean_object* v_value_329_; lean_object* v_tooltip_x3f_330_; lean_object* v_location_x3f_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_374_; 
v_v_328_ = lean_array_uget(v_bs_326_, v_i_325_);
v_value_329_ = lean_ctor_get(v_v_328_, 0);
v_tooltip_x3f_330_ = lean_ctor_get(v_v_328_, 1);
v_location_x3f_331_ = lean_ctor_get(v_v_328_, 2);
v_isSharedCheck_374_ = !lean_is_exclusive(v_v_328_);
if (v_isSharedCheck_374_ == 0)
{
v___x_333_ = v_v_328_;
v_isShared_334_ = v_isSharedCheck_374_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_location_x3f_331_);
lean_inc(v_tooltip_x3f_330_);
lean_inc(v_value_329_);
lean_dec(v_v_328_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_374_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v_bs_x27_336_; lean_object* v___y_338_; lean_object* v___y_344_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v_bs_x27_336_ = lean_array_uset(v_bs_326_, v_i_325_, v___x_335_);
if (lean_obj_tag(v_location_x3f_331_) == 0)
{
lean_object* v___x_349_; 
lean_del_object(v___x_333_);
v___x_349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_349_, 0, v_value_329_);
lean_ctor_set(v___x_349_, 1, v_tooltip_x3f_330_);
lean_ctor_set(v___x_349_, 2, v_location_x3f_331_);
v___y_338_ = v___x_349_;
goto v___jp_337_;
}
else
{
lean_object* v_val_350_; lean_object* v_module_351_; lean_object* v_range_352_; uint8_t v___x_353_; 
v_val_350_ = lean_ctor_get(v_location_x3f_331_, 0);
lean_inc(v_val_350_);
lean_dec_ref_known(v_location_x3f_331_, 1);
v_module_351_ = lean_ctor_get(v_val_350_, 0);
v_range_352_ = lean_ctor_get(v_val_350_, 1);
lean_inc_ref(v_range_352_);
v___x_353_ = lean_name_eq(v_module_351_, v_hintMod_321_);
if (v___x_353_ == 0)
{
lean_dec_ref(v_range_352_);
v___y_344_ = v_val_350_;
goto v___jp_343_;
}
else
{
lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_371_; 
lean_inc(v_module_351_);
v_isSharedCheck_371_ = !lean_is_exclusive(v_val_350_);
if (v_isSharedCheck_371_ == 0)
{
lean_object* v_unused_372_; lean_object* v_unused_373_; 
v_unused_372_ = lean_ctor_get(v_val_350_, 1);
lean_dec(v_unused_372_);
v_unused_373_ = lean_ctor_get(v_val_350_, 0);
lean_dec(v_unused_373_);
v___x_355_ = v_val_350_;
v_isShared_356_ = v_isSharedCheck_371_;
goto v_resetjp_354_;
}
else
{
lean_dec(v_val_350_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_371_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v_start_357_; lean_object* v_stop_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_370_; 
v_start_357_ = lean_ctor_get(v_range_352_, 0);
v_stop_358_ = lean_ctor_get(v_range_352_, 1);
v_isSharedCheck_370_ = !lean_is_exclusive(v_range_352_);
if (v_isSharedCheck_370_ == 0)
{
v___x_360_ = v_range_352_;
v_isShared_361_ = v_isSharedCheck_370_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_stop_358_);
lean_inc(v_start_357_);
lean_dec(v_range_352_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_370_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_365_; 
lean_inc_ref_n(v_range_322_, 2);
v___x_362_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_322_, v_byteOffset_323_, v_start_357_);
v___x_363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_322_, v_byteOffset_323_, v_stop_358_);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_363_);
lean_ctor_set(v___x_360_, 0, v___x_362_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_362_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_369_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
lean_object* v___x_367_; 
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v___x_365_);
v___x_367_ = v___x_355_;
goto v_reusejp_366_;
}
else
{
lean_object* v_reuseFailAlloc_368_; 
v_reuseFailAlloc_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_368_, 0, v_module_351_);
lean_ctor_set(v_reuseFailAlloc_368_, 1, v___x_365_);
v___x_367_ = v_reuseFailAlloc_368_;
goto v_reusejp_366_;
}
v_reusejp_366_:
{
v___y_344_ = v___x_367_;
goto v___jp_343_;
}
}
}
}
}
}
v___jp_337_:
{
size_t v___x_339_; size_t v___x_340_; lean_object* v___x_341_; 
v___x_339_ = ((size_t)1ULL);
v___x_340_ = lean_usize_add(v_i_325_, v___x_339_);
v___x_341_ = lean_array_uset(v_bs_x27_336_, v_i_325_, v___y_338_);
v_i_325_ = v___x_340_;
v_bs_326_ = v___x_341_;
goto _start;
}
v___jp_343_:
{
lean_object* v___x_345_; lean_object* v___x_347_; 
v___x_345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_345_, 0, v___y_344_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 2, v___x_345_);
v___x_347_ = v___x_333_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_348_; 
v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_348_, 0, v_value_329_);
lean_ctor_set(v_reuseFailAlloc_348_, 1, v_tooltip_x3f_330_);
lean_ctor_set(v_reuseFailAlloc_348_, 2, v___x_345_);
v___x_347_ = v_reuseFailAlloc_348_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
v___y_338_ = v___x_347_;
goto v___jp_337_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_hintMod_321_ = stack[0].m_obj;
lean_object* v_range_322_ = stack[1].m_obj;
lean_object* v_byteOffset_323_ = stack[2].m_obj;
size_t v_sz_324_ = stack[3].m_num;
size_t v_i_325_ = stack[4].m_num;
lean_object* v_bs_326_ = stack[5].m_obj;
lean_object* v_res_375_;
v_res_375_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_321_, v_range_322_, v_byteOffset_323_, v_sz_324_, v_i_325_, v_bs_326_);
stack->m_obj
 = v_res_375_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4___boxed(lean_object* v_hintMod_376_, lean_object* v_range_377_, lean_object* v_byteOffset_378_, lean_object* v_sz_379_, lean_object* v_i_380_, lean_object* v_bs_381_){
_start:
{
size_t v_sz_boxed_382_; size_t v_i_boxed_383_; lean_object* v_res_384_; 
v_sz_boxed_382_ = lean_unbox_usize(v_sz_379_);
lean_dec(v_sz_379_);
v_i_boxed_383_ = lean_unbox_usize(v_i_380_);
lean_dec(v_i_380_);
v_res_384_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_376_, v_range_377_, v_byteOffset_378_, v_sz_boxed_382_, v_i_boxed_383_, v_bs_381_);
lean_dec(v_byteOffset_378_);
lean_dec(v_hintMod_376_);
return v_res_384_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(lean_object* v_hintMod_385_, lean_object* v_range_386_, lean_object* v_byteOffset_387_, size_t v_sz_388_, size_t v_i_389_, lean_object* v_bs_390_){
_start:
{
uint8_t v___x_391_; 
v___x_391_ = lean_usize_dec_lt(v_i_389_, v_sz_388_);
if (v___x_391_ == 0)
{
lean_dec_ref(v_range_386_);
return v_bs_390_;
}
else
{
lean_object* v_v_392_; lean_object* v_value_393_; lean_object* v_tooltip_x3f_394_; lean_object* v_location_x3f_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_438_; 
v_v_392_ = lean_array_uget(v_bs_390_, v_i_389_);
v_value_393_ = lean_ctor_get(v_v_392_, 0);
v_tooltip_x3f_394_ = lean_ctor_get(v_v_392_, 1);
v_location_x3f_395_ = lean_ctor_get(v_v_392_, 2);
v_isSharedCheck_438_ = !lean_is_exclusive(v_v_392_);
if (v_isSharedCheck_438_ == 0)
{
v___x_397_ = v_v_392_;
v_isShared_398_ = v_isSharedCheck_438_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_location_x3f_395_);
lean_inc(v_tooltip_x3f_394_);
lean_inc(v_value_393_);
lean_dec(v_v_392_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_438_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v_bs_x27_400_; lean_object* v___y_402_; lean_object* v___y_408_; 
v___x_399_ = lean_unsigned_to_nat(0u);
v_bs_x27_400_ = lean_array_uset(v_bs_390_, v_i_389_, v___x_399_);
if (lean_obj_tag(v_location_x3f_395_) == 0)
{
lean_object* v___x_413_; 
lean_del_object(v___x_397_);
v___x_413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_413_, 0, v_value_393_);
lean_ctor_set(v___x_413_, 1, v_tooltip_x3f_394_);
lean_ctor_set(v___x_413_, 2, v_location_x3f_395_);
v___y_402_ = v___x_413_;
goto v___jp_401_;
}
else
{
lean_object* v_val_414_; lean_object* v_module_415_; lean_object* v_range_416_; uint8_t v___x_417_; 
v_val_414_ = lean_ctor_get(v_location_x3f_395_, 0);
lean_inc(v_val_414_);
lean_dec_ref_known(v_location_x3f_395_, 1);
v_module_415_ = lean_ctor_get(v_val_414_, 0);
v_range_416_ = lean_ctor_get(v_val_414_, 1);
lean_inc_ref(v_range_416_);
v___x_417_ = lean_name_eq(v_module_415_, v_hintMod_385_);
if (v___x_417_ == 0)
{
lean_dec_ref(v_range_416_);
v___y_408_ = v_val_414_;
goto v___jp_407_;
}
else
{
lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_435_; 
lean_inc(v_module_415_);
v_isSharedCheck_435_ = !lean_is_exclusive(v_val_414_);
if (v_isSharedCheck_435_ == 0)
{
lean_object* v_unused_436_; lean_object* v_unused_437_; 
v_unused_436_ = lean_ctor_get(v_val_414_, 1);
lean_dec(v_unused_436_);
v_unused_437_ = lean_ctor_get(v_val_414_, 0);
lean_dec(v_unused_437_);
v___x_419_ = v_val_414_;
v_isShared_420_ = v_isSharedCheck_435_;
goto v_resetjp_418_;
}
else
{
lean_dec(v_val_414_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_435_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v_start_421_; lean_object* v_stop_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_434_; 
v_start_421_ = lean_ctor_get(v_range_416_, 0);
v_stop_422_ = lean_ctor_get(v_range_416_, 1);
v_isSharedCheck_434_ = !lean_is_exclusive(v_range_416_);
if (v_isSharedCheck_434_ == 0)
{
v___x_424_ = v_range_416_;
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_stop_422_);
lean_inc(v_start_421_);
lean_dec(v_range_416_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_434_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
lean_inc_ref_n(v_range_386_, 2);
v___x_426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_386_, v_byteOffset_387_, v_start_421_);
v___x_427_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_386_, v_byteOffset_387_, v_stop_422_);
if (v_isShared_425_ == 0)
{
lean_ctor_set(v___x_424_, 1, v___x_427_);
lean_ctor_set(v___x_424_, 0, v___x_426_);
v___x_429_ = v___x_424_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_433_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_431_; 
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 1, v___x_429_);
v___x_431_ = v___x_419_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_module_415_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
v___y_408_ = v___x_431_;
goto v___jp_407_;
}
}
}
}
}
}
v___jp_401_:
{
size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_i_389_, v___x_403_);
v___x_405_ = lean_array_uset(v_bs_x27_400_, v_i_389_, v___y_402_);
v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_385_, v_range_386_, v_byteOffset_387_, v_sz_388_, v___x_404_, v___x_405_);
return v___x_406_;
}
v___jp_407_:
{
lean_object* v___x_409_; lean_object* v___x_411_; 
v___x_409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_409_, 0, v___y_408_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 2, v___x_409_);
v___x_411_ = v___x_397_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_value_393_);
lean_ctor_set(v_reuseFailAlloc_412_, 1, v_tooltip_x3f_394_);
lean_ctor_set(v_reuseFailAlloc_412_, 2, v___x_409_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
v___y_402_ = v___x_411_;
goto v___jp_401_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_hintMod_385_ = stack[0].m_obj;
lean_object* v_range_386_ = stack[1].m_obj;
lean_object* v_byteOffset_387_ = stack[2].m_obj;
size_t v_sz_388_ = stack[3].m_num;
size_t v_i_389_ = stack[4].m_num;
lean_object* v_bs_390_ = stack[5].m_obj;
lean_object* v_res_439_;
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_385_, v_range_386_, v_byteOffset_387_, v_sz_388_, v_i_389_, v_bs_390_);
stack->m_obj
 = v_res_439_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3___boxed(lean_object* v_hintMod_440_, lean_object* v_range_441_, lean_object* v_byteOffset_442_, lean_object* v_sz_443_, lean_object* v_i_444_, lean_object* v_bs_445_){
_start:
{
size_t v_sz_boxed_446_; size_t v_i_boxed_447_; lean_object* v_res_448_; 
v_sz_boxed_446_ = lean_unbox_usize(v_sz_443_);
lean_dec(v_sz_443_);
v_i_boxed_447_ = lean_unbox_usize(v_i_444_);
lean_dec(v_i_444_);
v_res_448_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_440_, v_range_441_, v_byteOffset_442_, v_sz_boxed_446_, v_i_boxed_447_, v_bs_445_);
lean_dec(v_byteOffset_442_);
lean_dec(v_hintMod_440_);
return v_res_448_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(lean_object* v_range_449_, lean_object* v_byteOffset_450_, size_t v_sz_451_, size_t v_i_452_, lean_object* v_bs_453_){
_start:
{
uint8_t v___x_454_; 
v___x_454_ = lean_usize_dec_lt(v_i_452_, v_sz_451_);
if (v___x_454_ == 0)
{
lean_dec_ref(v_range_449_);
return v_bs_453_;
}
else
{
lean_object* v_v_455_; lean_object* v_range_456_; lean_object* v_newText_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_481_; 
v_v_455_ = lean_array_uget(v_bs_453_, v_i_452_);
v_range_456_ = lean_ctor_get(v_v_455_, 0);
v_newText_457_ = lean_ctor_get(v_v_455_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_v_455_);
if (v_isSharedCheck_481_ == 0)
{
v___x_459_ = v_v_455_;
v_isShared_460_ = v_isSharedCheck_481_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_newText_457_);
lean_inc(v_range_456_);
lean_dec(v_v_455_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_481_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v_start_461_; lean_object* v_stop_462_; lean_object* v___x_464_; uint8_t v_isShared_465_; uint8_t v_isSharedCheck_480_; 
v_start_461_ = lean_ctor_get(v_range_456_, 0);
v_stop_462_ = lean_ctor_get(v_range_456_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_range_456_);
if (v_isSharedCheck_480_ == 0)
{
v___x_464_ = v_range_456_;
v_isShared_465_ = v_isSharedCheck_480_;
goto v_resetjp_463_;
}
else
{
lean_inc(v_stop_462_);
lean_inc(v_start_461_);
lean_dec(v_range_456_);
v___x_464_ = lean_box(0);
v_isShared_465_ = v_isSharedCheck_480_;
goto v_resetjp_463_;
}
v_resetjp_463_:
{
lean_object* v___x_466_; lean_object* v_bs_x27_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_471_; 
v___x_466_ = lean_unsigned_to_nat(0u);
v_bs_x27_467_ = lean_array_uset(v_bs_453_, v_i_452_, v___x_466_);
lean_inc_ref_n(v_range_449_, 2);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_449_, v_byteOffset_450_, v_start_461_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_449_, v_byteOffset_450_, v_stop_462_);
if (v_isShared_465_ == 0)
{
lean_ctor_set(v___x_464_, 1, v___x_469_);
lean_ctor_set(v___x_464_, 0, v___x_468_);
v___x_471_ = v___x_464_;
goto v_reusejp_470_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_468_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_469_);
v___x_471_ = v_reuseFailAlloc_479_;
goto v_reusejp_470_;
}
v_reusejp_470_:
{
lean_object* v___x_473_; 
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 0, v___x_471_);
v___x_473_ = v___x_459_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v_newText_457_);
v___x_473_ = v_reuseFailAlloc_478_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((size_t)1ULL);
v___x_475_ = lean_usize_add(v_i_452_, v___x_474_);
v___x_476_ = lean_array_uset(v_bs_x27_467_, v_i_452_, v___x_473_);
v_i_452_ = v___x_475_;
v_bs_453_ = v___x_476_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_449_ = stack[0].m_obj;
lean_object* v_byteOffset_450_ = stack[1].m_obj;
size_t v_sz_451_ = stack[2].m_num;
size_t v_i_452_ = stack[3].m_num;
lean_object* v_bs_453_ = stack[4].m_obj;
lean_object* v_res_482_;
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_449_, v_byteOffset_450_, v_sz_451_, v_i_452_, v_bs_453_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2___boxed(lean_object* v_range_483_, lean_object* v_byteOffset_484_, lean_object* v_sz_485_, lean_object* v_i_486_, lean_object* v_bs_487_){
_start:
{
size_t v_sz_boxed_488_; size_t v_i_boxed_489_; lean_object* v_res_490_; 
v_sz_boxed_488_ = lean_unbox_usize(v_sz_485_);
lean_dec(v_sz_485_);
v_i_boxed_489_ = lean_unbox_usize(v_i_486_);
lean_dec(v_i_486_);
v_res_490_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_483_, v_byteOffset_484_, v_sz_boxed_488_, v_i_boxed_489_, v_bs_487_);
lean_dec(v_byteOffset_484_);
return v_res_490_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(lean_object* v_range_491_, lean_object* v_byteOffset_492_, size_t v_sz_493_, size_t v_i_494_, lean_object* v_bs_495_){
_start:
{
uint8_t v___x_496_; 
v___x_496_ = lean_usize_dec_lt(v_i_494_, v_sz_493_);
if (v___x_496_ == 0)
{
lean_dec_ref(v_range_491_);
return v_bs_495_;
}
else
{
lean_object* v_v_497_; lean_object* v_range_498_; lean_object* v_newText_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_523_; 
v_v_497_ = lean_array_uget(v_bs_495_, v_i_494_);
v_range_498_ = lean_ctor_get(v_v_497_, 0);
v_newText_499_ = lean_ctor_get(v_v_497_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_v_497_);
if (v_isSharedCheck_523_ == 0)
{
v___x_501_ = v_v_497_;
v_isShared_502_ = v_isSharedCheck_523_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_newText_499_);
lean_inc(v_range_498_);
lean_dec(v_v_497_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_523_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_start_503_; lean_object* v_stop_504_; lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_522_; 
v_start_503_ = lean_ctor_get(v_range_498_, 0);
v_stop_504_ = lean_ctor_get(v_range_498_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_range_498_);
if (v_isSharedCheck_522_ == 0)
{
v___x_506_ = v_range_498_;
v_isShared_507_ = v_isSharedCheck_522_;
goto v_resetjp_505_;
}
else
{
lean_inc(v_stop_504_);
lean_inc(v_start_503_);
lean_dec(v_range_498_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_522_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; lean_object* v_bs_x27_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v_bs_x27_509_ = lean_array_uset(v_bs_495_, v_i_494_, v___x_508_);
lean_inc_ref_n(v_range_491_, 2);
v___x_510_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_491_, v_byteOffset_492_, v_start_503_);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_491_, v_byteOffset_492_, v_stop_504_);
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v___x_511_);
lean_ctor_set(v___x_506_, 0, v___x_510_);
v___x_513_ = v___x_506_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v___x_511_);
v___x_513_ = v_reuseFailAlloc_521_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
lean_object* v___x_515_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_513_);
v___x_515_ = v___x_501_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_newText_499_);
v___x_515_ = v_reuseFailAlloc_520_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
size_t v___x_516_; size_t v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_516_ = ((size_t)1ULL);
v___x_517_ = lean_usize_add(v_i_494_, v___x_516_);
v___x_518_ = lean_array_uset(v_bs_x27_509_, v_i_494_, v___x_515_);
v___x_519_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_491_, v_byteOffset_492_, v_sz_493_, v___x_517_, v___x_518_);
return v___x_519_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_491_ = stack[0].m_obj;
lean_object* v_byteOffset_492_ = stack[1].m_obj;
size_t v_sz_493_ = stack[2].m_num;
size_t v_i_494_ = stack[3].m_num;
lean_object* v_bs_495_ = stack[4].m_obj;
lean_object* v_res_524_;
v_res_524_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_491_, v_byteOffset_492_, v_sz_493_, v_i_494_, v_bs_495_);
stack->m_obj
 = v_res_524_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___boxed(lean_object* v_range_525_, lean_object* v_byteOffset_526_, lean_object* v_sz_527_, lean_object* v_i_528_, lean_object* v_bs_529_){
_start:
{
size_t v_sz_boxed_530_; size_t v_i_boxed_531_; lean_object* v_res_532_; 
v_sz_boxed_530_ = lean_unbox_usize(v_sz_527_);
lean_dec(v_sz_527_);
v_i_boxed_531_ = lean_unbox_usize(v_i_528_);
lean_dec(v_i_528_);
v_res_532_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_525_, v_byteOffset_526_, v_sz_boxed_530_, v_i_boxed_531_, v_bs_529_);
lean_dec(v_byteOffset_526_);
return v_res_532_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(lean_object* v_hintMod_533_, lean_object* v_range_534_, lean_object* v_as_535_, size_t v_i_536_, size_t v_stop_537_){
_start:
{
uint8_t v___x_542_; 
v___x_542_ = lean_usize_dec_eq(v_i_536_, v_stop_537_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v_location_x3f_544_; 
v___x_543_ = lean_array_uget_borrowed(v_as_535_, v_i_536_);
v_location_x3f_544_ = lean_ctor_get(v___x_543_, 2);
if (lean_obj_tag(v_location_x3f_544_) == 0)
{
goto v___jp_538_;
}
else
{
lean_object* v_val_545_; lean_object* v_module_546_; lean_object* v_range_547_; uint8_t v___x_548_; uint8_t v___y_550_; uint8_t v___x_551_; 
v_val_545_ = lean_ctor_get(v_location_x3f_544_, 0);
v_module_546_ = lean_ctor_get(v_val_545_, 0);
v_range_547_ = lean_ctor_get(v_val_545_, 1);
v___x_548_ = 1;
v___x_551_ = lean_name_eq(v_module_546_, v_hintMod_533_);
if (v___x_551_ == 0)
{
v___y_550_ = v___x_551_;
goto v___jp_549_;
}
else
{
uint8_t v___x_552_; 
v___x_552_ = l_Lean_Syntax_Range_overlaps(v_range_534_, v_range_547_, v___x_551_, v___x_542_);
v___y_550_ = v___x_552_;
goto v___jp_549_;
}
v___jp_549_:
{
if (v___y_550_ == 0)
{
goto v___jp_538_;
}
else
{
return v___x_548_;
}
}
}
}
else
{
uint8_t v___x_553_; 
v___x_553_ = 0;
return v___x_553_;
}
v___jp_538_:
{
size_t v___x_539_; size_t v___x_540_; 
v___x_539_ = ((size_t)1ULL);
v___x_540_ = lean_usize_add(v_i_536_, v___x_539_);
v_i_536_ = v___x_540_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_hintMod_533_ = stack[0].m_obj;
lean_object* v_range_534_ = stack[1].m_obj;
lean_object* v_as_535_ = stack[2].m_obj;
size_t v_i_536_ = stack[3].m_num;
size_t v_stop_537_ = stack[4].m_num;
uint8_t v_res_554_;
v_res_554_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_533_, v_range_534_, v_as_535_, v_i_536_, v_stop_537_);
stack->m_num = v_res_554_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5___boxed(lean_object* v_hintMod_555_, lean_object* v_range_556_, lean_object* v_as_557_, lean_object* v_i_558_, lean_object* v_stop_559_){
_start:
{
size_t v_i_boxed_560_; size_t v_stop_boxed_561_; uint8_t v_res_562_; lean_object* v_r_563_; 
v_i_boxed_560_ = lean_unbox_usize(v_i_558_);
lean_dec(v_i_558_);
v_stop_boxed_561_ = lean_unbox_usize(v_stop_559_);
lean_dec(v_stop_559_);
v_res_562_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_555_, v_range_556_, v_as_557_, v_i_boxed_560_, v_stop_boxed_561_);
lean_dec_ref(v_as_557_);
lean_dec_ref(v_range_556_);
lean_dec(v_hintMod_555_);
v_r_563_ = lean_box(v_res_562_);
return v_r_563_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(lean_object* v_range_564_, uint8_t v___x_565_, lean_object* v_as_566_, size_t v_i_567_, size_t v_stop_568_){
_start:
{
uint8_t v___x_569_; 
v___x_569_ = lean_usize_dec_eq(v_i_567_, v_stop_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v_range_571_; uint8_t v___x_572_; uint8_t v___x_573_; 
v___x_570_ = lean_array_uget_borrowed(v_as_566_, v_i_567_);
v_range_571_ = lean_ctor_get(v___x_570_, 0);
v___x_572_ = 1;
v___x_573_ = l_Lean_Syntax_Range_overlaps(v_range_564_, v_range_571_, v___x_572_, v___x_565_);
if (v___x_573_ == 0)
{
size_t v___x_574_; size_t v___x_575_; 
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_567_, v___x_574_);
v_i_567_ = v___x_575_;
goto _start;
}
else
{
return v___x_572_;
}
}
else
{
uint8_t v___x_577_; 
v___x_577_ = 0;
return v___x_577_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_range_564_ = stack[0].m_obj;
uint8_t v___x_565_ = stack[1].m_num;
lean_object* v_as_566_ = stack[2].m_obj;
size_t v_i_567_ = stack[3].m_num;
size_t v_stop_568_ = stack[4].m_num;
uint8_t v_res_578_;
v_res_578_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_564_, v___x_565_, v_as_566_, v_i_567_, v_stop_568_);
stack->m_num = v_res_578_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4___boxed(lean_object* v_range_579_, lean_object* v___x_580_, lean_object* v_as_581_, lean_object* v_i_582_, lean_object* v_stop_583_){
_start:
{
uint8_t v___x_2706__boxed_584_; size_t v_i_boxed_585_; size_t v_stop_boxed_586_; uint8_t v_res_587_; lean_object* v_r_588_; 
v___x_2706__boxed_584_ = lean_unbox(v___x_580_);
v_i_boxed_585_ = lean_unbox_usize(v_i_582_);
lean_dec(v_i_582_);
v_stop_boxed_586_ = lean_unbox_usize(v_stop_583_);
lean_dec(v_stop_583_);
v_res_587_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_579_, v___x_2706__boxed_584_, v_as_581_, v_i_boxed_585_, v_stop_boxed_586_);
lean_dec_ref(v_as_581_);
lean_dec_ref(v_range_579_);
v_r_588_ = lean_box(v_res_587_);
return v_r_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f(lean_object* v_hintMod_589_, lean_object* v_ihi_590_, lean_object* v_range_591_, lean_object* v_newText_592_){
_start:
{
lean_object* v_position_593_; lean_object* v_label_594_; lean_object* v_kind_x3f_595_; lean_object* v_textEdits_596_; lean_object* v_tooltip_x3f_597_; uint8_t v_paddingLeft_598_; uint8_t v_paddingRight_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_685_; 
v_position_593_ = lean_ctor_get(v_ihi_590_, 0);
v_label_594_ = lean_ctor_get(v_ihi_590_, 1);
v_kind_x3f_595_ = lean_ctor_get(v_ihi_590_, 2);
v_textEdits_596_ = lean_ctor_get(v_ihi_590_, 3);
v_tooltip_x3f_597_ = lean_ctor_get(v_ihi_590_, 4);
v_paddingLeft_598_ = lean_ctor_get_uint8(v_ihi_590_, sizeof(void*)*5);
v_paddingRight_599_ = lean_ctor_get_uint8(v_ihi_590_, sizeof(void*)*5 + 1);
v_isSharedCheck_685_ = !lean_is_exclusive(v_ihi_590_);
if (v_isSharedCheck_685_ == 0)
{
v___x_601_ = v_ihi_590_;
v_isShared_602_ = v_isSharedCheck_685_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_tooltip_x3f_597_);
lean_inc(v_textEdits_596_);
lean_inc(v_kind_x3f_595_);
lean_inc(v_label_594_);
lean_inc(v_position_593_);
lean_dec(v_ihi_590_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_685_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_615_; lean_object* v___y_616_; uint8_t v___y_629_; uint8_t v___y_664_; uint8_t v___y_665_; uint8_t v___y_668_; 
if (lean_obj_tag(v_label_594_) == 0)
{
uint8_t v___x_677_; 
v___x_677_ = 0;
v___y_668_ = v___x_677_;
goto v___jp_667_;
}
else
{
lean_object* v_p_678_; lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_p_678_ = lean_ctor_get(v_label_594_, 0);
v___x_679_ = lean_unsigned_to_nat(0u);
v___x_680_ = lean_array_get_size(v_p_678_);
v___x_681_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
if (v___x_681_ == 0)
{
v___y_668_ = v___x_681_;
goto v___jp_667_;
}
else
{
if (v___x_681_ == 0)
{
v___y_668_ = v___x_681_;
goto v___jp_667_;
}
else
{
size_t v___x_682_; size_t v___x_683_; uint8_t v___x_684_; 
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_680_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_589_, v_range_591_, v_p_678_, v___x_682_, v___x_683_);
v___y_668_ = v___x_684_;
goto v___jp_667_;
}
}
}
v___jp_603_:
{
size_t v_sz_607_; size_t v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v_sz_607_ = lean_array_size(v_textEdits_596_);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_591_, v___y_605_, v_sz_607_, v___x_608_, v_textEdits_596_);
lean_dec(v___y_605_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 3, v___x_609_);
lean_ctor_set(v___x_601_, 1, v___y_606_);
lean_ctor_set(v___x_601_, 0, v___y_604_);
v___x_611_ = v___x_601_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___y_604_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v___y_606_);
lean_ctor_set(v_reuseFailAlloc_613_, 2, v_kind_x3f_595_);
lean_ctor_set(v_reuseFailAlloc_613_, 3, v___x_609_);
lean_ctor_set(v_reuseFailAlloc_613_, 4, v_tooltip_x3f_597_);
lean_ctor_set_uint8(v_reuseFailAlloc_613_, sizeof(void*)*5, v_paddingLeft_598_);
lean_ctor_set_uint8(v_reuseFailAlloc_613_, sizeof(void*)*5 + 1, v_paddingRight_599_);
v___x_611_ = v_reuseFailAlloc_613_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
lean_object* v___x_612_; 
v___x_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
return v___x_612_;
}
}
v___jp_614_:
{
if (lean_obj_tag(v_label_594_) == 0)
{
v___y_604_ = v___y_616_;
v___y_605_ = v___y_615_;
v___y_606_ = v_label_594_;
goto v___jp_603_;
}
else
{
lean_object* v_p_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_627_; 
v_p_617_ = lean_ctor_get(v_label_594_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_label_594_);
if (v_isSharedCheck_627_ == 0)
{
v___x_619_ = v_label_594_;
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_p_617_);
lean_dec(v_label_594_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_627_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
size_t v_sz_621_; size_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_625_; 
v_sz_621_ = lean_array_size(v_p_617_);
v___x_622_ = ((size_t)0ULL);
lean_inc_ref(v_range_591_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_589_, v_range_591_, v___y_615_, v_sz_621_, v___x_622_, v_p_617_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_623_);
v___x_625_ = v___x_619_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
v___y_604_ = v___y_616_;
v___y_605_ = v___y_615_;
v___y_606_ = v___x_625_;
goto v___jp_603_;
}
}
}
}
v___jp_628_:
{
if (v___y_629_ == 0)
{
lean_object* v_start_630_; lean_object* v_stop_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v_byteOffset_636_; lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_start_630_ = lean_ctor_get(v_range_591_, 0);
v_stop_631_ = lean_ctor_get(v_range_591_, 1);
v___x_632_ = lean_string_utf8_byte_size(v_newText_592_);
v___x_633_ = lean_nat_to_int(v___x_632_);
v___x_634_ = l_Lean_Syntax_Range_bsize(v_range_591_);
v___x_635_ = lean_nat_to_int(v___x_634_);
v_byteOffset_636_ = lean_int_sub(v___x_633_, v___x_635_);
lean_dec(v___x_635_);
lean_dec(v___x_633_);
v___x_637_ = lean_unsigned_to_nat(1u);
v___x_638_ = lean_nat_add(v_stop_631_, v___x_637_);
v___x_639_ = lean_nat_dec_le(v___x_638_, v_position_593_);
lean_dec(v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_640_ = lean_nat_add(v_position_593_, v___x_637_);
v___x_641_ = lean_nat_dec_le(v___x_640_, v_start_630_);
lean_dec(v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_642_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_643_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1));
v___x_644_ = lean_unsigned_to_nat(87u);
v___x_645_ = lean_unsigned_to_nat(6u);
v___x_646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2));
v___x_647_ = l_Nat_reprFast(v_position_593_);
v___x_648_ = lean_string_append(v___x_646_, v___x_647_);
lean_dec_ref(v___x_647_);
v___x_649_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3));
v___x_650_ = lean_string_append(v___x_648_, v___x_649_);
lean_inc(v_start_630_);
v___x_651_ = l_Nat_reprFast(v_start_630_);
v___x_652_ = lean_string_append(v___x_650_, v___x_651_);
lean_dec_ref(v___x_651_);
v___x_653_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4));
v___x_654_ = lean_string_append(v___x_652_, v___x_653_);
lean_inc(v_stop_631_);
v___x_655_ = l_Nat_reprFast(v_stop_631_);
v___x_656_ = lean_string_append(v___x_654_, v___x_655_);
lean_dec_ref(v___x_655_);
v___x_657_ = l_mkPanicMessageWithDecl(v___x_642_, v___x_643_, v___x_644_, v___x_645_, v___x_656_);
lean_dec_ref(v___x_656_);
v___x_658_ = l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(v___x_657_);
v___y_615_ = v_byteOffset_636_;
v___y_616_ = v___x_658_;
goto v___jp_614_;
}
else
{
v___y_615_ = v_byteOffset_636_;
v___y_616_ = v_position_593_;
goto v___jp_614_;
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_nat_to_int(v_position_593_);
v___x_660_ = lean_int_add(v___x_659_, v_byteOffset_636_);
lean_dec(v___x_659_);
v___x_661_ = l_Int_toNat(v___x_660_);
lean_dec(v___x_660_);
v___y_615_ = v_byteOffset_636_;
v___y_616_ = v___x_661_;
goto v___jp_614_;
}
}
else
{
lean_object* v___x_662_; 
lean_del_object(v___x_601_);
lean_dec(v_tooltip_x3f_597_);
lean_dec_ref(v_textEdits_596_);
lean_dec(v_kind_x3f_595_);
lean_dec_ref(v_label_594_);
lean_dec(v_position_593_);
lean_dec_ref(v_range_591_);
v___x_662_ = lean_box(0);
return v___x_662_;
}
}
v___jp_663_:
{
if (v___y_665_ == 0)
{
v___y_629_ = v___y_664_;
goto v___jp_628_;
}
else
{
lean_object* v___x_666_; 
lean_del_object(v___x_601_);
lean_dec(v_tooltip_x3f_597_);
lean_dec_ref(v_textEdits_596_);
lean_dec(v_kind_x3f_595_);
lean_dec_ref(v_label_594_);
lean_dec(v_position_593_);
lean_dec_ref(v_range_591_);
v___x_666_ = lean_box(0);
return v___x_666_;
}
}
v___jp_667_:
{
uint8_t v___x_669_; uint8_t v___x_670_; 
v___x_669_ = 1;
v___x_670_ = l_Lean_Syntax_Range_contains(v_range_591_, v_position_593_, v___x_669_);
if (v___x_670_ == 0)
{
lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_671_ = lean_unsigned_to_nat(0u);
v___x_672_ = lean_array_get_size(v_textEdits_596_);
v___x_673_ = lean_nat_dec_lt(v___x_671_, v___x_672_);
if (v___x_673_ == 0)
{
v___y_629_ = v___y_668_;
goto v___jp_628_;
}
else
{
if (v___x_673_ == 0)
{
v___y_629_ = v___y_668_;
goto v___jp_628_;
}
else
{
size_t v___x_674_; size_t v___x_675_; uint8_t v___x_676_; 
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_672_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_591_, v___x_670_, v_textEdits_596_, v___x_674_, v___x_675_);
v___y_664_ = v___y_668_;
v___y_665_ = v___x_676_;
goto v___jp_663_;
}
}
}
else
{
v___y_664_ = v___y_668_;
v___y_665_ = v___x_670_;
goto v___jp_663_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___boxed(lean_object* v_hintMod_686_, lean_object* v_ihi_687_, lean_object* v_range_688_, lean_object* v_newText_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(v_hintMod_686_, v_ihi_687_, v_range_688_, v_newText_689_);
lean_dec_ref(v_newText_689_);
lean_dec(v_hintMod_686_);
return v_res_690_;
}
}
static lean_object* _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_720_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_720_, 0, lean_box(0));
lean_closure_set(v___x_720_, 1, lean_box(0));
lean_closure_set(v___x_720_, 2, v___x_719_);
return v___x_720_;
}
}
lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(lean_object* v_msg_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v___f_725_; lean_object* v___x_14663__overap_726_; lean_object* v___x_727_; 
v___x_724_ = lean_obj_once(&l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0, &l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0_once, _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0);
v___f_725_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_725_, 0, v___x_724_);
v___x_14663__overap_726_ = lean_panic_fn_borrowed(v___f_725_, v_msg_721_);
lean_dec_ref(v___f_725_);
lean_inc_ref(v___y_722_);
v___x_727_ = lean_apply_2(v___x_14663__overap_726_, v___y_722_, lean_box(0));
return v___x_727_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_721_ = stack[0].m_obj;
lean_object* v___y_722_ = stack[1].m_obj;
lean_object* v_res_728_;
v_res_728_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v_msg_721_, v___y_722_);
stack->m_obj
 = v_res_728_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___boxed(lean_object* v_msg_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v_msg_729_, v___y_730_);
lean_dec_ref(v___y_730_);
return v_res_732_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(uint8_t v___x_733_, lean_object* v_x_734_, lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___x_740_ = lean_box(v___x_733_);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___y_737_);
v___x_742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
return v___x_742_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_733_ = stack[0].m_num;
lean_object* v_x_734_ = stack[1].m_obj;
lean_object* v_x_735_ = stack[2].m_obj;
lean_object* v_x_736_ = stack[3].m_obj;
lean_object* v___y_737_ = stack[4].m_obj;
lean_object* v___y_738_ = stack[5].m_obj;
lean_object* v_res_743_;
v_res_743_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(v___x_733_, v_x_734_, v_x_735_, v_x_736_, v___y_737_, v___y_738_);
stack->m_obj
 = v_res_743_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed(lean_object* v___x_744_, lean_object* v_x_745_, lean_object* v_x_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
uint8_t v___x_17635__boxed_751_; lean_object* v_res_752_; 
v___x_17635__boxed_751_ = lean_unbox(v___x_744_);
v_res_752_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(v___x_17635__boxed_751_, v_x_745_, v_x_746_, v_x_747_, v___y_748_, v___y_749_);
lean_dec_ref(v___y_749_);
lean_dec_ref(v_x_747_);
lean_dec_ref(v_x_746_);
lean_dec_ref(v_x_745_);
return v_res_752_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(lean_object* v_ci_753_, lean_object* v_i_754_, lean_object* v_x_755_, lean_object* v___y_756_, lean_object* v___y_757_){
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
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ci_753_ = stack[0].m_obj;
lean_object* v_i_754_ = stack[1].m_obj;
lean_object* v_x_755_ = stack[2].m_obj;
lean_object* v___y_756_ = stack[3].m_obj;
lean_object* v___y_757_ = stack[4].m_obj;
lean_object* v_res_798_;
v_res_798_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(v_ci_753_, v_i_754_, v_x_755_, v___y_756_, v___y_757_);
stack->m_obj
 = v_res_798_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed(lean_object* v_ci_799_, lean_object* v_i_800_, lean_object* v_x_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(v_ci_799_, v_i_800_, v_x_801_, v___y_802_, v___y_803_);
lean_dec_ref(v___y_803_);
lean_dec_ref(v_x_801_);
return v_res_805_;
}
}
lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(lean_object* v_postNode_806_, lean_object* v_ci_807_, lean_object* v_i_808_, lean_object* v_cs_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v___x_814_; 
lean_inc_ref(v___y_812_);
v___x_814_ = lean_apply_6(v_postNode_806_, v_ci_807_, v_i_808_, v_cs_809_, v___y_811_, v___y_812_, lean_box(0));
return v___x_814_;
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_postNode_806_ = stack[0].m_obj;
lean_object* v_ci_807_ = stack[1].m_obj;
lean_object* v_i_808_ = stack[2].m_obj;
lean_object* v_cs_809_ = stack[3].m_obj;
lean_object* v_x_810_ = stack[4].m_obj;
lean_object* v___y_811_ = stack[5].m_obj;
lean_object* v___y_812_ = stack[6].m_obj;
lean_object* v_res_815_;
v_res_815_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(v_postNode_806_, v_ci_807_, v_i_808_, v_cs_809_, v_x_810_, v___y_811_, v___y_812_);
stack->m_obj
 = v_res_815_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed(lean_object* v_postNode_816_, lean_object* v_ci_817_, lean_object* v_i_818_, lean_object* v_cs_819_, lean_object* v_x_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(v_postNode_816_, v_ci_817_, v_i_818_, v_cs_819_, v_x_820_, v___y_821_, v___y_822_);
lean_dec_ref(v___y_822_);
lean_dec(v_x_820_);
return v_res_824_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_instMonadEIO___redArg();
return v___x_825_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(lean_object* v_msg_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___f_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_17034__overap_844_; lean_object* v___x_845_; 
v___x_830_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_831_ = l_ReaderT_instMonad___redArg(v___x_830_);
lean_inc_ref_n(v___x_831_, 6);
v___f_832_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_832_, 0, v___x_831_);
v___f_833_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_833_, 0, v___x_831_);
v___f_834_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_834_, 0, v___x_831_);
v___f_835_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_835_, 0, v___x_831_);
v___x_836_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_836_, 0, lean_box(0));
lean_closure_set(v___x_836_, 1, lean_box(0));
lean_closure_set(v___x_836_, 2, v___x_831_);
v___x_837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___f_832_);
v___x_838_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_838_, 0, lean_box(0));
lean_closure_set(v___x_838_, 1, lean_box(0));
lean_closure_set(v___x_838_, 2, v___x_831_);
v___x_839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
lean_ctor_set(v___x_839_, 2, v___f_833_);
lean_ctor_set(v___x_839_, 3, v___f_834_);
lean_ctor_set(v___x_839_, 4, v___f_835_);
v___x_840_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_840_, 0, lean_box(0));
lean_closure_set(v___x_840_, 1, lean_box(0));
lean_closure_set(v___x_840_, 2, v___x_831_);
v___x_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_839_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = lean_box(0);
v___x_843_ = l_instInhabitedOfMonad___redArg(v___x_841_, v___x_842_);
v___x_17034__overap_844_ = lean_panic_fn_borrowed(v___x_843_, v_msg_826_);
lean_dec(v___x_843_);
lean_inc_ref(v___y_828_);
v___x_845_ = lean_apply_3(v___x_17034__overap_844_, v___y_827_, v___y_828_, lean_box(0));
return v___x_845_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_826_ = stack[0].m_obj;
lean_object* v___y_827_ = stack[1].m_obj;
lean_object* v___y_828_ = stack[2].m_obj;
lean_object* v_res_846_;
v_res_846_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_826_, v___y_827_, v___y_828_);
stack->m_obj
 = v_res_846_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_msg_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_847_, v___y_848_, v___y_849_);
lean_dec_ref(v___y_849_);
return v_res_851_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_855_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2));
v___x_856_ = lean_unsigned_to_nat(21u);
v___x_857_ = lean_unsigned_to_nat(65u);
v___x_858_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1));
v___x_859_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0));
v___x_860_ = l_mkPanicMessageWithDecl(v___x_859_, v___x_858_, v___x_857_, v___x_856_, v___x_855_);
return v___x_860_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(lean_object* v_preNode_861_, lean_object* v_postNode_862_, lean_object* v_x_863_, lean_object* v_x_864_, lean_object* v___y_865_, lean_object* v___y_866_){
_start:
{
switch(lean_obj_tag(v_x_864_))
{
case 0:
{
lean_object* v_i_868_; lean_object* v_t_869_; lean_object* v___x_870_; 
v_i_868_ = lean_ctor_get(v_x_864_, 0);
lean_inc_ref(v_i_868_);
v_t_869_ = lean_ctor_get(v_x_864_, 1);
lean_inc_ref(v_t_869_);
lean_dec_ref_known(v_x_864_, 2);
v___x_870_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_868_, v_x_863_);
v_x_863_ = v___x_870_;
v_x_864_ = v_t_869_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_863_) == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; 
lean_dec_ref_known(v_x_864_, 2);
lean_dec_ref(v_postNode_862_);
lean_dec_ref(v_preNode_861_);
v___x_872_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3);
v___x_873_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v___x_872_, v___y_865_, v___y_866_);
return v___x_873_;
}
else
{
lean_object* v_i_874_; lean_object* v_children_875_; lean_object* v_val_876_; lean_object* v___x_877_; 
v_i_874_ = lean_ctor_get(v_x_864_, 0);
lean_inc_ref_n(v_i_874_, 2);
v_children_875_ = lean_ctor_get(v_x_864_, 1);
lean_inc_ref_n(v_children_875_, 2);
lean_dec_ref_known(v_x_864_, 2);
v_val_876_ = lean_ctor_get(v_x_863_, 0);
lean_inc_n(v_val_876_, 2);
lean_inc_ref(v_preNode_861_);
lean_inc_ref(v___y_866_);
v___x_877_ = lean_apply_6(v_preNode_861_, v_val_876_, v_i_874_, v_children_875_, v___y_865_, v___y_866_, lean_box(0));
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; lean_object* v_fst_879_; uint8_t v___x_880_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v_fst_879_ = lean_ctor_get(v_a_878_, 0);
v___x_880_ = lean_unbox(v_fst_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_915_; 
lean_dec_ref(v_preNode_861_);
v_isSharedCheck_915_ = !lean_is_exclusive(v_x_863_);
if (v_isSharedCheck_915_ == 0)
{
lean_object* v_unused_916_; 
v_unused_916_ = lean_ctor_get(v_x_863_, 0);
lean_dec(v_unused_916_);
v___x_882_ = v_x_863_;
v_isShared_883_ = v_isSharedCheck_915_;
goto v_resetjp_881_;
}
else
{
lean_dec(v_x_863_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_915_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_snd_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v_snd_884_ = lean_ctor_get(v_a_878_, 1);
lean_inc(v_snd_884_);
lean_dec(v_a_878_);
v___x_885_ = lean_box(0);
lean_inc_ref(v___y_866_);
v___x_886_ = lean_apply_7(v_postNode_862_, v_val_876_, v_i_874_, v_children_875_, v___x_885_, v_snd_884_, v___y_866_, lean_box(0));
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_906_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_906_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_906_ == 0)
{
v___x_889_ = v___x_886_;
v_isShared_890_ = v_isSharedCheck_906_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_a_887_);
lean_dec(v___x_886_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_906_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_905_; 
v_fst_891_ = lean_ctor_get(v_a_887_, 0);
v_snd_892_ = lean_ctor_get(v_a_887_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_a_887_);
if (v_isSharedCheck_905_ == 0)
{
v___x_894_ = v_a_887_;
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_snd_892_);
lean_inc(v_fst_891_);
lean_dec(v_a_887_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_905_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v_fst_891_);
v___x_897_ = v___x_882_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_fst_891_);
v___x_897_ = v_reuseFailAlloc_904_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v___x_897_);
v___x_899_ = v___x_894_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_903_; 
v_reuseFailAlloc_903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_903_, 0, v___x_897_);
lean_ctor_set(v_reuseFailAlloc_903_, 1, v_snd_892_);
v___x_899_ = v_reuseFailAlloc_903_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
lean_object* v___x_901_; 
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 0, v___x_899_);
v___x_901_ = v___x_889_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v___x_899_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
}
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_del_object(v___x_882_);
v_a_907_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_886_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_886_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
else
{
lean_object* v_snd_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v_snd_917_ = lean_ctor_get(v_a_878_, 1);
lean_inc(v_snd_917_);
lean_dec(v_a_878_);
v___x_918_ = l_Lean_Elab_Info_updateContext_x3f(v_x_863_, v_i_874_);
v___x_919_ = l_Lean_PersistentArray_toList___redArg(v_children_875_);
v___x_920_ = lean_box(0);
lean_inc_ref(v_postNode_862_);
v___x_921_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_861_, v_postNode_862_, v___x_918_, v___x_919_, v___x_920_, v_snd_917_, v___y_866_);
if (lean_obj_tag(v___x_921_) == 0)
{
lean_object* v_a_922_; lean_object* v_fst_923_; lean_object* v_snd_924_; lean_object* v___x_925_; 
v_a_922_ = lean_ctor_get(v___x_921_, 0);
lean_inc(v_a_922_);
lean_dec_ref_known(v___x_921_, 1);
v_fst_923_ = lean_ctor_get(v_a_922_, 0);
lean_inc(v_fst_923_);
v_snd_924_ = lean_ctor_get(v_a_922_, 1);
lean_inc(v_snd_924_);
lean_dec(v_a_922_);
lean_inc_ref(v___y_866_);
v___x_925_ = lean_apply_7(v_postNode_862_, v_val_876_, v_i_874_, v_children_875_, v_fst_923_, v_snd_924_, v___y_866_, lean_box(0));
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_943_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_943_ == 0)
{
v___x_928_ = v___x_925_;
v_isShared_929_ = v_isSharedCheck_943_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_925_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_943_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v_fst_930_; lean_object* v_snd_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_942_; 
v_fst_930_ = lean_ctor_get(v_a_926_, 0);
v_snd_931_ = lean_ctor_get(v_a_926_, 1);
v_isSharedCheck_942_ = !lean_is_exclusive(v_a_926_);
if (v_isSharedCheck_942_ == 0)
{
v___x_933_ = v_a_926_;
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_snd_931_);
lean_inc(v_fst_930_);
lean_dec(v_a_926_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_942_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_935_, 0, v_fst_930_);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_935_);
v___x_937_ = v___x_933_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_935_);
lean_ctor_set(v_reuseFailAlloc_941_, 1, v_snd_931_);
v___x_937_ = v_reuseFailAlloc_941_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
lean_object* v___x_939_; 
if (v_isShared_929_ == 0)
{
lean_ctor_set(v___x_928_, 0, v___x_937_);
v___x_939_ = v___x_928_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v___x_937_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
v_a_944_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_925_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_925_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_val_876_);
lean_dec_ref(v_children_875_);
lean_dec_ref(v_i_874_);
lean_dec_ref(v_postNode_862_);
v_a_952_ = lean_ctor_get(v___x_921_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_921_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_921_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_921_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
else
{
lean_object* v_a_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
lean_dec(v_val_876_);
lean_dec_ref(v_children_875_);
lean_dec_ref(v_i_874_);
lean_dec_ref_known(v_x_863_, 1);
lean_dec_ref(v_postNode_862_);
lean_dec_ref(v_preNode_861_);
v_a_960_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_967_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_967_ == 0)
{
v___x_962_ = v___x_877_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_a_960_);
lean_dec(v___x_877_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
}
default: 
{
lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_976_; 
lean_dec(v_x_863_);
lean_dec_ref(v_postNode_862_);
lean_dec_ref(v_preNode_861_);
v_isSharedCheck_976_ = !lean_is_exclusive(v_x_864_);
if (v_isSharedCheck_976_ == 0)
{
lean_object* v_unused_977_; 
v_unused_977_ = lean_ctor_get(v_x_864_, 0);
lean_dec(v_unused_977_);
v___x_969_ = v_x_864_;
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
else
{
lean_dec(v_x_864_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_976_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v___x_971_ = lean_box(0);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___y_865_);
if (v_isShared_970_ == 0)
{
lean_ctor_set_tag(v___x_969_, 0);
lean_ctor_set(v___x_969_, 0, v___x_972_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_861_ = stack[0].m_obj;
lean_object* v_postNode_862_ = stack[1].m_obj;
lean_object* v_x_863_ = stack[2].m_obj;
lean_object* v_x_864_ = stack[3].m_obj;
lean_object* v___y_865_ = stack[4].m_obj;
lean_object* v___y_866_ = stack[5].m_obj;
lean_object* v_res_978_;
v_res_978_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_861_, v_postNode_862_, v_x_863_, v_x_864_, v___y_865_, v___y_866_);
stack->m_obj
 = v_res_978_;
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(lean_object* v_preNode_979_, lean_object* v_postNode_980_, lean_object* v___x_981_, lean_object* v_x_982_, lean_object* v_x_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
if (lean_obj_tag(v_x_982_) == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v___x_981_);
lean_dec_ref(v_postNode_980_);
lean_dec_ref(v_preNode_979_);
v___x_987_ = l_List_reverse___redArg(v_x_983_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___y_984_);
v___x_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_989_, 0, v___x_988_);
return v___x_989_;
}
else
{
lean_object* v_head_990_; lean_object* v_tail_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1011_; 
v_head_990_ = lean_ctor_get(v_x_982_, 0);
v_tail_991_ = lean_ctor_get(v_x_982_, 1);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_x_982_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_993_ = v_x_982_;
v_isShared_994_ = v_isSharedCheck_1011_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_tail_991_);
lean_inc(v_head_990_);
lean_dec(v_x_982_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1011_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; 
lean_inc(v___x_981_);
lean_inc_ref(v_postNode_980_);
lean_inc_ref(v_preNode_979_);
v___x_995_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_979_, v_postNode_980_, v___x_981_, v_head_990_, v___y_984_, v___y_985_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v_fst_997_; lean_object* v_snd_998_; lean_object* v___x_1000_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
v_fst_997_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_fst_997_);
v_snd_998_ = lean_ctor_get(v_a_996_, 1);
lean_inc(v_snd_998_);
lean_dec(v_a_996_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v_x_983_);
lean_ctor_set(v___x_993_, 0, v_fst_997_);
v___x_1000_ = v___x_993_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_fst_997_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v_x_983_);
v___x_1000_ = v_reuseFailAlloc_1002_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
v_x_982_ = v_tail_991_;
v_x_983_ = v___x_1000_;
v___y_984_ = v_snd_998_;
goto _start;
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_del_object(v___x_993_);
lean_dec(v_tail_991_);
lean_dec(v_x_983_);
lean_dec(v___x_981_);
lean_dec_ref(v_postNode_980_);
lean_dec_ref(v_preNode_979_);
v_a_1003_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_995_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_995_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_979_ = stack[0].m_obj;
lean_object* v_postNode_980_ = stack[1].m_obj;
lean_object* v___x_981_ = stack[2].m_obj;
lean_object* v_x_982_ = stack[3].m_obj;
lean_object* v_x_983_ = stack[4].m_obj;
lean_object* v___y_984_ = stack[5].m_obj;
lean_object* v___y_985_ = stack[6].m_obj;
lean_object* v_res_1012_;
v_res_1012_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_979_, v_postNode_980_, v___x_981_, v_x_982_, v_x_983_, v___y_984_, v___y_985_);
stack->m_obj
 = v_res_1012_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_preNode_1013_, lean_object* v_postNode_1014_, lean_object* v___x_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_1013_, v_postNode_1014_, v___x_1015_, v_x_1016_, v_x_1017_, v___y_1018_, v___y_1019_);
lean_dec_ref(v___y_1019_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___boxed(lean_object* v_preNode_1022_, lean_object* v_postNode_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_1022_, v_postNode_1023_, v_x_1024_, v_x_1025_, v___y_1026_, v___y_1027_);
lean_dec_ref(v___y_1027_);
return v_res_1029_;
}
}
lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(lean_object* v_preNode_1030_, lean_object* v_postNode_1031_, lean_object* v_ctx_x3f_1032_, lean_object* v_t_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___f_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___f_1037_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1037_, 0, v_postNode_1031_);
v___x_1038_ = lean_box(0);
v___x_1039_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_1030_, v___f_1037_, v_ctx_x3f_1032_, v_t_1033_, v___y_1034_, v___y_1035_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1056_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1056_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1056_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v_snd_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1054_; 
v_snd_1044_ = lean_ctor_get(v_a_1040_, 1);
v_isSharedCheck_1054_ = !lean_is_exclusive(v_a_1040_);
if (v_isSharedCheck_1054_ == 0)
{
lean_object* v_unused_1055_; 
v_unused_1055_ = lean_ctor_get(v_a_1040_, 0);
lean_dec(v_unused_1055_);
v___x_1046_ = v_a_1040_;
v_isShared_1047_ = v_isSharedCheck_1054_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_snd_1044_);
lean_dec(v_a_1040_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1054_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 0, v___x_1038_);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v___x_1038_);
lean_ctor_set(v_reuseFailAlloc_1053_, 1, v_snd_1044_);
v___x_1049_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
lean_object* v___x_1051_; 
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1049_);
v___x_1051_ = v___x_1042_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
else
{
lean_object* v_a_1057_; lean_object* v___x_1059_; uint8_t v_isShared_1060_; uint8_t v_isSharedCheck_1064_; 
v_a_1057_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1064_ == 0)
{
v___x_1059_ = v___x_1039_;
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
else
{
lean_inc(v_a_1057_);
lean_dec(v___x_1039_);
v___x_1059_ = lean_box(0);
v_isShared_1060_ = v_isSharedCheck_1064_;
goto v_resetjp_1058_;
}
v_resetjp_1058_:
{
lean_object* v___x_1062_; 
if (v_isShared_1060_ == 0)
{
v___x_1062_ = v___x_1059_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_a_1057_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1030_ = stack[0].m_obj;
lean_object* v_postNode_1031_ = stack[1].m_obj;
lean_object* v_ctx_x3f_1032_ = stack[2].m_obj;
lean_object* v_t_1033_ = stack[3].m_obj;
lean_object* v___y_1034_ = stack[4].m_obj;
lean_object* v___y_1035_ = stack[5].m_obj;
lean_object* v_res_1065_;
v_res_1065_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v_preNode_1030_, v_postNode_1031_, v_ctx_x3f_1032_, v_t_1033_, v___y_1034_, v___y_1035_);
stack->m_obj
 = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___boxed(lean_object* v_preNode_1066_, lean_object* v_postNode_1067_, lean_object* v_ctx_x3f_1068_, lean_object* v_t_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v_preNode_1066_, v_postNode_1067_, v_ctx_x3f_1068_, v_t_1069_, v___y_1070_, v___y_1071_);
lean_dec_ref(v___y_1071_);
return v_res_1073_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(lean_object* v_a_1075_, lean_object* v_b_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_array_1080_; lean_object* v_start_1081_; lean_object* v_stop_1082_; lean_object* v___x_1084_; uint8_t v_isShared_1085_; uint8_t v_isSharedCheck_1105_; 
v_array_1080_ = lean_ctor_get(v_a_1075_, 0);
v_start_1081_ = lean_ctor_get(v_a_1075_, 1);
v_stop_1082_ = lean_ctor_get(v_a_1075_, 2);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_a_1075_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1084_ = v_a_1075_;
v_isShared_1085_ = v_isSharedCheck_1105_;
goto v_resetjp_1083_;
}
else
{
lean_inc(v_stop_1082_);
lean_inc(v_start_1081_);
lean_inc(v_array_1080_);
lean_dec(v_a_1075_);
v___x_1084_ = lean_box(0);
v_isShared_1085_ = v_isSharedCheck_1105_;
goto v_resetjp_1083_;
}
v_resetjp_1083_:
{
uint8_t v___x_1086_; 
v___x_1086_ = lean_nat_dec_lt(v_start_1081_, v_stop_1082_);
if (v___x_1086_ == 0)
{
lean_object* v___x_1087_; lean_object* v___x_1088_; 
lean_del_object(v___x_1084_);
lean_dec(v_stop_1082_);
lean_dec(v_start_1081_);
lean_dec_ref(v_array_1080_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_b_1076_);
lean_ctor_set(v___x_1087_, 1, v___y_1077_);
v___x_1088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1087_);
return v___x_1088_;
}
else
{
lean_object* v___f_1089_; lean_object* v___x_1090_; lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___f_1089_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0));
v___x_1090_ = lean_box(v___x_1086_);
v___f_1091_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1091_, 0, v___x_1090_);
v___x_1092_ = lean_box(0);
v___x_1093_ = lean_unsigned_to_nat(1u);
v___x_1094_ = lean_nat_add(v_start_1081_, v___x_1093_);
lean_inc_ref(v_array_1080_);
if (v_isShared_1085_ == 0)
{
lean_ctor_set(v___x_1084_, 1, v___x_1094_);
v___x_1096_ = v___x_1084_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_array_1080_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_stop_1082_);
v___x_1096_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1097_ = lean_array_fget(v_array_1080_, v_start_1081_);
lean_dec(v_start_1081_);
lean_dec_ref(v_array_1080_);
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v___x_1097_);
v___x_1100_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v___f_1091_, v___f_1089_, v___x_1098_, v___x_1099_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1100_) == 0)
{
lean_object* v_a_1101_; lean_object* v_snd_1102_; 
v_a_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_a_1101_);
lean_dec_ref_known(v___x_1100_, 1);
v_snd_1102_ = lean_ctor_get(v_a_1101_, 1);
lean_inc(v_snd_1102_);
lean_dec(v_a_1101_);
v_a_1075_ = v___x_1096_;
v_b_1076_ = v___x_1092_;
v___y_1077_ = v_snd_1102_;
goto _start;
}
else
{
lean_dec_ref(v___x_1096_);
return v___x_1100_;
}
}
}
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1075_ = stack[0].m_obj;
lean_object* v_b_1076_ = stack[1].m_obj;
lean_object* v___y_1077_ = stack[2].m_obj;
lean_object* v___y_1078_ = stack[3].m_obj;
lean_object* v_res_1106_;
v_res_1106_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_1075_, v_b_1076_, v___y_1077_, v___y_1078_);
stack->m_obj
 = v_res_1106_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___boxed(lean_object* v_a_1107_, lean_object* v_b_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_1107_, v_b_1108_, v___y_1109_, v___y_1110_);
lean_dec_ref(v___y_1110_);
return v_res_1112_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(lean_object* v___x_1113_, uint8_t v_val_1114_, lean_object* v_as_1115_, size_t v_i_1116_, size_t v_stop_1117_, lean_object* v_b_1118_){
_start:
{
lean_object* v___y_1120_; uint8_t v___x_1124_; 
v___x_1124_ = lean_usize_dec_eq(v_i_1116_, v_stop_1117_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v_position_1126_; uint8_t v___x_1127_; 
v___x_1125_ = lean_array_uget_borrowed(v_as_1115_, v_i_1116_);
v_position_1126_ = lean_ctor_get(v___x_1125_, 0);
v___x_1127_ = l_Lean_Syntax_Range_contains(v___x_1113_, v_position_1126_, v_val_1114_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_inc(v___x_1125_);
v___x_1128_ = lean_array_push(v_b_1118_, v___x_1125_);
v___y_1120_ = v___x_1128_;
goto v___jp_1119_;
}
else
{
v___y_1120_ = v_b_1118_;
goto v___jp_1119_;
}
}
else
{
return v_b_1118_;
}
v___jp_1119_:
{
size_t v___x_1121_; size_t v___x_1122_; 
v___x_1121_ = ((size_t)1ULL);
v___x_1122_ = lean_usize_add(v_i_1116_, v___x_1121_);
v_i_1116_ = v___x_1122_;
v_b_1118_ = v___y_1120_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1113_ = stack[0].m_obj;
uint8_t v_val_1114_ = stack[1].m_num;
lean_object* v_as_1115_ = stack[2].m_obj;
size_t v_i_1116_ = stack[3].m_num;
size_t v_stop_1117_ = stack[4].m_num;
lean_object* v_b_1118_ = stack[5].m_obj;
lean_object* v_res_1129_;
v_res_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1113_, v_val_1114_, v_as_1115_, v_i_1116_, v_stop_1117_, v_b_1118_);
stack->m_obj
 = v_res_1129_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5___boxed(lean_object* v___x_1130_, lean_object* v_val_1131_, lean_object* v_as_1132_, lean_object* v_i_1133_, lean_object* v_stop_1134_, lean_object* v_b_1135_){
_start:
{
uint8_t v_val_18585__boxed_1136_; size_t v_i_boxed_1137_; size_t v_stop_boxed_1138_; lean_object* v_res_1139_; 
v_val_18585__boxed_1136_ = lean_unbox(v_val_1131_);
v_i_boxed_1137_ = lean_unbox_usize(v_i_1133_);
lean_dec(v_i_1133_);
v_stop_boxed_1138_ = lean_unbox_usize(v_stop_1134_);
lean_dec(v_stop_1134_);
v_res_1139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1130_, v_val_18585__boxed_1136_, v_as_1132_, v_i_boxed_1137_, v_stop_boxed_1138_, v_b_1135_);
lean_dec_ref(v_as_1132_);
lean_dec_ref(v___x_1130_);
return v_res_1139_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(lean_object* v___x_1140_, lean_object* v_as_1141_, size_t v_i_1142_, size_t v_stop_1143_, lean_object* v_b_1144_){
_start:
{
lean_object* v___y_1146_; uint8_t v___x_1150_; 
v___x_1150_ = lean_usize_dec_eq(v_i_1142_, v_stop_1143_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v_position_1152_; uint8_t v___x_1153_; uint8_t v___x_1154_; 
v___x_1151_ = lean_array_uget_borrowed(v_as_1141_, v_i_1142_);
v_position_1152_ = lean_ctor_get(v___x_1151_, 0);
v___x_1153_ = 1;
v___x_1154_ = l_Lean_Syntax_Range_contains(v___x_1140_, v_position_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
v___y_1146_ = v_b_1144_;
goto v___jp_1145_;
}
else
{
lean_object* v___x_1155_; 
lean_inc(v___x_1151_);
v___x_1155_ = lean_array_push(v_b_1144_, v___x_1151_);
v___y_1146_ = v___x_1155_;
goto v___jp_1145_;
}
}
else
{
return v_b_1144_;
}
v___jp_1145_:
{
size_t v___x_1147_; size_t v___x_1148_; 
v___x_1147_ = ((size_t)1ULL);
v___x_1148_ = lean_usize_add(v_i_1142_, v___x_1147_);
v_i_1142_ = v___x_1148_;
v_b_1144_ = v___y_1146_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1140_ = stack[0].m_obj;
lean_object* v_as_1141_ = stack[1].m_obj;
size_t v_i_1142_ = stack[2].m_num;
size_t v_stop_1143_ = stack[3].m_num;
lean_object* v_b_1144_ = stack[4].m_obj;
lean_object* v_res_1156_;
v_res_1156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1140_, v_as_1141_, v_i_1142_, v_stop_1143_, v_b_1144_);
stack->m_obj
 = v_res_1156_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___boxed(lean_object* v___x_1157_, lean_object* v_as_1158_, lean_object* v_i_1159_, lean_object* v_stop_1160_, lean_object* v_b_1161_){
_start:
{
size_t v_i_boxed_1162_; size_t v_stop_boxed_1163_; lean_object* v_res_1164_; 
v_i_boxed_1162_ = lean_unbox_usize(v_i_1159_);
lean_dec(v_i_1159_);
v_stop_boxed_1163_ = lean_unbox_usize(v_stop_1160_);
lean_dec(v_stop_1160_);
v_res_1164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1157_, v_as_1158_, v_i_boxed_1162_, v_stop_boxed_1163_, v_b_1161_);
lean_dec_ref(v_as_1158_);
lean_dec_ref(v___x_1157_);
return v_res_1164_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(lean_object* v___x_1165_, size_t v_sz_1166_, size_t v_i_1167_, lean_object* v_bs_1168_){
_start:
{
uint8_t v___x_1170_; 
v___x_1170_ = lean_usize_dec_lt(v_i_1167_, v_sz_1166_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_dec_ref(v___x_1165_);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v_bs_1168_);
return v___x_1171_;
}
else
{
lean_object* v_v_1172_; lean_object* v___x_1173_; lean_object* v_bs_x27_1174_; lean_object* v___x_1175_; 
v_v_1172_ = lean_array_uget(v_bs_1168_, v_i_1167_);
v___x_1173_ = lean_unsigned_to_nat(0u);
v_bs_x27_1174_ = lean_array_uset(v_bs_1168_, v_i_1167_, v___x_1173_);
lean_inc_ref(v___x_1165_);
v___x_1175_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v___x_1165_, v_v_1172_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; size_t v___x_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
v___x_1177_ = ((size_t)1ULL);
v___x_1178_ = lean_usize_add(v_i_1167_, v___x_1177_);
v___x_1179_ = lean_array_uset(v_bs_x27_1174_, v_i_1167_, v_a_1176_);
v_i_1167_ = v___x_1178_;
v_bs_1168_ = v___x_1179_;
goto _start;
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1189_; 
lean_dec_ref(v_bs_x27_1174_);
lean_dec_ref(v___x_1165_);
v_a_1181_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1189_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1189_ == 0)
{
v___x_1183_ = v___x_1175_;
v_isShared_1184_ = v_isSharedCheck_1189_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1175_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1189_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; lean_object* v___x_1187_; 
v___x_1185_ = l_Lean_Server_RequestError_ofIoError(v_a_1181_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1185_);
v___x_1187_ = v___x_1183_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v___x_1185_);
v___x_1187_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
return v___x_1187_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1165_ = stack[0].m_obj;
size_t v_sz_1166_ = stack[1].m_num;
size_t v_i_1167_ = stack[2].m_num;
lean_object* v_bs_1168_ = stack[3].m_obj;
lean_object* v_res_1190_;
v_res_1190_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_1165_, v_sz_1166_, v_i_1167_, v_bs_1168_);
stack->m_obj
 = v_res_1190_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg___boxed(lean_object* v___x_1191_, lean_object* v_sz_1192_, lean_object* v_i_1193_, lean_object* v_bs_1194_, lean_object* v___y_1195_){
_start:
{
size_t v_sz_boxed_1196_; size_t v_i_boxed_1197_; lean_object* v_res_1198_; 
v_sz_boxed_1196_ = lean_unbox_usize(v_sz_1192_);
lean_dec(v_sz_1192_);
v_i_boxed_1197_ = lean_unbox_usize(v_i_1193_);
lean_dec(v_i_1193_);
v_res_1198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_1191_, v_sz_boxed_1196_, v_i_boxed_1197_, v_bs_1194_);
return v_res_1198_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1201_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__1));
v___x_1202_ = lean_unsigned_to_nat(2u);
v___x_1203_ = lean_unsigned_to_nat(162u);
v___x_1204_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__0));
v___x_1205_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_1206_ = l_mkPanicMessageWithDecl(v___x_1205_, v___x_1204_, v___x_1203_, v___x_1202_, v___x_1201_);
return v___x_1206_;
}
}
lean_object* l_Lean_Server_FileWorker_handleInlayHints(lean_object* v_p_1207_, lean_object* v_s_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v_doc_1211_; lean_object* v_toEditableDocumentCore_1212_; lean_object* v_meta_1213_; lean_object* v_cancelTk_1214_; lean_object* v_cmdSnaps_1215_; lean_object* v_text_1216_; lean_object* v_oldInlayHints_1217_; lean_object* v_oldFinishedSnaps_1218_; lean_object* v_lastEditTimestamp_x3f_1219_; uint8_t v_isFirstRequestAfterEdit_1220_; uint8_t v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; 
v_doc_1211_ = lean_ctor_get(v_a_1209_, 1);
v_toEditableDocumentCore_1212_ = lean_ctor_get(v_doc_1211_, 0);
v_meta_1213_ = lean_ctor_get(v_toEditableDocumentCore_1212_, 0);
v_cancelTk_1214_ = lean_ctor_get(v_a_1209_, 4);
v_cmdSnaps_1215_ = lean_ctor_get(v_toEditableDocumentCore_1212_, 2);
v_text_1216_ = lean_ctor_get(v_meta_1213_, 3);
v_oldInlayHints_1217_ = lean_ctor_get(v_s_1208_, 0);
v_oldFinishedSnaps_1218_ = lean_ctor_get(v_s_1208_, 1);
v_lastEditTimestamp_x3f_1219_ = lean_ctor_get(v_s_1208_, 2);
v_isFirstRequestAfterEdit_1220_ = lean_ctor_get_uint8(v_s_1208_, sizeof(void*)*3);
if (v_isFirstRequestAfterEdit_1220_ == 0)
{
lean_object* v_range_1248_; lean_object* v___x_1249_; uint8_t v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; lean_object* v___y_1254_; lean_object* v_snd_1255_; lean_object* v___y_1268_; uint8_t v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v_lower_1273_; lean_object* v_upper_1274_; lean_object* v___y_1292_; uint8_t v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1299_; uint8_t v___y_1300_; uint8_t v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1318_; uint8_t v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; uint8_t v___y_1322_; lean_object* v___y_1323_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___y_1332_; 
v_range_1248_ = lean_ctor_get(v_p_1207_, 2);
lean_inc_ref(v_range_1248_);
lean_dec_ref(v_p_1207_);
v___x_1249_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_1216_, v_range_1248_);
v___x_1329_ = lean_unsigned_to_nat(3000u);
v___x_1330_ = lean_io_mono_ms_now();
if (lean_obj_tag(v_lastEditTimestamp_x3f_1219_) == 0)
{
lean_object* v___x_1381_; 
lean_dec(v___x_1330_);
v___x_1381_ = lean_unsigned_to_nat(0u);
v___y_1332_ = v___x_1381_;
goto v___jp_1331_;
}
else
{
lean_object* v_val_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_val_1382_ = lean_ctor_get(v_lastEditTimestamp_x3f_1219_, 0);
v___x_1383_ = lean_nat_sub(v___x_1330_, v_val_1382_);
lean_dec(v___x_1330_);
v___x_1384_ = lean_nat_sub(v___x_1329_, v___x_1383_);
lean_dec(v___x_1383_);
v___y_1332_ = v___x_1384_;
goto v___jp_1331_;
}
v___jp_1250_:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v___x_1256_ = l_Array_append___redArg(v_snd_1255_, v___y_1254_);
lean_dec_ref(v___y_1254_);
v___x_1257_ = lean_array_get_size(v___x_1256_);
v___x_1258_ = lean_mk_empty_array_with_capacity(v___y_1253_);
v___x_1259_ = lean_nat_dec_lt(v___y_1253_, v___x_1257_);
lean_dec(v___y_1253_);
if (v___x_1259_ == 0)
{
lean_dec_ref(v___x_1249_);
v___y_1222_ = v___y_1251_;
v___y_1223_ = v___y_1252_;
v___y_1224_ = v___x_1256_;
v___y_1225_ = v___x_1258_;
goto v___jp_1221_;
}
else
{
uint8_t v___x_1260_; 
v___x_1260_ = lean_nat_dec_le(v___x_1257_, v___x_1257_);
if (v___x_1260_ == 0)
{
if (v___x_1259_ == 0)
{
lean_dec_ref(v___x_1249_);
v___y_1222_ = v___y_1251_;
v___y_1223_ = v___y_1252_;
v___y_1224_ = v___x_1256_;
v___y_1225_ = v___x_1258_;
goto v___jp_1221_;
}
else
{
size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v___x_1261_ = ((size_t)0ULL);
v___x_1262_ = lean_usize_of_nat(v___x_1257_);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1249_, v___x_1256_, v___x_1261_, v___x_1262_, v___x_1258_);
lean_dec_ref(v___x_1249_);
v___y_1222_ = v___y_1251_;
v___y_1223_ = v___y_1252_;
v___y_1224_ = v___x_1256_;
v___y_1225_ = v___x_1263_;
goto v___jp_1221_;
}
}
else
{
size_t v___x_1264_; size_t v___x_1265_; lean_object* v___x_1266_; 
v___x_1264_ = ((size_t)0ULL);
v___x_1265_ = lean_usize_of_nat(v___x_1257_);
v___x_1266_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1249_, v___x_1256_, v___x_1264_, v___x_1265_, v___x_1258_);
lean_dec_ref(v___x_1249_);
v___y_1222_ = v___y_1251_;
v___y_1223_ = v___y_1252_;
v___y_1224_ = v___x_1256_;
v___y_1225_ = v___x_1266_;
goto v___jp_1221_;
}
}
}
v___jp_1267_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = l_Array_toSubarray___redArg(v___y_1268_, v_lower_1273_, v_upper_1274_);
v___x_1276_ = lean_box(0);
v___x_1277_ = lean_mk_empty_array_with_capacity(v___y_1272_);
v___x_1278_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v___x_1275_, v___x_1276_, v___x_1277_, v_a_1209_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v_snd_1280_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v_snd_1280_ = lean_ctor_get(v_a_1279_, 1);
lean_inc(v_snd_1280_);
lean_dec(v_a_1279_);
v___y_1251_ = v___y_1269_;
v___y_1252_ = v___y_1270_;
v___y_1253_ = v___y_1272_;
v___y_1254_ = v___y_1271_;
v_snd_1255_ = v_snd_1280_;
goto v___jp_1250_;
}
else
{
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1281_; lean_object* v_snd_1282_; 
v_a_1281_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1278_, 1);
v_snd_1282_ = lean_ctor_get(v_a_1281_, 1);
lean_inc(v_snd_1282_);
lean_dec(v_a_1281_);
v___y_1251_ = v___y_1269_;
v___y_1252_ = v___y_1270_;
v___y_1253_ = v___y_1272_;
v___y_1254_ = v___y_1271_;
v_snd_1255_ = v_snd_1282_;
goto v___jp_1250_;
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___x_1249_);
lean_dec(v_lastEditTimestamp_x3f_1219_);
v_a_1283_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1278_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1278_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
v___jp_1291_:
{
uint8_t v___x_1297_; 
v___x_1297_ = lean_nat_dec_le(v_oldFinishedSnaps_1218_, v___y_1295_);
if (v___x_1297_ == 0)
{
lean_inc(v___y_1294_);
v___y_1268_ = v___y_1292_;
v___y_1269_ = v___y_1293_;
v___y_1270_ = v___y_1294_;
v___y_1271_ = v___y_1296_;
v___y_1272_ = v___y_1295_;
v_lower_1273_ = v_oldFinishedSnaps_1218_;
v_upper_1274_ = v___y_1294_;
goto v___jp_1267_;
}
else
{
lean_dec(v_oldFinishedSnaps_1218_);
lean_inc(v___y_1295_);
lean_inc(v___y_1294_);
v___y_1268_ = v___y_1292_;
v___y_1269_ = v___y_1293_;
v___y_1270_ = v___y_1294_;
v___y_1271_ = v___y_1296_;
v___y_1272_ = v___y_1295_;
v_lower_1273_ = v___y_1295_;
v_upper_1274_ = v___y_1294_;
goto v___jp_1267_;
}
}
v___jp_1298_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_array_get_size(v_oldInlayHints_1217_);
v___x_1307_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init___closed__0));
v___x_1308_ = lean_nat_dec_lt(v___x_1305_, v___x_1306_);
if (v___x_1308_ == 0)
{
lean_dec(v___y_1304_);
lean_dec(v___y_1303_);
lean_dec_ref(v_oldInlayHints_1217_);
v___y_1292_ = v___y_1299_;
v___y_1293_ = v___y_1300_;
v___y_1294_ = v___y_1302_;
v___y_1295_ = v___x_1305_;
v___y_1296_ = v___x_1307_;
goto v___jp_1291_;
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1309_, 0, v___y_1303_);
lean_ctor_set(v___x_1309_, 1, v___y_1304_);
v___x_1310_ = lean_nat_dec_le(v___x_1306_, v___x_1306_);
if (v___x_1310_ == 0)
{
if (v___x_1308_ == 0)
{
lean_dec_ref_known(v___x_1309_, 2);
lean_dec_ref(v_oldInlayHints_1217_);
v___y_1292_ = v___y_1299_;
v___y_1293_ = v___y_1300_;
v___y_1294_ = v___y_1302_;
v___y_1295_ = v___x_1305_;
v___y_1296_ = v___x_1307_;
goto v___jp_1291_;
}
else
{
size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1306_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1309_, v___y_1301_, v_oldInlayHints_1217_, v___x_1311_, v___x_1312_, v___x_1307_);
lean_dec_ref(v_oldInlayHints_1217_);
lean_dec_ref_known(v___x_1309_, 2);
v___y_1292_ = v___y_1299_;
v___y_1293_ = v___y_1300_;
v___y_1294_ = v___y_1302_;
v___y_1295_ = v___x_1305_;
v___y_1296_ = v___x_1313_;
goto v___jp_1291_;
}
}
else
{
size_t v___x_1314_; size_t v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = ((size_t)0ULL);
v___x_1315_ = lean_usize_of_nat(v___x_1306_);
v___x_1316_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1309_, v___y_1301_, v_oldInlayHints_1217_, v___x_1314_, v___x_1315_, v___x_1307_);
lean_dec_ref(v_oldInlayHints_1217_);
lean_dec_ref_known(v___x_1309_, 2);
v___y_1292_ = v___y_1299_;
v___y_1293_ = v___y_1300_;
v___y_1294_ = v___y_1302_;
v___y_1295_ = v___x_1305_;
v___y_1296_ = v___x_1316_;
goto v___jp_1291_;
}
}
}
v___jp_1317_:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = lean_nat_sub(v___y_1321_, v___y_1320_);
v___x_1325_ = lean_nat_dec_lt(v___x_1324_, v___y_1321_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; 
lean_dec(v___x_1324_);
v___x_1326_ = lean_unsigned_to_nat(0u);
v___y_1299_ = v___y_1318_;
v___y_1300_ = v___y_1319_;
v___y_1301_ = v___y_1322_;
v___y_1302_ = v___y_1321_;
v___y_1303_ = v___y_1323_;
v___y_1304_ = v___x_1326_;
goto v___jp_1298_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___x_1327_ = lean_array_fget_borrowed(v___y_1318_, v___x_1324_);
lean_dec(v___x_1324_);
v___x_1328_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1327_);
v___y_1299_ = v___y_1318_;
v___y_1300_ = v___y_1319_;
v___y_1301_ = v___y_1322_;
v___y_1302_ = v___y_1321_;
v___y_1303_ = v___y_1323_;
v___y_1304_ = v___x_1328_;
goto v___jp_1298_;
}
}
v___jp_1331_:
{
uint32_t v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v_snd_1336_; lean_object* v_fst_1337_; lean_object* v_snd_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1379_; 
v___x_1333_ = lean_uint32_of_nat(v___y_1332_);
lean_dec(v___y_1332_);
v___x_1334_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_1214_);
lean_inc(v_cmdSnaps_1215_);
v___x_1335_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_cmdSnaps_1215_, v___x_1333_, v___x_1334_);
v_snd_1336_ = lean_ctor_get(v___x_1335_, 1);
lean_inc(v_snd_1336_);
v_fst_1337_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_fst_1337_);
lean_dec_ref(v___x_1335_);
v_snd_1338_ = lean_ctor_get(v_snd_1336_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_snd_1336_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v_snd_1336_, 0);
lean_dec(v_unused_1380_);
v___x_1340_ = v_snd_1336_;
v_isShared_1341_ = v_isSharedCheck_1379_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_snd_1338_);
lean_dec(v_snd_1336_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1379_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
uint8_t v___x_1342_; 
v___x_1342_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_cancelTk_1214_);
if (v___x_1342_ == 0)
{
lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
lean_inc(v_lastEditTimestamp_x3f_1219_);
lean_inc(v_oldFinishedSnaps_1218_);
lean_inc_ref(v_oldInlayHints_1217_);
lean_del_object(v___x_1340_);
lean_dec_ref(v_s_1208_);
v___x_1343_ = lean_array_mk(v_fst_1337_);
v___x_1344_ = lean_array_get_size(v___x_1343_);
v___x_1345_ = lean_nat_dec_le(v_oldFinishedSnaps_1218_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; lean_object* v___x_1347_; 
lean_dec_ref(v___x_1343_);
lean_dec(v_snd_1338_);
lean_dec_ref(v___x_1249_);
lean_dec(v_lastEditTimestamp_x3f_1219_);
lean_dec(v_oldFinishedSnaps_1218_);
lean_dec_ref(v_oldInlayHints_1217_);
v___x_1346_ = lean_obj_once(&l_Lean_Server_FileWorker_handleInlayHints___closed__2, &l_Lean_Server_FileWorker_handleInlayHints___closed__2_once, _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2);
v___x_1347_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v___x_1346_, v_a_1209_);
return v___x_1347_;
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v___x_1348_ = lean_unsigned_to_nat(1u);
v___x_1349_ = lean_nat_sub(v_oldFinishedSnaps_1218_, v___x_1348_);
v___x_1350_ = lean_nat_dec_lt(v___x_1349_, v___x_1344_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; uint8_t v___x_1352_; 
lean_dec(v___x_1349_);
v___x_1351_ = lean_unsigned_to_nat(0u);
v___x_1352_ = lean_unbox(v_snd_1338_);
lean_dec(v_snd_1338_);
v___y_1318_ = v___x_1343_;
v___y_1319_ = v___x_1352_;
v___y_1320_ = v___x_1348_;
v___y_1321_ = v___x_1344_;
v___y_1322_ = v___x_1342_;
v___y_1323_ = v___x_1351_;
goto v___jp_1317_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v___x_1353_ = lean_array_fget_borrowed(v___x_1343_, v___x_1349_);
lean_dec(v___x_1349_);
v___x_1354_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1353_);
v___x_1355_ = lean_unbox(v_snd_1338_);
lean_dec(v_snd_1338_);
v___y_1318_ = v___x_1343_;
v___y_1319_ = v___x_1355_;
v___y_1320_ = v___x_1348_;
v___y_1321_ = v___x_1344_;
v___y_1322_ = v___x_1342_;
v___y_1323_ = v___x_1354_;
goto v___jp_1317_;
}
}
}
else
{
size_t v_sz_1356_; size_t v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_snd_1338_);
lean_dec(v_fst_1337_);
lean_dec_ref(v___x_1249_);
v_sz_1356_ = lean_array_size(v_oldInlayHints_1217_);
v___x_1357_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1217_);
lean_inc_ref(v_text_1216_);
v___x_1358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1216_, v_sz_1356_, v___x_1357_, v_oldInlayHints_1217_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1370_; 
v_a_1359_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1361_ = v___x_1358_;
v_isShared_1362_ = v_isSharedCheck_1370_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1358_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1370_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1363_, 0, v_a_1359_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*1, v_isFirstRequestAfterEdit_1220_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 1, v_s_1208_);
lean_ctor_set(v___x_1340_, 0, v___x_1363_);
v___x_1365_ = v___x_1340_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_s_1208_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1362_ == 0)
{
lean_ctor_set(v___x_1361_, 0, v___x_1365_);
v___x_1367_ = v___x_1361_;
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
lean_del_object(v___x_1340_);
lean_dec_ref(v_s_1208_);
v_a_1371_ = lean_ctor_get(v___x_1358_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1358_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1358_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1358_);
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
}
}
else
{
lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1413_; 
lean_inc(v_lastEditTimestamp_x3f_1219_);
lean_inc(v_oldFinishedSnaps_1218_);
lean_inc_ref(v_oldInlayHints_1217_);
lean_dec_ref(v_p_1207_);
v_isSharedCheck_1413_ = !lean_is_exclusive(v_s_1208_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; lean_object* v_unused_1415_; lean_object* v_unused_1416_; 
v_unused_1414_ = lean_ctor_get(v_s_1208_, 2);
lean_dec(v_unused_1414_);
v_unused_1415_ = lean_ctor_get(v_s_1208_, 1);
lean_dec(v_unused_1415_);
v_unused_1416_ = lean_ctor_get(v_s_1208_, 0);
lean_dec(v_unused_1416_);
v___x_1386_ = v_s_1208_;
v_isShared_1387_ = v_isSharedCheck_1413_;
goto v_resetjp_1385_;
}
else
{
lean_dec(v_s_1208_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1413_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
size_t v_sz_1388_; size_t v___x_1389_; lean_object* v___x_1390_; 
v_sz_1388_ = lean_array_size(v_oldInlayHints_1217_);
v___x_1389_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1217_);
lean_inc_ref(v_text_1216_);
v___x_1390_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1216_, v_sz_1388_, v___x_1389_, v_oldInlayHints_1217_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1393_; uint8_t v_isShared_1394_; uint8_t v_isSharedCheck_1404_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1393_ = v___x_1390_;
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
else
{
lean_inc(v_a_1391_);
lean_dec(v___x_1390_);
v___x_1393_ = lean_box(0);
v_isShared_1394_ = v_isSharedCheck_1404_;
goto v_resetjp_1392_;
}
v_resetjp_1392_:
{
uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1395_ = 0;
v___x_1396_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1396_, 0, v_a_1391_);
lean_ctor_set_uint8(v___x_1396_, sizeof(void*)*1, v___x_1395_);
if (v_isShared_1387_ == 0)
{
v___x_1398_ = v___x_1386_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_oldInlayHints_1217_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v_oldFinishedSnaps_1218_);
lean_ctor_set(v_reuseFailAlloc_1403_, 2, v_lastEditTimestamp_x3f_1219_);
v___x_1398_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*3, v___x_1395_);
v___x_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1396_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
if (v_isShared_1394_ == 0)
{
lean_ctor_set(v___x_1393_, 0, v___x_1399_);
v___x_1401_ = v___x_1393_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v___x_1399_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_del_object(v___x_1386_);
lean_dec(v_lastEditTimestamp_x3f_1219_);
lean_dec(v_oldFinishedSnaps_1218_);
lean_dec_ref(v_oldInlayHints_1217_);
v_a_1405_ = lean_ctor_get(v___x_1390_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1390_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1390_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1390_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
v___jp_1221_:
{
size_t v_sz_1226_; size_t v___x_1227_; lean_object* v___x_1228_; 
v_sz_1226_ = lean_array_size(v___y_1225_);
v___x_1227_ = ((size_t)0ULL);
lean_inc_ref(v_text_1216_);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1216_, v_sz_1226_, v___x_1227_, v___y_1225_);
if (lean_obj_tag(v___x_1228_) == 0)
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1239_; 
v_a_1229_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1231_ = v___x_1228_;
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1228_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1233_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1233_, 0, v_a_1229_);
lean_ctor_set_uint8(v___x_1233_, sizeof(void*)*1, v___y_1222_);
v___x_1234_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1234_, 0, v___y_1224_);
lean_ctor_set(v___x_1234_, 1, v___y_1223_);
lean_ctor_set(v___x_1234_, 2, v_lastEditTimestamp_x3f_1219_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*3, v_isFirstRequestAfterEdit_1220_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1235_);
v___x_1237_ = v___x_1231_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1235_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v_lastEditTimestamp_x3f_1219_);
v_a_1240_ = lean_ctor_get(v___x_1228_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1228_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1228_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1228_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleInlayHints_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1207_ = stack[0].m_obj;
lean_object* v_s_1208_ = stack[1].m_obj;
lean_object* v_a_1209_ = stack[2].m_obj;
lean_object* v_res_1417_;
v_res_1417_ = l_Lean_Server_FileWorker_handleInlayHints(v_p_1207_, v_s_1208_, v_a_1209_);
stack->m_obj
 = v_res_1417_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints___boxed(lean_object* v_p_1418_, lean_object* v_s_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Server_FileWorker_handleInlayHints(v_p_1418_, v_s_1419_, v_a_1420_);
lean_dec_ref(v_a_1420_);
return v_res_1422_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(lean_object* v___x_1423_, size_t v_sz_1424_, size_t v_i_1425_, lean_object* v_bs_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_1423_, v_sz_1424_, v_i_1425_, v_bs_1426_);
return v___x_1429_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1423_ = stack[0].m_obj;
size_t v_sz_1424_ = stack[1].m_num;
size_t v_i_1425_ = stack[2].m_num;
lean_object* v_bs_1426_ = stack[3].m_obj;
lean_object* v___y_1427_ = stack[4].m_obj;
lean_object* v_res_1430_;
v_res_1430_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(v___x_1423_, v_sz_1424_, v_i_1425_, v_bs_1426_, v___y_1427_);
stack->m_obj
 = v_res_1430_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___boxed(lean_object* v___x_1431_, lean_object* v_sz_1432_, lean_object* v_i_1433_, lean_object* v_bs_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_){
_start:
{
size_t v_sz_boxed_1437_; size_t v_i_boxed_1438_; lean_object* v_res_1439_; 
v_sz_boxed_1437_ = lean_unbox_usize(v_sz_1432_);
lean_dec(v_sz_1432_);
v_i_boxed_1438_ = lean_unbox_usize(v_i_1433_);
lean_dec(v_i_1433_);
v_res_1439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(v___x_1431_, v_sz_boxed_1437_, v_i_boxed_1438_, v_bs_1434_, v___y_1435_);
lean_dec_ref(v___y_1435_);
return v_res_1439_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(lean_object* v_inst_1440_, lean_object* v_R_1441_, lean_object* v_a_1442_, lean_object* v_b_1443_, lean_object* v_c_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_1442_, v_b_1443_, v___y_1445_, v___y_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1442_ = stack[2].m_obj;
lean_object* v_b_1443_ = stack[3].m_obj;
lean_object* v___y_1445_ = stack[5].m_obj;
lean_object* v___y_1446_ = stack[6].m_obj;
lean_object* v_res_1449_;
v_res_1449_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(lean_box(0), lean_box(0), v_a_1442_, v_b_1443_, lean_box(0), v___y_1445_, v___y_1446_);
stack->m_obj
 = v_res_1449_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___boxed(lean_object* v_inst_1450_, lean_object* v_R_1451_, lean_object* v_a_1452_, lean_object* v_b_1453_, lean_object* v_c_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(v_inst_1450_, v_R_1451_, v_a_1452_, v_b_1453_, v_c_1454_, v___y_1455_, v___y_1456_);
lean_dec_ref(v___y_1456_);
return v_res_1458_;
}
}
lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_1459_, lean_object* v_msg_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_){
_start:
{
lean_object* v___x_1464_; 
v___x_1464_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_1460_, v___y_1461_, v___y_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT void l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1460_ = stack[1].m_obj;
lean_object* v___y_1461_ = stack[2].m_obj;
lean_object* v___y_1462_ = stack[3].m_obj;
lean_object* v_res_1465_;
v_res_1465_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(lean_box(0), v_msg_1460_, v___y_1461_, v___y_1462_);
stack->m_obj
 = v_res_1465_;
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1466_, lean_object* v_msg_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(v_00_u03b1_1466_, v_msg_1467_, v___y_1468_, v___y_1469_);
lean_dec_ref(v___y_1469_);
return v_res_1471_;
}
}
lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(lean_object* v_00_u03b1_1472_, lean_object* v_preNode_1473_, lean_object* v_postNode_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_1473_, v_postNode_1474_, v_x_1475_, v_x_1476_, v___y_1477_, v___y_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1473_ = stack[1].m_obj;
lean_object* v_postNode_1474_ = stack[2].m_obj;
lean_object* v_x_1475_ = stack[3].m_obj;
lean_object* v_x_1476_ = stack[4].m_obj;
lean_object* v___y_1477_ = stack[5].m_obj;
lean_object* v___y_1478_ = stack[6].m_obj;
lean_object* v_res_1481_;
v_res_1481_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(lean_box(0), v_preNode_1473_, v_postNode_1474_, v_x_1475_, v_x_1476_, v___y_1477_, v___y_1478_);
stack->m_obj
 = v_res_1481_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1482_, lean_object* v_preNode_1483_, lean_object* v_postNode_1484_, lean_object* v_x_1485_, lean_object* v_x_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_res_1490_; 
v_res_1490_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(v_00_u03b1_1482_, v_preNode_1483_, v_postNode_1484_, v_x_1485_, v_x_1486_, v___y_1487_, v___y_1488_);
lean_dec_ref(v___y_1488_);
return v_res_1490_;
}
}
lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(lean_object* v_00_u03b1_1491_, lean_object* v_preNode_1492_, lean_object* v_postNode_1493_, lean_object* v___x_1494_, lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_1492_, v_postNode_1493_, v___x_1494_, v_x_1495_, v_x_1496_, v___y_1497_, v___y_1498_);
return v___x_1500_;
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_preNode_1492_ = stack[1].m_obj;
lean_object* v_postNode_1493_ = stack[2].m_obj;
lean_object* v___x_1494_ = stack[3].m_obj;
lean_object* v_x_1495_ = stack[4].m_obj;
lean_object* v_x_1496_ = stack[5].m_obj;
lean_object* v___y_1497_ = stack[6].m_obj;
lean_object* v___y_1498_ = stack[7].m_obj;
lean_object* v_res_1501_;
v_res_1501_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(lean_box(0), v_preNode_1492_, v_postNode_1493_, v___x_1494_, v_x_1495_, v_x_1496_, v___y_1497_, v___y_1498_);
stack->m_obj
 = v_res_1501_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1502_, lean_object* v_preNode_1503_, lean_object* v_postNode_1504_, lean_object* v___x_1505_, lean_object* v_x_1506_, lean_object* v_x_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(v_00_u03b1_1502_, v_preNode_1503_, v_postNode_1504_, v___x_1505_, v_x_1506_, v_x_1507_, v___y_1508_, v___y_1509_);
lean_dec_ref(v___y_1509_);
return v_res_1511_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(lean_object* v___x_1514_, lean_object* v___x_1515_, lean_object* v_as_1516_, size_t v_sz_1517_, size_t v_i_1518_, lean_object* v_b_1519_){
_start:
{
uint8_t v___x_1521_; 
v___x_1521_ = lean_usize_dec_lt(v_i_1518_, v_sz_1517_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v_b_1519_);
return v___x_1522_;
}
else
{
lean_object* v_snd_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1566_; 
v_snd_1523_ = lean_ctor_get(v_b_1519_, 1);
v_isSharedCheck_1566_ = !lean_is_exclusive(v_b_1519_);
if (v_isSharedCheck_1566_ == 0)
{
lean_object* v_unused_1567_; 
v_unused_1567_ = lean_ctor_get(v_b_1519_, 0);
lean_dec(v_unused_1567_);
v___x_1525_ = v_b_1519_;
v_isShared_1526_ = v_isSharedCheck_1566_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_snd_1523_);
lean_dec(v_b_1519_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1566_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v_fst_1527_; lean_object* v_snd_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1565_; 
v_fst_1527_ = lean_ctor_get(v_snd_1523_, 0);
v_snd_1528_ = lean_ctor_get(v_snd_1523_, 1);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_snd_1523_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1530_ = v_snd_1523_;
v_isShared_1531_ = v_isSharedCheck_1565_;
goto v_resetjp_1529_;
}
else
{
lean_inc(v_snd_1528_);
lean_inc(v_fst_1527_);
lean_dec(v_snd_1523_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1565_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_a_1532_; 
v_a_1532_ = lean_array_uget_borrowed(v_as_1516_, v_i_1518_);
if (lean_obj_tag(v_a_1532_) == 0)
{
lean_object* v_range_1533_; lean_object* v_text_1534_; lean_object* v_mod_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v_range_1533_ = lean_ctor_get(v_a_1532_, 0);
v_text_1534_ = lean_ctor_get(v_a_1532_, 1);
v_mod_1535_ = lean_ctor_get(v___x_1515_, 1);
v___x_1536_ = lean_box(0);
lean_inc_ref(v_range_1533_);
v___x_1537_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1514_, v_range_1533_);
lean_inc(v_fst_1527_);
v___x_1538_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(v_mod_1535_, v_fst_1527_, v___x_1537_, v_text_1534_);
if (lean_obj_tag(v___x_1538_) == 1)
{
lean_object* v_val_1539_; lean_object* v___x_1541_; 
lean_dec(v_fst_1527_);
v_val_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_val_1539_);
lean_dec_ref_known(v___x_1538_, 1);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v_val_1539_);
v___x_1541_ = v___x_1530_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1548_; 
v_reuseFailAlloc_1548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_val_1539_);
lean_ctor_set(v_reuseFailAlloc_1548_, 1, v_snd_1528_);
v___x_1541_ = v_reuseFailAlloc_1548_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
lean_object* v___x_1543_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v___x_1541_);
lean_ctor_set(v___x_1525_, 0, v___x_1536_);
v___x_1543_ = v___x_1525_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1547_, 1, v___x_1541_);
v___x_1543_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
size_t v___x_1544_; size_t v___x_1545_; 
v___x_1544_ = ((size_t)1ULL);
v___x_1545_ = lean_usize_add(v_i_1518_, v___x_1544_);
v_i_1518_ = v___x_1545_;
v_b_1519_ = v___x_1543_;
goto _start;
}
}
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
lean_dec(v___x_1538_);
lean_dec(v_snd_1528_);
v___x_1549_ = lean_box(v___x_1521_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v___x_1549_);
v___x_1551_ = v___x_1530_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v_fst_1527_);
lean_ctor_set(v_reuseFailAlloc_1556_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1553_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v___x_1551_);
lean_ctor_set(v___x_1525_, 0, v___x_1536_);
v___x_1553_ = v___x_1525_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v___x_1553_);
return v___x_1554_;
}
}
}
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1559_; 
v___x_1557_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0));
if (v_isShared_1531_ == 0)
{
v___x_1559_ = v___x_1530_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_fst_1527_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v_snd_1528_);
v___x_1559_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
lean_object* v___x_1561_; 
if (v_isShared_1526_ == 0)
{
lean_ctor_set(v___x_1525_, 1, v___x_1559_);
lean_ctor_set(v___x_1525_, 0, v___x_1557_);
v___x_1561_ = v___x_1525_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1557_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v___x_1559_);
v___x_1561_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1514_ = stack[0].m_obj;
lean_object* v___x_1515_ = stack[1].m_obj;
lean_object* v_as_1516_ = stack[2].m_obj;
size_t v_sz_1517_ = stack[3].m_num;
size_t v_i_1518_ = stack[4].m_num;
lean_object* v_b_1519_ = stack[5].m_obj;
lean_object* v_res_1568_;
v_res_1568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1514_, v___x_1515_, v_as_1516_, v_sz_1517_, v_i_1518_, v_b_1519_);
stack->m_obj
 = v_res_1568_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___boxed(lean_object* v___x_1569_, lean_object* v___x_1570_, lean_object* v_as_1571_, lean_object* v_sz_1572_, lean_object* v_i_1573_, lean_object* v_b_1574_, lean_object* v___y_1575_){
_start:
{
size_t v_sz_boxed_1576_; size_t v_i_boxed_1577_; lean_object* v_res_1578_; 
v_sz_boxed_1576_ = lean_unbox_usize(v_sz_1572_);
lean_dec(v_sz_1572_);
v_i_boxed_1577_ = lean_unbox_usize(v_i_1573_);
lean_dec(v_i_1573_);
v_res_1578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1569_, v___x_1570_, v_as_1571_, v_sz_boxed_1576_, v_i_boxed_1577_, v_b_1574_);
lean_dec_ref(v_as_1571_);
lean_dec_ref(v___x_1570_);
lean_dec_ref(v___x_1569_);
return v_res_1578_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(lean_object* v_p_1579_, lean_object* v___x_1580_, lean_object* v___x_1581_, lean_object* v_as_1582_, size_t v_sz_1583_, size_t v_i_1584_, lean_object* v_b_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_a_1589_; uint8_t v___x_1593_; 
v___x_1593_ = lean_usize_dec_lt(v_i_1584_, v_sz_1583_);
if (v___x_1593_ == 0)
{
lean_object* v___x_1594_; 
v___x_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1594_, 0, v_b_1585_);
return v___x_1594_;
}
else
{
lean_object* v_snd_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1659_; 
v_snd_1595_ = lean_ctor_get(v_b_1585_, 1);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_b_1585_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; 
v_unused_1660_ = lean_ctor_get(v_b_1585_, 0);
lean_dec(v_unused_1660_);
v___x_1597_ = v_b_1585_;
v_isShared_1598_ = v_isSharedCheck_1659_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_snd_1595_);
lean_dec(v_b_1585_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1659_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_contentChanges_1599_; lean_object* v___x_1600_; lean_object* v_a_1601_; uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1605_; 
v_contentChanges_1599_ = lean_ctor_get(v_p_1579_, 1);
v___x_1600_ = lean_box(0);
v_a_1601_ = lean_array_uget_borrowed(v_as_1582_, v_i_1584_);
v___x_1602_ = 0;
v___x_1603_ = lean_box(v___x_1602_);
lean_inc(v_a_1601_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 1, v___x_1603_);
lean_ctor_set(v___x_1597_, 0, v_a_1601_);
v___x_1605_ = v___x_1597_;
goto v_reusejp_1604_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_a_1601_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1603_);
v___x_1605_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1604_;
}
v_reusejp_1604_:
{
lean_object* v___x_1606_; size_t v_sz_1607_; size_t v___x_1608_; lean_object* v___x_1609_; 
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1600_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v_sz_1607_ = lean_array_size(v_contentChanges_1599_);
v___x_1608_ = ((size_t)0ULL);
v___x_1609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1580_, v___x_1581_, v_contentChanges_1599_, v_sz_1607_, v___x_1608_, v___x_1606_);
if (lean_obj_tag(v___x_1609_) == 0)
{
lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1649_; 
v_a_1610_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1612_ = v___x_1609_;
v_isShared_1613_ = v_isSharedCheck_1649_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v___x_1609_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1649_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v_fst_1614_; 
v_fst_1614_ = lean_ctor_get(v_a_1610_, 0);
if (lean_obj_tag(v_fst_1614_) == 0)
{
lean_object* v_snd_1615_; lean_object* v_snd_1616_; uint8_t v___x_1617_; 
lean_del_object(v___x_1612_);
v_snd_1615_ = lean_ctor_get(v_a_1610_, 1);
lean_inc(v_snd_1615_);
lean_dec(v_a_1610_);
v_snd_1616_ = lean_ctor_get(v_snd_1615_, 1);
v___x_1617_ = lean_unbox(v_snd_1616_);
if (v___x_1617_ == 0)
{
lean_object* v_fst_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1626_; 
v_fst_1618_ = lean_ctor_get(v_snd_1615_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_snd_1615_);
if (v_isSharedCheck_1626_ == 0)
{
lean_object* v_unused_1627_; 
v_unused_1627_ = lean_ctor_get(v_snd_1615_, 1);
lean_dec(v_unused_1627_);
v___x_1620_ = v_snd_1615_;
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_fst_1618_);
lean_dec(v_snd_1615_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1626_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1624_; 
v___x_1622_ = lean_array_push(v_snd_1595_, v_fst_1618_);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 1, v___x_1622_);
lean_ctor_set(v___x_1620_, 0, v___x_1600_);
v___x_1624_ = v___x_1620_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v___x_1622_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
v_a_1589_ = v___x_1624_;
goto v___jp_1588_;
}
}
}
else
{
lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
v_isSharedCheck_1634_ = !lean_is_exclusive(v_snd_1615_);
if (v_isSharedCheck_1634_ == 0)
{
lean_object* v_unused_1635_; lean_object* v_unused_1636_; 
v_unused_1635_ = lean_ctor_get(v_snd_1615_, 1);
lean_dec(v_unused_1635_);
v_unused_1636_ = lean_ctor_get(v_snd_1615_, 0);
lean_dec(v_unused_1636_);
v___x_1629_ = v_snd_1615_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_dec(v_snd_1615_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 1, v_snd_1595_);
lean_ctor_set(v___x_1629_, 0, v___x_1600_);
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1633_, 1, v_snd_1595_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
v_a_1589_ = v___x_1632_;
goto v___jp_1588_;
}
}
}
}
else
{
lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1646_; 
lean_inc_ref(v_fst_1614_);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_a_1610_);
if (v_isSharedCheck_1646_ == 0)
{
lean_object* v_unused_1647_; lean_object* v_unused_1648_; 
v_unused_1647_ = lean_ctor_get(v_a_1610_, 1);
lean_dec(v_unused_1647_);
v_unused_1648_ = lean_ctor_get(v_a_1610_, 0);
lean_dec(v_unused_1648_);
v___x_1638_ = v_a_1610_;
v_isShared_1639_ = v_isSharedCheck_1646_;
goto v_resetjp_1637_;
}
else
{
lean_dec(v_a_1610_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1646_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v___x_1641_; 
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 1, v_snd_1595_);
v___x_1641_ = v___x_1638_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_fst_1614_);
lean_ctor_set(v_reuseFailAlloc_1645_, 1, v_snd_1595_);
v___x_1641_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1643_; 
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1641_);
v___x_1643_ = v___x_1612_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
lean_dec(v_snd_1595_);
v_a_1650_ = lean_ctor_get(v___x_1609_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1609_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1609_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1609_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1656_; 
v_reuseFailAlloc_1656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1656_, 0, v_a_1650_);
v___x_1655_ = v_reuseFailAlloc_1656_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
return v___x_1655_;
}
}
}
}
}
}
v___jp_1588_:
{
size_t v___x_1590_; size_t v___x_1591_; 
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = lean_usize_add(v_i_1584_, v___x_1590_);
v_i_1584_ = v___x_1591_;
v_b_1585_ = v_a_1589_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1579_ = stack[0].m_obj;
lean_object* v___x_1580_ = stack[1].m_obj;
lean_object* v___x_1581_ = stack[2].m_obj;
lean_object* v_as_1582_ = stack[3].m_obj;
size_t v_sz_1583_ = stack[4].m_num;
size_t v_i_1584_ = stack[5].m_num;
lean_object* v_b_1585_ = stack[6].m_obj;
lean_object* v___y_1586_ = stack[7].m_obj;
lean_object* v_res_1661_;
v_res_1661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1579_, v___x_1580_, v___x_1581_, v_as_1582_, v_sz_1583_, v_i_1584_, v_b_1585_, v___y_1586_);
stack->m_obj
 = v_res_1661_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1___boxed(lean_object* v_p_1662_, lean_object* v___x_1663_, lean_object* v___x_1664_, lean_object* v_as_1665_, lean_object* v_sz_1666_, lean_object* v_i_1667_, lean_object* v_b_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_){
_start:
{
size_t v_sz_boxed_1671_; size_t v_i_boxed_1672_; lean_object* v_res_1673_; 
v_sz_boxed_1671_ = lean_unbox_usize(v_sz_1666_);
lean_dec(v_sz_1666_);
v_i_boxed_1672_ = lean_unbox_usize(v_i_1667_);
lean_dec(v_i_1667_);
v_res_1673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1662_, v___x_1663_, v___x_1664_, v_as_1665_, v_sz_boxed_1671_, v_i_boxed_1672_, v_b_1668_, v___y_1669_);
lean_dec_ref(v___y_1669_);
lean_dec_ref(v_as_1665_);
lean_dec_ref(v___x_1664_);
lean_dec_ref(v___x_1663_);
lean_dec_ref(v_p_1662_);
return v_res_1673_;
}
}
lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(lean_object* v_p_1677_, lean_object* v_oldInlayHints_1678_, lean_object* v_a_1679_){
_start:
{
lean_object* v_doc_1681_; lean_object* v_toEditableDocumentCore_1682_; lean_object* v_meta_1683_; lean_object* v_text_1684_; lean_object* v___x_1685_; size_t v_sz_1686_; size_t v___x_1687_; lean_object* v___x_1688_; 
v_doc_1681_ = lean_ctor_get(v_a_1679_, 1);
v_toEditableDocumentCore_1682_ = lean_ctor_get(v_doc_1681_, 0);
v_meta_1683_ = lean_ctor_get(v_toEditableDocumentCore_1682_, 0);
v_text_1684_ = lean_ctor_get(v_meta_1683_, 3);
v___x_1685_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0));
v_sz_1686_ = lean_array_size(v_oldInlayHints_1678_);
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1677_, v_text_1684_, v_meta_1683_, v_oldInlayHints_1678_, v_sz_1686_, v___x_1687_, v___x_1685_, v_a_1679_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1702_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1702_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1702_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1702_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1702_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v_fst_1693_; 
v_fst_1693_ = lean_ctor_get(v_a_1689_, 0);
if (lean_obj_tag(v_fst_1693_) == 0)
{
lean_object* v_snd_1694_; lean_object* v___x_1696_; 
v_snd_1694_ = lean_ctor_get(v_a_1689_, 1);
lean_inc(v_snd_1694_);
lean_dec(v_a_1689_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v_snd_1694_);
v___x_1696_ = v___x_1691_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_snd_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
else
{
lean_object* v_val_1698_; lean_object* v___x_1700_; 
lean_inc_ref(v_fst_1693_);
lean_dec(v_a_1689_);
v_val_1698_ = lean_ctor_get(v_fst_1693_, 0);
lean_inc(v_val_1698_);
lean_dec_ref_known(v_fst_1693_, 1);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v_val_1698_);
v___x_1700_ = v___x_1691_;
goto v_reusejp_1699_;
}
else
{
lean_object* v_reuseFailAlloc_1701_; 
v_reuseFailAlloc_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1701_, 0, v_val_1698_);
v___x_1700_ = v_reuseFailAlloc_1701_;
goto v_reusejp_1699_;
}
v_reusejp_1699_:
{
return v___x_1700_;
}
}
}
}
else
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1710_; 
v_a_1703_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1710_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1705_ = v___x_1688_;
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1688_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1710_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v___x_1708_; 
if (v_isShared_1706_ == 0)
{
v___x_1708_ = v___x_1705_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_a_1703_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1677_ = stack[0].m_obj;
lean_object* v_oldInlayHints_1678_ = stack[1].m_obj;
lean_object* v_a_1679_ = stack[2].m_obj;
lean_object* v_res_1711_;
v_res_1711_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1677_, v_oldInlayHints_1678_, v_a_1679_);
stack->m_obj
 = v_res_1711_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___boxed(lean_object* v_p_1712_, lean_object* v_oldInlayHints_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1712_, v_oldInlayHints_1713_, v_a_1714_);
lean_dec_ref(v_a_1714_);
lean_dec_ref(v_oldInlayHints_1713_);
lean_dec_ref(v_p_1712_);
return v_res_1716_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(lean_object* v___x_1717_, lean_object* v___x_1718_, lean_object* v_as_1719_, size_t v_sz_1720_, size_t v_i_1721_, lean_object* v_b_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1717_, v___x_1718_, v_as_1719_, v_sz_1720_, v_i_1721_, v_b_1722_);
return v___x_1725_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1717_ = stack[0].m_obj;
lean_object* v___x_1718_ = stack[1].m_obj;
lean_object* v_as_1719_ = stack[2].m_obj;
size_t v_sz_1720_ = stack[3].m_num;
size_t v_i_1721_ = stack[4].m_num;
lean_object* v_b_1722_ = stack[5].m_obj;
lean_object* v___y_1723_ = stack[6].m_obj;
lean_object* v_res_1726_;
v_res_1726_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(v___x_1717_, v___x_1718_, v_as_1719_, v_sz_1720_, v_i_1721_, v_b_1722_, v___y_1723_);
stack->m_obj
 = v_res_1726_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___boxed(lean_object* v___x_1727_, lean_object* v___x_1728_, lean_object* v_as_1729_, lean_object* v_sz_1730_, lean_object* v_i_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
size_t v_sz_boxed_1735_; size_t v_i_boxed_1736_; lean_object* v_res_1737_; 
v_sz_boxed_1735_ = lean_unbox_usize(v_sz_1730_);
lean_dec(v_sz_1730_);
v_i_boxed_1736_ = lean_unbox_usize(v_i_1731_);
lean_dec(v_i_1731_);
v_res_1737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(v___x_1727_, v___x_1728_, v_as_1729_, v_sz_boxed_1735_, v_i_boxed_1736_, v_b_1732_, v___y_1733_);
lean_dec_ref(v___y_1733_);
lean_dec_ref(v_as_1729_);
lean_dec_ref(v___x_1728_);
lean_dec_ref(v___x_1727_);
return v_res_1737_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(lean_object* v_a_1738_, lean_object* v_as_1739_, size_t v_i_1740_, size_t v_stop_1741_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_usize_dec_eq(v_i_1740_, v_stop_1741_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = lean_array_uget_borrowed(v_as_1739_, v_i_1740_);
v___x_1744_ = l_Lean_Elab_instBEqInlayHintTextEdit_beq(v_a_1738_, v___x_1743_);
if (v___x_1744_ == 0)
{
size_t v___x_1745_; size_t v___x_1746_; 
v___x_1745_ = ((size_t)1ULL);
v___x_1746_ = lean_usize_add(v_i_1740_, v___x_1745_);
v_i_1740_ = v___x_1746_;
goto _start;
}
else
{
return v___x_1744_;
}
}
else
{
uint8_t v___x_1748_; 
v___x_1748_ = 0;
return v___x_1748_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1738_ = stack[0].m_obj;
lean_object* v_as_1739_ = stack[1].m_obj;
size_t v_i_1740_ = stack[2].m_num;
size_t v_stop_1741_ = stack[3].m_num;
uint8_t v_res_1749_;
v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1738_, v_as_1739_, v_i_1740_, v_stop_1741_);
stack->m_num = v_res_1749_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0___boxed(lean_object* v_a_1750_, lean_object* v_as_1751_, lean_object* v_i_1752_, lean_object* v_stop_1753_){
_start:
{
size_t v_i_boxed_1754_; size_t v_stop_boxed_1755_; uint8_t v_res_1756_; lean_object* v_r_1757_; 
v_i_boxed_1754_ = lean_unbox_usize(v_i_1752_);
lean_dec(v_i_1752_);
v_stop_boxed_1755_ = lean_unbox_usize(v_stop_1753_);
lean_dec(v_stop_1753_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1750_, v_as_1751_, v_i_boxed_1754_, v_stop_boxed_1755_);
lean_dec_ref(v_as_1751_);
lean_dec_ref(v_a_1750_);
v_r_1757_ = lean_box(v_res_1756_);
return v_r_1757_;
}
}
uint8_t l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(lean_object* v_as_1758_, lean_object* v_a_1759_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1760_ = lean_unsigned_to_nat(0u);
v___x_1761_ = lean_array_get_size(v_as_1758_);
v___x_1762_ = lean_nat_dec_lt(v___x_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
return v___x_1762_;
}
else
{
if (v___x_1762_ == 0)
{
return v___x_1762_;
}
else
{
size_t v___x_1763_; size_t v___x_1764_; uint8_t v___x_1765_; 
v___x_1763_ = ((size_t)0ULL);
v___x_1764_ = lean_usize_of_nat(v___x_1761_);
v___x_1765_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1759_, v_as_1758_, v___x_1763_, v___x_1764_);
return v___x_1765_;
}
}
}
}
LEAN_EXPORT void l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1758_ = stack[0].m_obj;
lean_object* v_a_1759_ = stack[1].m_obj;
uint8_t v_res_1766_;
v_res_1766_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_as_1758_, v_a_1759_);
stack->m_num = v_res_1766_;
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0___boxed(lean_object* v_as_1767_, lean_object* v_a_1768_){
_start:
{
uint8_t v_res_1769_; lean_object* v_r_1770_; 
v_res_1769_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_as_1767_, v_a_1768_);
lean_dec_ref(v_a_1768_);
lean_dec_ref(v_as_1767_);
v_r_1770_ = lean_box(v_res_1769_);
return v_r_1770_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(lean_object* v___x_1771_, lean_object* v_as_1772_, size_t v_i_1773_, size_t v_stop_1774_){
_start:
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_usize_dec_eq(v_i_1773_, v_stop_1774_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; lean_object* v_textEdits_1777_; uint8_t v___x_1778_; 
v___x_1776_ = lean_array_uget_borrowed(v_as_1772_, v_i_1773_);
v_textEdits_1777_ = lean_ctor_get(v___x_1776_, 3);
v___x_1778_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_textEdits_1777_, v___x_1771_);
if (v___x_1778_ == 0)
{
size_t v___x_1779_; size_t v___x_1780_; 
v___x_1779_ = ((size_t)1ULL);
v___x_1780_ = lean_usize_add(v_i_1773_, v___x_1779_);
v_i_1773_ = v___x_1780_;
goto _start;
}
else
{
return v___x_1778_;
}
}
else
{
uint8_t v___x_1782_; 
v___x_1782_ = 0;
return v___x_1782_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1771_ = stack[0].m_obj;
lean_object* v_as_1772_ = stack[1].m_obj;
size_t v_i_1773_ = stack[2].m_num;
size_t v_stop_1774_ = stack[3].m_num;
uint8_t v_res_1783_;
v_res_1783_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1771_, v_as_1772_, v_i_1773_, v_stop_1774_);
stack->m_num = v_res_1783_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1___boxed(lean_object* v___x_1784_, lean_object* v_as_1785_, lean_object* v_i_1786_, lean_object* v_stop_1787_){
_start:
{
size_t v_i_boxed_1788_; size_t v_stop_boxed_1789_; uint8_t v_res_1790_; lean_object* v_r_1791_; 
v_i_boxed_1788_ = lean_unbox_usize(v_i_1786_);
lean_dec(v_i_1786_);
v_stop_boxed_1789_ = lean_unbox_usize(v_stop_1787_);
lean_dec(v_stop_1787_);
v_res_1790_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1784_, v_as_1785_, v_i_boxed_1788_, v_stop_boxed_1789_);
lean_dec_ref(v_as_1785_);
lean_dec_ref(v___x_1784_);
v_r_1791_ = lean_box(v_res_1790_);
return v_r_1791_;
}
}
uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(lean_object* v_oldInlayHints_1792_, lean_object* v___x_1793_, lean_object* v___x_1794_, lean_object* v_as_1795_, size_t v_i_1796_, size_t v_stop_1797_){
_start:
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_usize_dec_eq(v_i_1796_, v_stop_1797_);
if (v___x_1802_ == 0)
{
lean_object* v___x_1803_; uint8_t v___x_1804_; uint8_t v___x_1805_; lean_object* v___x_1807_; 
v___x_1803_ = lean_unsigned_to_nat(0u);
v___x_1804_ = lean_nat_dec_lt(v___x_1803_, v___x_1793_);
v___x_1805_ = 1;
v___x_1807_ = lean_array_uget(v_as_1795_, v_i_1796_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_range_1808_; lean_object* v_text_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1822_; 
v_range_1808_ = lean_ctor_get(v___x_1807_, 0);
v_text_1809_ = lean_ctor_get(v___x_1807_, 1);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1811_ = v___x_1807_;
v_isShared_1812_ = v_isSharedCheck_1822_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_text_1809_);
lean_inc(v_range_1808_);
lean_dec(v___x_1807_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1822_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; uint8_t v___x_1814_; 
v___x_1813_ = lean_array_get_size(v_oldInlayHints_1792_);
v___x_1814_ = lean_nat_dec_lt(v___x_1803_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_del_object(v___x_1811_);
lean_dec_ref(v_text_1809_);
lean_dec_ref(v_range_1808_);
goto v___jp_1806_;
}
else
{
if (v___x_1814_ == 0)
{
lean_del_object(v___x_1811_);
lean_dec_ref(v_text_1809_);
lean_dec_ref(v_range_1808_);
return v___x_1805_;
}
else
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1794_, v_range_1808_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1815_);
v___x_1817_ = v___x_1811_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1815_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_text_1809_);
v___x_1817_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
size_t v___x_1818_; size_t v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = ((size_t)0ULL);
v___x_1819_ = lean_usize_of_nat(v___x_1813_);
v___x_1820_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1817_, v_oldInlayHints_1792_, v___x_1818_, v___x_1819_);
lean_dec_ref(v___x_1817_);
if (v___x_1820_ == 0)
{
return v___x_1805_;
}
else
{
goto v___jp_1798_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1807_);
goto v___jp_1806_;
}
v___jp_1806_:
{
if (v___x_1804_ == 0)
{
goto v___jp_1798_;
}
else
{
return v___x_1805_;
}
}
}
else
{
uint8_t v___x_1823_; 
v___x_1823_ = 0;
return v___x_1823_;
}
v___jp_1798_:
{
size_t v___x_1799_; size_t v___x_1800_; 
v___x_1799_ = ((size_t)1ULL);
v___x_1800_ = lean_usize_add(v_i_1796_, v___x_1799_);
v_i_1796_ = v___x_1800_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldInlayHints_1792_ = stack[0].m_obj;
lean_object* v___x_1793_ = stack[1].m_obj;
lean_object* v___x_1794_ = stack[2].m_obj;
lean_object* v_as_1795_ = stack[3].m_obj;
size_t v_i_1796_ = stack[4].m_num;
size_t v_stop_1797_ = stack[5].m_num;
uint8_t v_res_1824_;
v_res_1824_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1792_, v___x_1793_, v___x_1794_, v_as_1795_, v_i_1796_, v_stop_1797_);
stack->m_num = v_res_1824_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2___boxed(lean_object* v_oldInlayHints_1825_, lean_object* v___x_1826_, lean_object* v___x_1827_, lean_object* v_as_1828_, lean_object* v_i_1829_, lean_object* v_stop_1830_){
_start:
{
size_t v_i_boxed_1831_; size_t v_stop_boxed_1832_; uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_i_boxed_1831_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_stop_boxed_1832_ = lean_unbox_usize(v_stop_1830_);
lean_dec(v_stop_1830_);
v_res_1833_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1825_, v___x_1826_, v___x_1827_, v_as_1828_, v_i_boxed_1831_, v_stop_boxed_1832_);
lean_dec_ref(v_as_1828_);
lean_dec_ref(v___x_1827_);
lean_dec(v___x_1826_);
lean_dec_ref(v_oldInlayHints_1825_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(lean_object* v_p_1835_, lean_object* v_oldInlayHints_1836_, lean_object* v_a_1837_){
_start:
{
uint8_t v___y_1840_; lean_object* v_contentChanges_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_contentChanges_1846_ = lean_ctor_get(v_p_1835_, 1);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_array_get_size(v_contentChanges_1846_);
v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
uint8_t v___x_1850_; 
v___x_1850_ = 1;
v___y_1840_ = v___x_1850_;
goto v___jp_1839_;
}
else
{
if (v___x_1849_ == 0)
{
v___y_1840_ = v___x_1849_;
goto v___jp_1839_;
}
else
{
lean_object* v_doc_1851_; lean_object* v_toEditableDocumentCore_1852_; lean_object* v_meta_1853_; lean_object* v_text_1854_; size_t v___x_1855_; size_t v___x_1856_; uint8_t v___x_1857_; 
v_doc_1851_ = lean_ctor_get(v_a_1837_, 1);
v_toEditableDocumentCore_1852_ = lean_ctor_get(v_doc_1851_, 0);
v_meta_1853_ = lean_ctor_get(v_toEditableDocumentCore_1852_, 0);
v_text_1854_ = lean_ctor_get(v_meta_1853_, 3);
v___x_1855_ = ((size_t)0ULL);
v___x_1856_ = lean_usize_of_nat(v___x_1848_);
v___x_1857_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1836_, v___x_1848_, v_text_1854_, v_contentChanges_1846_, v___x_1855_, v___x_1856_);
if (v___x_1857_ == 0)
{
v___y_1840_ = v___x_1849_;
goto v___jp_1839_;
}
else
{
uint8_t v___x_1858_; 
v___x_1858_ = 0;
v___y_1840_ = v___x_1858_;
goto v___jp_1839_;
}
}
}
v___jp_1839_:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_io_mono_ms_now();
if (v___y_1840_ == 0)
{
lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
lean_dec(v___x_1841_);
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1835_ = stack[0].m_obj;
lean_object* v_oldInlayHints_1836_ = stack[1].m_obj;
lean_object* v_a_1837_ = stack[2].m_obj;
lean_object* v_res_1859_;
v_res_1859_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1835_, v_oldInlayHints_1836_, v_a_1837_);
stack->m_obj
 = v_res_1859_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___boxed(lean_object* v_p_1860_, lean_object* v_oldInlayHints_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1860_, v_oldInlayHints_1861_, v_a_1862_);
lean_dec_ref(v_a_1862_);
lean_dec_ref(v_oldInlayHints_1861_);
lean_dec_ref(v_p_1860_);
return v_res_1864_;
}
}
lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange(lean_object* v_p_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_oldInlayHints_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1899_; 
v_oldInlayHints_1869_ = lean_ctor_get(v_a_1866_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_a_1866_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; lean_object* v_unused_1901_; 
v_unused_1900_ = lean_ctor_get(v_a_1866_, 2);
lean_dec(v_unused_1900_);
v_unused_1901_ = lean_ctor_get(v_a_1866_, 1);
lean_dec(v_unused_1901_);
v___x_1871_ = v_a_1866_;
v_isShared_1872_ = v_isSharedCheck_1899_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_oldInlayHints_1869_);
lean_dec(v_a_1866_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1899_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1873_; 
v___x_1873_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1865_, v_oldInlayHints_1869_, v_a_1867_);
if (lean_obj_tag(v___x_1873_) == 0)
{
lean_object* v_a_1874_; lean_object* v___x_1875_; lean_object* v_a_1876_; lean_object* v___x_1878_; uint8_t v_isShared_1879_; uint8_t v_isSharedCheck_1890_; 
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref_known(v___x_1873_, 1);
v___x_1875_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1865_, v_oldInlayHints_1869_, v_a_1867_);
lean_dec_ref(v_oldInlayHints_1869_);
v_a_1876_ = lean_ctor_get(v___x_1875_, 0);
v_isSharedCheck_1890_ = !lean_is_exclusive(v___x_1875_);
if (v_isSharedCheck_1890_ == 0)
{
v___x_1878_ = v___x_1875_;
v_isShared_1879_ = v_isSharedCheck_1890_;
goto v_resetjp_1877_;
}
else
{
lean_inc(v_a_1876_);
lean_dec(v___x_1875_);
v___x_1878_ = lean_box(0);
v_isShared_1879_ = v_isSharedCheck_1890_;
goto v_resetjp_1877_;
}
v_resetjp_1877_:
{
lean_object* v___x_1880_; uint8_t v___x_1881_; lean_object* v___x_1883_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = 1;
if (v_isShared_1872_ == 0)
{
lean_ctor_set(v___x_1871_, 2, v_a_1876_);
lean_ctor_set(v___x_1871_, 1, v___x_1880_);
lean_ctor_set(v___x_1871_, 0, v_a_1874_);
v___x_1883_ = v___x_1871_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1874_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v___x_1880_);
lean_ctor_set(v_reuseFailAlloc_1889_, 2, v_a_1876_);
v___x_1883_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
lean_ctor_set_uint8(v___x_1883_, sizeof(void*)*3, v___x_1881_);
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v___x_1883_);
if (v_isShared_1879_ == 0)
{
lean_ctor_set(v___x_1878_, 0, v___x_1885_);
v___x_1887_ = v___x_1878_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
lean_del_object(v___x_1871_);
lean_dec_ref(v_oldInlayHints_1869_);
v_a_1891_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1873_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1873_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_handleInlayHintsDidChange_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_1865_ = stack[0].m_obj;
lean_object* v_a_1866_ = stack[1].m_obj;
lean_object* v_a_1867_ = stack[2].m_obj;
lean_object* v_res_1902_;
v_res_1902_ = l_Lean_Server_FileWorker_handleInlayHintsDidChange(v_p_1865_, v_a_1866_, v_a_1867_);
stack->m_obj
 = v_res_1902_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed(lean_object* v_p_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Lean_Server_FileWorker_handleInlayHintsDidChange(v_p_1903_, v_a_1904_, v_a_1905_);
lean_dec_ref(v_a_1905_);
lean_dec_ref(v_p_1903_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(lean_object* v___x_1908_, lean_object* v_x_1909_){
_start:
{
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed(lean_object* v___x_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v_res_1912_; 
v_res_1912_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(v___x_1910_, v_x_1911_);
lean_dec_ref(v_x_1911_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1913_, lean_object* v_x_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_){
_start:
{
lean_object* v_ks_1917_; lean_object* v_vs_1918_; lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1942_; 
v_ks_1917_ = lean_ctor_get(v_x_1913_, 0);
v_vs_1918_ = lean_ctor_get(v_x_1913_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_x_1913_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1920_ = v_x_1913_;
v_isShared_1921_ = v_isSharedCheck_1942_;
goto v_resetjp_1919_;
}
else
{
lean_inc(v_vs_1918_);
lean_inc(v_ks_1917_);
lean_dec(v_x_1913_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1942_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1922_; uint8_t v___x_1923_; 
v___x_1922_ = lean_array_get_size(v_ks_1917_);
v___x_1923_ = lean_nat_dec_lt(v_x_1914_, v___x_1922_);
if (v___x_1923_ == 0)
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
lean_dec(v_x_1914_);
v___x_1924_ = lean_array_push(v_ks_1917_, v_x_1915_);
v___x_1925_ = lean_array_push(v_vs_1918_, v_x_1916_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v___x_1925_);
lean_ctor_set(v___x_1920_, 0, v___x_1924_);
v___x_1927_ = v___x_1920_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1924_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
else
{
lean_object* v_k_x27_1929_; uint8_t v___x_1930_; 
v_k_x27_1929_ = lean_array_fget_borrowed(v_ks_1917_, v_x_1914_);
v___x_1930_ = lean_string_dec_eq(v_x_1915_, v_k_x27_1929_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1932_; 
if (v_isShared_1921_ == 0)
{
v___x_1932_ = v___x_1920_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_ks_1917_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_vs_1918_);
v___x_1932_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_unsigned_to_nat(1u);
v___x_1934_ = lean_nat_add(v_x_1914_, v___x_1933_);
lean_dec(v_x_1914_);
v_x_1913_ = v___x_1932_;
v_x_1914_ = v___x_1934_;
goto _start;
}
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1937_ = lean_array_fset(v_ks_1917_, v_x_1914_, v_x_1915_);
v___x_1938_ = lean_array_fset(v_vs_1918_, v_x_1914_, v_x_1916_);
lean_dec(v_x_1914_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 1, v___x_1938_);
lean_ctor_set(v___x_1920_, 0, v___x_1937_);
v___x_1940_ = v___x_1920_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1937_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(lean_object* v_n_1943_, lean_object* v_k_1944_, lean_object* v_v_1945_){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_unsigned_to_nat(0u);
v___x_1947_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_n_1943_, v___x_1946_, v_k_1944_, v_v_1945_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1948_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(lean_object* v_x_1949_, size_t v_x_1950_, size_t v_x_1951_, lean_object* v_x_1952_, lean_object* v_x_1953_){
_start:
{
if (lean_obj_tag(v_x_1949_) == 0)
{
lean_object* v_es_1954_; size_t v___x_1955_; size_t v___x_1956_; lean_object* v_j_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_es_1954_ = lean_ctor_get(v_x_1949_, 0);
v___x_1955_ = ((size_t)31ULL);
v___x_1956_ = lean_usize_land(v_x_1950_, v___x_1955_);
v_j_1957_ = lean_usize_to_nat(v___x_1956_);
v___x_1958_ = lean_array_get_size(v_es_1954_);
v___x_1959_ = lean_nat_dec_lt(v_j_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_dec(v_j_1957_);
lean_dec(v_x_1953_);
lean_dec_ref(v_x_1952_);
return v_x_1949_;
}
else
{
lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1998_; 
lean_inc_ref(v_es_1954_);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_x_1949_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v_x_1949_, 0);
lean_dec(v_unused_1999_);
v___x_1961_ = v_x_1949_;
v_isShared_1962_ = v_isSharedCheck_1998_;
goto v_resetjp_1960_;
}
else
{
lean_dec(v_x_1949_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1998_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v_v_1963_; lean_object* v___x_1964_; lean_object* v_xs_x27_1965_; lean_object* v___y_1967_; 
v_v_1963_ = lean_array_fget(v_es_1954_, v_j_1957_);
v___x_1964_ = lean_box(0);
v_xs_x27_1965_ = lean_array_fset(v_es_1954_, v_j_1957_, v___x_1964_);
switch(lean_obj_tag(v_v_1963_))
{
case 0:
{
lean_object* v_key_1972_; lean_object* v_val_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1983_; 
v_key_1972_ = lean_ctor_get(v_v_1963_, 0);
v_val_1973_ = lean_ctor_get(v_v_1963_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_v_1963_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1975_ = v_v_1963_;
v_isShared_1976_ = v_isSharedCheck_1983_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_val_1973_);
lean_inc(v_key_1972_);
lean_dec(v_v_1963_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1983_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
uint8_t v___x_1977_; 
v___x_1977_ = lean_string_dec_eq(v_x_1952_, v_key_1972_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_del_object(v___x_1975_);
v___x_1978_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1972_, v_val_1973_, v_x_1952_, v_x_1953_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
v___y_1967_ = v___x_1979_;
goto v___jp_1966_;
}
else
{
lean_object* v___x_1981_; 
lean_dec(v_val_1973_);
lean_dec(v_key_1972_);
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 1, v_x_1953_);
lean_ctor_set(v___x_1975_, 0, v_x_1952_);
v___x_1981_ = v___x_1975_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_x_1952_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_x_1953_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
v___y_1967_ = v___x_1981_;
goto v___jp_1966_;
}
}
}
}
case 1:
{
lean_object* v_node_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1996_; 
v_node_1984_ = lean_ctor_get(v_v_1963_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v_v_1963_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1986_ = v_v_1963_;
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_node_1984_);
lean_dec(v_v_1963_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
size_t v___x_1988_; size_t v___x_1989_; size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1994_; 
v___x_1988_ = ((size_t)5ULL);
v___x_1989_ = lean_usize_shift_right(v_x_1950_, v___x_1988_);
v___x_1990_ = ((size_t)1ULL);
v___x_1991_ = lean_usize_add(v_x_1951_, v___x_1990_);
v___x_1992_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_node_1984_, v___x_1989_, v___x_1991_, v_x_1952_, v_x_1953_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1992_);
v___x_1994_ = v___x_1986_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v___x_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
v___y_1967_ = v___x_1994_;
goto v___jp_1966_;
}
}
}
default: 
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v_x_1952_);
lean_ctor_set(v___x_1997_, 1, v_x_1953_);
v___y_1967_ = v___x_1997_;
goto v___jp_1966_;
}
}
v___jp_1966_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = lean_array_fset(v_xs_x27_1965_, v_j_1957_, v___y_1967_);
lean_dec(v_j_1957_);
if (v_isShared_1962_ == 0)
{
lean_ctor_set(v___x_1961_, 0, v___x_1968_);
v___x_1970_ = v___x_1961_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
}
else
{
lean_object* v_ks_2000_; lean_object* v_vs_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2019_; 
v_ks_2000_ = lean_ctor_get(v_x_1949_, 0);
v_vs_2001_ = lean_ctor_get(v_x_1949_, 1);
v_isSharedCheck_2019_ = !lean_is_exclusive(v_x_1949_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2003_ = v_x_1949_;
v_isShared_2004_ = v_isSharedCheck_2019_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_vs_2001_);
lean_inc(v_ks_2000_);
lean_dec(v_x_1949_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2019_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v___x_2006_; 
if (v_isShared_2004_ == 0)
{
v___x_2006_ = v___x_2003_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_ks_2000_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_vs_2001_);
v___x_2006_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v_newNode_2007_; size_t v___x_2008_; uint8_t v___x_2009_; 
v_newNode_2007_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v___x_2006_, v_x_1952_, v_x_1953_);
v___x_2008_ = ((size_t)7ULL);
v___x_2009_ = lean_usize_dec_le(v___x_2008_, v_x_1951_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v___x_2010_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2007_);
v___x_2011_ = lean_unsigned_to_nat(4u);
v___x_2012_ = lean_nat_dec_lt(v___x_2010_, v___x_2011_);
lean_dec(v___x_2010_);
if (v___x_2012_ == 0)
{
lean_object* v_ks_2013_; lean_object* v_vs_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_ks_2013_ = lean_ctor_get(v_newNode_2007_, 0);
lean_inc_ref(v_ks_2013_);
v_vs_2014_ = lean_ctor_get(v_newNode_2007_, 1);
lean_inc_ref(v_vs_2014_);
lean_dec_ref(v_newNode_2007_);
v___x_2015_ = lean_unsigned_to_nat(0u);
v___x_2016_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0);
v___x_2017_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_x_1951_, v_ks_2013_, v_vs_2014_, v___x_2015_, v___x_2016_);
lean_dec_ref(v_vs_2014_);
lean_dec_ref(v_ks_2013_);
return v___x_2017_;
}
else
{
return v_newNode_2007_;
}
}
else
{
return v_newNode_2007_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1949_ = stack[0].m_obj;
size_t v_x_1950_ = stack[1].m_num;
size_t v_x_1951_ = stack[2].m_num;
lean_object* v_x_1952_ = stack[3].m_obj;
lean_object* v_x_1953_ = stack[4].m_obj;
lean_object* v_res_2020_;
v_res_2020_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_1949_, v_x_1950_, v_x_1951_, v_x_1952_, v_x_1953_);
stack->m_obj
 = v_res_2020_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(size_t v_depth_2021_, lean_object* v_keys_2022_, lean_object* v_vals_2023_, lean_object* v_i_2024_, lean_object* v_entries_2025_){
_start:
{
lean_object* v___x_2026_; uint8_t v___x_2027_; 
v___x_2026_ = lean_array_get_size(v_keys_2022_);
v___x_2027_ = lean_nat_dec_lt(v_i_2024_, v___x_2026_);
if (v___x_2027_ == 0)
{
lean_dec(v_i_2024_);
return v_entries_2025_;
}
else
{
lean_object* v_k_2028_; lean_object* v_v_2029_; uint64_t v___x_2030_; size_t v_h_2031_; size_t v___x_2032_; lean_object* v___x_2033_; size_t v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; size_t v_h_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v_k_2028_ = lean_array_fget_borrowed(v_keys_2022_, v_i_2024_);
v_v_2029_ = lean_array_fget_borrowed(v_vals_2023_, v_i_2024_);
v___x_2030_ = lean_string_hash(v_k_2028_);
v_h_2031_ = lean_uint64_to_usize(v___x_2030_);
v___x_2032_ = ((size_t)5ULL);
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = ((size_t)1ULL);
v___x_2035_ = lean_usize_sub(v_depth_2021_, v___x_2034_);
v___x_2036_ = lean_usize_mul(v___x_2032_, v___x_2035_);
v_h_2037_ = lean_usize_shift_right(v_h_2031_, v___x_2036_);
v___x_2038_ = lean_nat_add(v_i_2024_, v___x_2033_);
lean_dec(v_i_2024_);
lean_inc(v_v_2029_);
lean_inc(v_k_2028_);
v___x_2039_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_entries_2025_, v_h_2037_, v_depth_2021_, v_k_2028_, v_v_2029_);
v_i_2024_ = v___x_2038_;
v_entries_2025_ = v___x_2039_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2021_ = stack[0].m_num;
lean_object* v_keys_2022_ = stack[1].m_obj;
lean_object* v_vals_2023_ = stack[2].m_obj;
lean_object* v_i_2024_ = stack[3].m_obj;
lean_object* v_entries_2025_ = stack[4].m_obj;
lean_object* v_res_2041_;
v_res_2041_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_2021_, v_keys_2022_, v_vals_2023_, v_i_2024_, v_entries_2025_);
stack->m_obj
 = v_res_2041_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_depth_2042_, lean_object* v_keys_2043_, lean_object* v_vals_2044_, lean_object* v_i_2045_, lean_object* v_entries_2046_){
_start:
{
size_t v_depth_boxed_2047_; lean_object* v_res_2048_; 
v_depth_boxed_2047_ = lean_unbox_usize(v_depth_2042_);
lean_dec(v_depth_2042_);
v_res_2048_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_boxed_2047_, v_keys_2043_, v_vals_2044_, v_i_2045_, v_entries_2046_);
lean_dec_ref(v_vals_2044_);
lean_dec_ref(v_keys_2043_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_, lean_object* v_x_2053_){
_start:
{
size_t v_x_2419__boxed_2054_; size_t v_x_2420__boxed_2055_; lean_object* v_res_2056_; 
v_x_2419__boxed_2054_ = lean_unbox_usize(v_x_2050_);
lean_dec(v_x_2050_);
v_x_2420__boxed_2055_ = lean_unbox_usize(v_x_2051_);
lean_dec(v_x_2051_);
v_res_2056_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_2049_, v_x_2419__boxed_2054_, v_x_2420__boxed_2055_, v_x_2052_, v_x_2053_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(lean_object* v_x_2057_, lean_object* v_x_2058_, lean_object* v_x_2059_){
_start:
{
uint64_t v___x_2060_; size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v___x_2060_ = lean_string_hash(v_x_2058_);
v___x_2061_ = lean_uint64_to_usize(v___x_2060_);
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_2057_, v___x_2061_, v___x_2062_, v_x_2058_, v_x_2059_);
return v___x_2063_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(lean_object* v_mutex_2064_, lean_object* v_a_x3f_2065_){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2067_ = lean_io_basemutex_unlock(v_mutex_2064_);
v___x_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2068_, 0, v___x_2067_);
return v___x_2068_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_2064_ = stack[0].m_obj;
lean_object* v_a_x3f_2065_ = stack[1].m_obj;
lean_object* v_res_2069_;
v_res_2069_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2064_, v_a_x3f_2065_);
stack->m_obj
 = v_res_2069_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0___boxed(lean_object* v_mutex_2070_, lean_object* v_a_x3f_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2070_, v_a_x3f_2071_);
lean_dec(v_a_x3f_2071_);
lean_dec(v_mutex_2070_);
return v_res_2073_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_mutex_2074_, lean_object* v_k_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v_ref_2078_; lean_object* v_mutex_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v_ref_2078_ = lean_ctor_get(v_mutex_2074_, 0);
lean_inc(v_ref_2078_);
v_mutex_2079_ = lean_ctor_get(v_mutex_2074_, 1);
lean_inc(v_mutex_2079_);
lean_dec_ref(v_mutex_2074_);
v___x_2080_ = lean_io_basemutex_lock(v_mutex_2079_);
lean_inc_ref(v___y_2076_);
v___x_2081_ = lean_apply_3(v_k_2075_, v_ref_2078_, v___y_2076_, lean_box(0));
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2098_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2084_ = v___x_2081_;
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_a_2082_);
lean_dec(v___x_2081_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2098_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___x_2087_; 
lean_inc(v_a_2082_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set_tag(v___x_2084_, 1);
v___x_2087_ = v___x_2084_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2082_);
v___x_2087_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
lean_object* v___x_2088_; lean_object* v___x_2090_; uint8_t v_isShared_2091_; uint8_t v_isSharedCheck_2095_; 
v___x_2088_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2079_, v___x_2087_);
lean_dec_ref(v___x_2087_);
lean_dec(v_mutex_2079_);
v_isSharedCheck_2095_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v___x_2088_, 0);
lean_dec(v_unused_2096_);
v___x_2090_ = v___x_2088_;
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
else
{
lean_dec(v___x_2088_);
v___x_2090_ = lean_box(0);
v_isShared_2091_ = v_isSharedCheck_2095_;
goto v_resetjp_2089_;
}
v_resetjp_2089_:
{
lean_object* v___x_2093_; 
if (v_isShared_2091_ == 0)
{
lean_ctor_set(v___x_2090_, 0, v_a_2082_);
v___x_2093_ = v___x_2090_;
goto v_reusejp_2092_;
}
else
{
lean_object* v_reuseFailAlloc_2094_; 
v_reuseFailAlloc_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2094_, 0, v_a_2082_);
v___x_2093_ = v_reuseFailAlloc_2094_;
goto v_reusejp_2092_;
}
v_reusejp_2092_:
{
return v___x_2093_;
}
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
v_a_2099_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2099_);
lean_dec_ref_known(v___x_2081_, 1);
v___x_2100_ = lean_box(0);
v___x_2101_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2079_, v___x_2100_);
lean_dec(v_mutex_2079_);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2101_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; 
v_unused_2109_ = lean_ctor_get(v___x_2101_, 0);
lean_dec(v_unused_2109_);
v___x_2103_ = v___x_2101_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_dec(v___x_2101_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
lean_ctor_set_tag(v___x_2103_, 1);
lean_ctor_set(v___x_2103_, 0, v_a_2099_);
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2099_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_2074_ = stack[0].m_obj;
lean_object* v_k_2075_ = stack[1].m_obj;
lean_object* v___y_2076_ = stack[2].m_obj;
lean_object* v_res_2110_;
v_res_2110_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2074_, v_k_2075_, v___y_2076_);
stack->m_obj
 = v_res_2110_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_mutex_2111_, lean_object* v_k_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2111_, v_k_2112_, v___y_2113_);
lean_dec_ref(v___y_2113_);
return v_res_2115_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(lean_object* v_val_2116_, lean_object* v___f_2117_, lean_object* v_param_2118_, lean_object* v___x_2119_, lean_object* v_x_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = lean_st_ref_get(v_val_2116_);
lean_inc_ref(v___y_2121_);
v___x_2124_ = lean_apply_4(v___f_2117_, v_param_2118_, v___x_2123_, v___y_2121_, lean_box(0));
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2134_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2134_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2134_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v_snd_2129_; lean_object* v___x_2130_; lean_object* v___x_2132_; 
v_snd_2129_ = lean_ctor_get(v_a_2125_, 1);
lean_inc(v_snd_2129_);
lean_dec(v_a_2125_);
v___x_2130_ = lean_st_ref_swap(v_val_2116_, v_snd_2129_);
lean_dec(v___x_2130_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2119_);
v___x_2132_ = v___x_2127_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v___x_2119_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
v_a_2135_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2124_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2124_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2116_ = stack[0].m_obj;
lean_object* v___f_2117_ = stack[1].m_obj;
lean_object* v_param_2118_ = stack[2].m_obj;
lean_object* v___x_2119_ = stack[3].m_obj;
lean_object* v_x_2120_ = stack[4].m_obj;
lean_object* v___y_2121_ = stack[5].m_obj;
lean_object* v_res_2143_;
v_res_2143_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(v_val_2116_, v___f_2117_, v_param_2118_, v___x_2119_, v_x_2120_, v___y_2121_);
stack->m_obj
 = v_res_2143_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed(lean_object* v_val_2144_, lean_object* v___f_2145_, lean_object* v_param_2146_, lean_object* v___x_2147_, lean_object* v_x_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(v_val_2144_, v___f_2145_, v_param_2146_, v___x_2147_, v_x_2148_, v___y_2149_);
lean_dec_ref(v___y_2149_);
lean_dec(v_val_2144_);
return v_res_2151_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(lean_object* v___f_2152_, lean_object* v___f_2153_, lean_object* v___x_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2158_ = lean_st_ref_get(v___y_2155_);
v___x_2159_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_2158_, v___f_2152_, v___y_2156_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2169_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2169_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2169_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2164_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2153_, v_a_2160_);
v___x_2165_ = lean_st_ref_swap(v___y_2155_, v___x_2164_);
lean_dec(v___x_2165_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2154_);
v___x_2167_ = v___x_2162_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2154_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
lean_dec_ref(v___f_2153_);
v_a_2170_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2159_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2159_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2152_ = stack[0].m_obj;
lean_object* v___f_2153_ = stack[1].m_obj;
lean_object* v___x_2154_ = stack[2].m_obj;
lean_object* v___y_2155_ = stack[3].m_obj;
lean_object* v___y_2156_ = stack[4].m_obj;
lean_object* v_res_2178_;
v_res_2178_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(v___f_2152_, v___f_2153_, v___x_2154_, v___y_2155_, v___y_2156_);
stack->m_obj
 = v_res_2178_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed(lean_object* v___f_2179_, lean_object* v___f_2180_, lean_object* v___x_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v_res_2185_; 
v_res_2185_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(v___f_2179_, v___f_2180_, v___x_2181_, v___y_2182_, v___y_2183_);
lean_dec_ref(v___y_2183_);
lean_dec(v___y_2182_);
return v_res_2185_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(lean_object* v_val_2186_, lean_object* v___f_2187_, lean_object* v___x_2188_, lean_object* v___f_2189_, lean_object* v_val_2190_, lean_object* v_param_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___f_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; 
v___f_2194_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_2194_, 0, v_val_2186_);
lean_closure_set(v___f_2194_, 1, v___f_2187_);
lean_closure_set(v___f_2194_, 2, v_param_2191_);
lean_closure_set(v___f_2194_, 3, v___x_2188_);
v___f_2195_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_2195_, 0, v___f_2194_);
lean_closure_set(v___f_2195_, 1, v___f_2189_);
lean_closure_set(v___f_2195_, 2, v___x_2188_);
v___x_2196_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_2190_, v___f_2195_, v___y_2192_);
return v___x_2196_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2186_ = stack[0].m_obj;
lean_object* v___f_2187_ = stack[1].m_obj;
lean_object* v___x_2188_ = stack[2].m_obj;
lean_object* v___f_2189_ = stack[3].m_obj;
lean_object* v_val_2190_ = stack[4].m_obj;
lean_object* v_param_2191_ = stack[5].m_obj;
lean_object* v___y_2192_ = stack[6].m_obj;
lean_object* v_res_2197_;
v_res_2197_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(v_val_2186_, v___f_2187_, v___x_2188_, v___f_2189_, v_val_2190_, v_param_2191_, v___y_2192_);
stack->m_obj
 = v_res_2197_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed(lean_object* v_val_2198_, lean_object* v___f_2199_, lean_object* v___x_2200_, lean_object* v___f_2201_, lean_object* v_val_2202_, lean_object* v_param_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_res_2206_; 
v_res_2206_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(v_val_2198_, v___f_2199_, v___x_2200_, v___f_2201_, v_val_2202_, v_param_2203_, v___y_2204_);
lean_dec_ref(v___y_2204_);
return v_res_2206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(lean_object* v___x_2207_, lean_object* v_x_2208_){
_start:
{
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed(lean_object* v___x_2209_, lean_object* v_x_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(v___x_2209_, v_x_2210_);
lean_dec_ref(v_x_2210_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(lean_object* v_params_2214_){
_start:
{
lean_object* v___x_2215_; 
lean_inc(v_params_2214_);
v___x_2215_ = l_Lean_Lsp_instFromJsonInlayHintParams_fromJson(v_params_2214_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2231_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2218_ = v___x_2215_;
v_isShared_2219_ = v_isSharedCheck_2231_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2215_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2231_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2220_ = 3;
v___x_2221_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2222_ = l_Lean_Json_compress(v_params_2214_);
v___x_2223_ = lean_string_append(v___x_2221_, v___x_2222_);
lean_dec_ref(v___x_2222_);
v___x_2224_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1));
v___x_2225_ = lean_string_append(v___x_2223_, v___x_2224_);
v___x_2226_ = lean_string_append(v___x_2225_, v_a_2216_);
lean_dec(v_a_2216_);
v___x_2227_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set_uint8(v___x_2227_, sizeof(void*)*1, v___x_2220_);
if (v_isShared_2219_ == 0)
{
lean_ctor_set(v___x_2218_, 0, v___x_2227_);
v___x_2229_ = v___x_2218_;
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
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_params_2214_);
v_a_2232_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2215_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2215_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_j_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_j_2240_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2241_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2241_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2258_; 
v_a_2250_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2252_ = v___x_2241_;
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___x_2241_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2258_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v_textDocument_2254_; lean_object* v___x_2256_; 
v_textDocument_2254_ = lean_ctor_get(v_a_2250_, 1);
lean_inc_ref(v_textDocument_2254_);
lean_dec(v_a_2250_);
if (v_isShared_2253_ == 0)
{
lean_ctor_set(v___x_2252_, 0, v_textDocument_2254_);
v___x_2256_ = v___x_2252_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_textDocument_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(lean_object* v_method_2259_, lean_object* v_inst_2260_, lean_object* v_onDidChange_2261_, lean_object* v_param_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2259_, v___y_2263_, lean_box(0), v_inst_2260_, v___y_2264_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
lean_inc_ref(v___y_2264_);
v___x_2268_ = lean_apply_4(v_onDidChange_2261_, v_param_2262_, v_a_2267_, v___y_2264_, lean_box(0));
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2287_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2287_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2287_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v_snd_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2285_; 
v_snd_2273_ = lean_ctor_get(v_a_2269_, 1);
v_isSharedCheck_2285_ = !lean_is_exclusive(v_a_2269_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; 
v_unused_2286_ = lean_ctor_get(v_a_2269_, 0);
lean_dec(v_unused_2286_);
v___x_2275_ = v_a_2269_;
v_isShared_2276_ = v_isSharedCheck_2285_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_snd_2273_);
lean_dec(v_a_2269_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2285_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v_inst_2260_);
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_inst_2260_);
lean_ctor_set(v_reuseFailAlloc_2284_, 1, v_snd_2273_);
v___x_2278_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2282_; 
v___x_2279_ = lean_box(0);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
lean_ctor_set(v___x_2280_, 1, v___x_2278_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2280_);
v___x_2282_ = v___x_2271_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_inst_2260_);
v_a_2288_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2268_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2268_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec_ref(v_param_2262_);
lean_dec_ref(v_onDidChange_2261_);
lean_dec(v_inst_2260_);
v_a_2296_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2266_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2266_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2259_ = stack[0].m_obj;
lean_object* v_inst_2260_ = stack[1].m_obj;
lean_object* v_onDidChange_2261_ = stack[2].m_obj;
lean_object* v_param_2262_ = stack[3].m_obj;
lean_object* v___y_2263_ = stack[4].m_obj;
lean_object* v___y_2264_ = stack[5].m_obj;
lean_object* v_res_2304_;
v_res_2304_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(v_method_2259_, v_inst_2260_, v_onDidChange_2261_, v_param_2262_, v___y_2263_, v___y_2264_);
stack->m_obj
 = v_res_2304_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed(lean_object* v_method_2305_, lean_object* v_inst_2306_, lean_object* v_onDidChange_2307_, lean_object* v_param_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(v_method_2305_, v_inst_2306_, v_onDidChange_2307_, v_param_2308_, v___y_2309_, v___y_2310_);
lean_dec_ref(v___y_2310_);
lean_dec(v___y_2309_);
lean_dec_ref(v_method_2305_);
return v_res_2312_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(size_t v_sz_2313_, size_t v_i_2314_, lean_object* v_bs_2315_){
_start:
{
uint8_t v___x_2316_; 
v___x_2316_ = lean_usize_dec_lt(v_i_2314_, v_sz_2313_);
if (v___x_2316_ == 0)
{
return v_bs_2315_;
}
else
{
lean_object* v_v_2317_; lean_object* v___x_2318_; lean_object* v_bs_x27_2319_; lean_object* v___x_2320_; size_t v___x_2321_; size_t v___x_2322_; lean_object* v___x_2323_; 
v_v_2317_ = lean_array_uget(v_bs_2315_, v_i_2314_);
v___x_2318_ = lean_unsigned_to_nat(0u);
v_bs_x27_2319_ = lean_array_uset(v_bs_2315_, v_i_2314_, v___x_2318_);
v___x_2320_ = l_Lean_Lsp_instToJsonInlayHint_toJson(v_v_2317_);
v___x_2321_ = ((size_t)1ULL);
v___x_2322_ = lean_usize_add(v_i_2314_, v___x_2321_);
v___x_2323_ = lean_array_uset(v_bs_x27_2319_, v_i_2314_, v___x_2320_);
v_i_2314_ = v___x_2322_;
v_bs_2315_ = v___x_2323_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2313_ = stack[0].m_num;
size_t v_i_2314_ = stack[1].m_num;
lean_object* v_bs_2315_ = stack[2].m_obj;
lean_object* v_res_2325_;
v_res_2325_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_2313_, v_i_2314_, v_bs_2315_);
stack->m_obj
 = v_res_2325_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8___boxed(lean_object* v_sz_2326_, lean_object* v_i_2327_, lean_object* v_bs_2328_){
_start:
{
size_t v_sz_boxed_2329_; size_t v_i_boxed_2330_; lean_object* v_res_2331_; 
v_sz_boxed_2329_ = lean_unbox_usize(v_sz_2326_);
lean_dec(v_sz_2326_);
v_i_boxed_2330_ = lean_unbox_usize(v_i_2327_);
lean_dec(v_i_2327_);
v_res_2331_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_boxed_2329_, v_i_boxed_2330_, v_bs_2328_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object* v_a_2332_){
_start:
{
size_t v_sz_2333_; size_t v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v_sz_2333_ = lean_array_size(v_a_2332_);
v___x_2334_ = ((size_t)0ULL);
v___x_2335_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_2333_, v___x_2334_, v_a_2332_);
v___x_2336_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
return v___x_2336_;
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_params_2337_){
_start:
{
lean_object* v___x_2339_; 
v___x_2339_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_params_2337_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
lean_ctor_set_tag(v___x_2342_, 1);
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
v_a_2348_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2339_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2339_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
lean_ctor_set_tag(v___x_2350_, 0);
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_2337_ = stack[0].m_obj;
lean_object* v_res_2356_;
v_res_2356_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2337_);
stack->m_obj
 = v_res_2356_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_params_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2357_);
return v_res_2359_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(lean_object* v_method_2360_, lean_object* v_inst_2361_, lean_object* v_handler_2362_, lean_object* v_param_2363_, lean_object* v_state_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_param_2363_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_object* v_a_2368_; lean_object* v___x_2369_; 
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
lean_inc(v_a_2368_);
lean_dec_ref_known(v___x_2367_, 1);
v___x_2369_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2360_, v_state_2364_, lean_box(0), v_inst_2361_, v___y_2365_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2371_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2369_, 1);
lean_inc_ref(v___y_2365_);
v___x_2371_ = lean_apply_4(v_handler_2362_, v_a_2368_, v_a_2370_, v___y_2365_, lean_box(0));
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2395_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2395_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2395_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v_fst_2376_; lean_object* v_snd_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2394_; 
v_fst_2376_ = lean_ctor_get(v_a_2372_, 0);
v_snd_2377_ = lean_ctor_get(v_a_2372_, 1);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_a_2372_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2379_ = v_a_2372_;
v_isShared_2380_ = v_isSharedCheck_2394_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_snd_2377_);
lean_inc(v_fst_2376_);
lean_dec(v_a_2372_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2394_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_response_2381_; uint8_t v_isComplete_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v_response_2381_ = lean_ctor_get(v_fst_2376_, 0);
lean_inc(v_response_2381_);
v_isComplete_2382_ = lean_ctor_get_uint8(v_fst_2376_, sizeof(void*)*1);
lean_dec(v_fst_2376_);
v___x_2383_ = l_Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(v_response_2381_);
lean_inc(v___x_2383_);
v___x_2384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
v___x_2385_ = l_Lean_Json_compress(v___x_2383_);
v___x_2386_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2386_, 0, v___x_2384_);
lean_ctor_set(v___x_2386_, 1, v___x_2385_);
lean_ctor_set_uint8(v___x_2386_, sizeof(void*)*2, v_isComplete_2382_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v_inst_2361_);
v___x_2388_ = v___x_2379_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_inst_2361_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_snd_2377_);
v___x_2388_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
lean_object* v___x_2389_; lean_object* v___x_2391_; 
v___x_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2386_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2389_);
v___x_2391_ = v___x_2374_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v___x_2389_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_dec(v_inst_2361_);
v_a_2396_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2371_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2371_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec(v_a_2368_);
lean_dec_ref(v_handler_2362_);
lean_dec(v_inst_2361_);
v_a_2404_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2369_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2369_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec_ref(v_handler_2362_);
lean_dec(v_inst_2361_);
v_a_2412_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2367_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2367_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2360_ = stack[0].m_obj;
lean_object* v_inst_2361_ = stack[1].m_obj;
lean_object* v_handler_2362_ = stack[2].m_obj;
lean_object* v_param_2363_ = stack[3].m_obj;
lean_object* v_state_2364_ = stack[4].m_obj;
lean_object* v___y_2365_ = stack[5].m_obj;
lean_object* v_res_2420_;
v_res_2420_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(v_method_2360_, v_inst_2361_, v_handler_2362_, v_param_2363_, v_state_2364_, v___y_2365_);
stack->m_obj
 = v_res_2420_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed(lean_object* v_method_2421_, lean_object* v_inst_2422_, lean_object* v_handler_2423_, lean_object* v_param_2424_, lean_object* v_state_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(v_method_2421_, v_inst_2422_, v_handler_2423_, v_param_2424_, v_state_2425_, v___y_2426_);
lean_dec_ref(v___y_2426_);
lean_dec(v_state_2425_);
lean_dec_ref(v_method_2421_);
return v_res_2428_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(lean_object* v___f_2429_, lean_object* v___f_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_st_ref_get(v___y_2431_);
v___x_2435_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_2434_, v___f_2429_, v___y_2432_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2445_; 
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2445_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2445_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2441_; lean_object* v___x_2443_; 
lean_inc(v_a_2436_);
v___x_2440_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2430_, v_a_2436_);
v___x_2441_ = lean_st_ref_swap(v___y_2431_, v___x_2440_);
lean_dec(v___x_2441_);
if (v_isShared_2439_ == 0)
{
v___x_2443_ = v___x_2438_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2436_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
else
{
lean_dec_ref(v___f_2430_);
return v___x_2435_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_2429_ = stack[0].m_obj;
lean_object* v___f_2430_ = stack[1].m_obj;
lean_object* v___y_2431_ = stack[2].m_obj;
lean_object* v___y_2432_ = stack[3].m_obj;
lean_object* v_res_2446_;
v_res_2446_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(v___f_2429_, v___f_2430_, v___y_2431_, v___y_2432_);
stack->m_obj
 = v_res_2446_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed(lean_object* v___f_2447_, lean_object* v___f_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(v___f_2447_, v___f_2448_, v___y_2449_, v___y_2450_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
return v_res_2452_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(lean_object* v_val_2453_, lean_object* v___f_2454_, lean_object* v_param_2455_, lean_object* v_x_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_st_ref_get(v_val_2453_);
lean_inc_ref(v___y_2457_);
v___x_2460_ = lean_apply_4(v___f_2454_, v_param_2455_, v___x_2459_, v___y_2457_, lean_box(0));
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2471_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2471_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2471_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v_fst_2465_; lean_object* v_snd_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v_fst_2465_ = lean_ctor_get(v_a_2461_, 0);
lean_inc(v_fst_2465_);
v_snd_2466_ = lean_ctor_get(v_a_2461_, 1);
lean_inc(v_snd_2466_);
lean_dec(v_a_2461_);
v___x_2467_ = lean_st_ref_swap(v_val_2453_, v_snd_2466_);
lean_dec(v___x_2467_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set(v___x_2463_, 0, v_fst_2465_);
v___x_2469_ = v___x_2463_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_fst_2465_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
v_a_2472_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2460_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2460_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2453_ = stack[0].m_obj;
lean_object* v___f_2454_ = stack[1].m_obj;
lean_object* v_param_2455_ = stack[2].m_obj;
lean_object* v_x_2456_ = stack[3].m_obj;
lean_object* v___y_2457_ = stack[4].m_obj;
lean_object* v_res_2480_;
v_res_2480_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(v_val_2453_, v___f_2454_, v_param_2455_, v_x_2456_, v___y_2457_);
stack->m_obj
 = v_res_2480_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed(lean_object* v_val_2481_, lean_object* v___f_2482_, lean_object* v_param_2483_, lean_object* v_x_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(v_val_2481_, v___f_2482_, v_param_2483_, v_x_2484_, v___y_2485_);
lean_dec_ref(v___y_2485_);
lean_dec(v_val_2481_);
return v_res_2487_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(lean_object* v_val_2488_, lean_object* v___f_2489_, lean_object* v___f_2490_, lean_object* v_val_2491_, lean_object* v_param_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v___f_2495_; lean_object* v___f_2496_; lean_object* v___x_2497_; 
v___f_2495_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_2495_, 0, v_val_2488_);
lean_closure_set(v___f_2495_, 1, v___f_2489_);
lean_closure_set(v___f_2495_, 2, v_param_2492_);
v___f_2496_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_2496_, 0, v___f_2495_);
lean_closure_set(v___f_2496_, 1, v___f_2490_);
v___x_2497_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_2491_, v___f_2496_, v___y_2493_);
return v___x_2497_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2488_ = stack[0].m_obj;
lean_object* v___f_2489_ = stack[1].m_obj;
lean_object* v___f_2490_ = stack[2].m_obj;
lean_object* v_val_2491_ = stack[3].m_obj;
lean_object* v_param_2492_ = stack[4].m_obj;
lean_object* v___y_2493_ = stack[5].m_obj;
lean_object* v_res_2498_;
v_res_2498_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(v_val_2488_, v___f_2489_, v___f_2490_, v_val_2491_, v_param_2492_, v___y_2493_);
stack->m_obj
 = v_res_2498_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed(lean_object* v_val_2499_, lean_object* v___f_2500_, lean_object* v___f_2501_, lean_object* v_val_2502_, lean_object* v_param_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(v_val_2499_, v___f_2500_, v___f_2501_, v_val_2502_, v_param_2503_, v___y_2504_);
lean_dec_ref(v___y_2504_);
return v_res_2506_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_box(0);
v___x_2515_ = lean_task_pure(v___x_2514_);
return v___x_2515_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_method_2516_, lean_object* v_completeness_2517_, lean_object* v_inst_2518_, lean_object* v_initState_2519_, lean_object* v_handler_2520_, lean_object* v_onDidChange_2521_){
_start:
{
lean_object* v___f_2523_; lean_object* v___f_2524_; lean_object* v___f_2525_; uint8_t v___x_2526_; 
v___f_2523_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc_n(v_inst_2518_, 2);
lean_inc_ref_n(v_method_2516_, 2);
v___f_2524_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_2524_, 0, v_method_2516_);
lean_closure_set(v___f_2524_, 1, v_inst_2518_);
lean_closure_set(v___f_2524_, 2, v_handler_2520_);
v___f_2525_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_2525_, 0, v_method_2516_);
lean_closure_set(v___f_2525_, 1, v_inst_2518_);
lean_closure_set(v___f_2525_, 2, v_onDidChange_2521_);
v___x_2526_ = l_Lean_initializing();
if (v___x_2526_ == 0)
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; 
lean_dec_ref(v___f_2525_);
lean_dec_ref(v___f_2524_);
lean_dec(v_initState_2519_);
lean_dec(v_inst_2518_);
lean_dec(v_completeness_2517_);
v___x_2527_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2528_ = lean_string_append(v___x_2527_, v_method_2516_);
lean_dec_ref(v_method_2516_);
v___x_2529_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2));
v___x_2530_ = lean_string_append(v___x_2528_, v___x_2529_);
v___x_2531_ = lean_mk_io_user_error(v___x_2530_);
v___x_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2532_, 0, v___x_2531_);
return v___x_2532_;
}
else
{
lean_object* v___x_2533_; lean_object* v___f_2534_; lean_object* v___f_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___f_2540_; lean_object* v___f_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2533_ = lean_box(0);
v___f_2534_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3));
v___f_2535_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4));
v___x_2536_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5);
v___x_2537_ = l_Std_Mutex_new___redArg(v___x_2536_);
v___x_2538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2538_, 0, v_inst_2518_);
lean_ctor_set(v___x_2538_, 1, v_initState_2519_);
lean_inc_ref(v___x_2538_);
v___x_2539_ = lean_st_mk_ref(v___x_2538_);
lean_inc_ref_n(v___x_2537_, 2);
lean_inc_ref(v___f_2524_);
lean_inc_n(v___x_2539_, 2);
v___f_2540_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2540_, 0, v___x_2539_);
lean_closure_set(v___f_2540_, 1, v___f_2524_);
lean_closure_set(v___f_2540_, 2, v___f_2534_);
lean_closure_set(v___f_2540_, 3, v___x_2537_);
lean_inc_ref(v___f_2525_);
v___f_2541_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_2541_, 0, v___x_2539_);
lean_closure_set(v___f_2541_, 1, v___f_2525_);
lean_closure_set(v___f_2541_, 2, v___x_2533_);
lean_closure_set(v___f_2541_, 3, v___f_2535_);
lean_closure_set(v___f_2541_, 4, v___x_2537_);
v___x_2542_ = l_Lean_Server_statefulRequestHandlers;
v___x_2543_ = lean_st_ref_take(v___x_2542_);
v___x_2544_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2544_, 0, v___f_2523_);
lean_ctor_set(v___x_2544_, 1, v___f_2524_);
lean_ctor_set(v___x_2544_, 2, v___f_2540_);
lean_ctor_set(v___x_2544_, 3, v___f_2525_);
lean_ctor_set(v___x_2544_, 4, v___f_2541_);
lean_ctor_set(v___x_2544_, 5, v___x_2537_);
lean_ctor_set(v___x_2544_, 6, v___x_2538_);
lean_ctor_set(v___x_2544_, 7, v___x_2539_);
lean_ctor_set(v___x_2544_, 8, v_completeness_2517_);
v___x_2545_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v___x_2543_, v_method_2516_, v___x_2544_);
v___x_2546_ = lean_st_ref_put(v___x_2542_, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
return v___x_2547_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2516_ = stack[0].m_obj;
lean_object* v_completeness_2517_ = stack[1].m_obj;
lean_object* v_inst_2518_ = stack[2].m_obj;
lean_object* v_initState_2519_ = stack[3].m_obj;
lean_object* v_handler_2520_ = stack[4].m_obj;
lean_object* v_onDidChange_2521_ = stack[5].m_obj;
lean_object* v_res_2548_;
v_res_2548_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2516_, v_completeness_2517_, v_inst_2518_, v_initState_2519_, v_handler_2520_, v_onDidChange_2521_);
stack->m_obj
 = v_res_2548_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_method_2549_, lean_object* v_completeness_2550_, lean_object* v_inst_2551_, lean_object* v_initState_2552_, lean_object* v_handler_2553_, lean_object* v_onDidChange_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2549_, v_completeness_2550_, v_inst_2551_, v_initState_2552_, v_handler_2553_, v_onDidChange_2554_);
return v_res_2556_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_2557_, lean_object* v_i_2558_, lean_object* v_k_2559_){
_start:
{
lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2560_ = lean_array_get_size(v_keys_2557_);
v___x_2561_ = lean_nat_dec_lt(v_i_2558_, v___x_2560_);
if (v___x_2561_ == 0)
{
lean_dec(v_i_2558_);
return v___x_2561_;
}
else
{
lean_object* v_k_x27_2562_; uint8_t v___x_2563_; 
v_k_x27_2562_ = lean_array_fget_borrowed(v_keys_2557_, v_i_2558_);
v___x_2563_ = lean_string_dec_eq(v_k_2559_, v_k_x27_2562_);
if (v___x_2563_ == 0)
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = lean_unsigned_to_nat(1u);
v___x_2565_ = lean_nat_add(v_i_2558_, v___x_2564_);
lean_dec(v_i_2558_);
v_i_2558_ = v___x_2565_;
goto _start;
}
else
{
lean_dec(v_i_2558_);
return v___x_2561_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2557_ = stack[0].m_obj;
lean_object* v_i_2558_ = stack[1].m_obj;
lean_object* v_k_2559_ = stack[2].m_obj;
uint8_t v_res_2567_;
v_res_2567_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2557_, v_i_2558_, v_k_2559_);
stack->m_num = v_res_2567_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_2568_, lean_object* v_i_2569_, lean_object* v_k_2570_){
_start:
{
uint8_t v_res_2571_; lean_object* v_r_2572_; 
v_res_2571_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2568_, v_i_2569_, v_k_2570_);
lean_dec_ref(v_k_2570_);
lean_dec_ref(v_keys_2568_);
v_r_2572_ = lean_box(v_res_2571_);
return v_r_2572_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2573_, size_t v_x_2574_, lean_object* v_x_2575_){
_start:
{
if (lean_obj_tag(v_x_2573_) == 0)
{
lean_object* v_es_2576_; lean_object* v___x_2577_; size_t v___x_2578_; size_t v___x_2579_; lean_object* v_j_2580_; lean_object* v___x_2581_; 
v_es_2576_ = lean_ctor_get(v_x_2573_, 0);
v___x_2577_ = lean_box(2);
v___x_2578_ = ((size_t)31ULL);
v___x_2579_ = lean_usize_land(v_x_2574_, v___x_2578_);
v_j_2580_ = lean_usize_to_nat(v___x_2579_);
v___x_2581_ = lean_array_get_borrowed(v___x_2577_, v_es_2576_, v_j_2580_);
lean_dec(v_j_2580_);
switch(lean_obj_tag(v___x_2581_))
{
case 0:
{
lean_object* v_key_2582_; uint8_t v___x_2583_; 
v_key_2582_ = lean_ctor_get(v___x_2581_, 0);
v___x_2583_ = lean_string_dec_eq(v_x_2575_, v_key_2582_);
return v___x_2583_;
}
case 1:
{
lean_object* v_node_2584_; size_t v___x_2585_; size_t v___x_2586_; 
v_node_2584_ = lean_ctor_get(v___x_2581_, 0);
v___x_2585_ = ((size_t)5ULL);
v___x_2586_ = lean_usize_shift_right(v_x_2574_, v___x_2585_);
v_x_2573_ = v_node_2584_;
v_x_2574_ = v___x_2586_;
goto _start;
}
default: 
{
uint8_t v___x_2588_; 
v___x_2588_ = 0;
return v___x_2588_;
}
}
}
else
{
lean_object* v_ks_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v_ks_2589_ = lean_ctor_get(v_x_2573_, 0);
v___x_2590_ = lean_unsigned_to_nat(0u);
v___x_2591_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_2589_, v___x_2590_, v_x_2575_);
return v___x_2591_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2573_ = stack[0].m_obj;
size_t v_x_2574_ = stack[1].m_num;
lean_object* v_x_2575_ = stack[2].m_obj;
uint8_t v_res_2592_;
v_res_2592_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2573_, v_x_2574_, v_x_2575_);
stack->m_num = v_res_2592_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_){
_start:
{
size_t v_x_3877__boxed_2596_; uint8_t v_res_2597_; lean_object* v_r_2598_; 
v_x_3877__boxed_2596_ = lean_unbox_usize(v_x_2594_);
lean_dec(v_x_2594_);
v_res_2597_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2593_, v_x_3877__boxed_2596_, v_x_2595_);
lean_dec_ref(v_x_2595_);
lean_dec_ref(v_x_2593_);
v_r_2598_ = lean_box(v_res_2597_);
return v_r_2598_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_2599_, lean_object* v_x_2600_){
_start:
{
uint64_t v___x_2601_; size_t v___x_2602_; uint8_t v___x_2603_; 
v___x_2601_ = lean_string_hash(v_x_2600_);
v___x_2602_ = lean_uint64_to_usize(v___x_2601_);
v___x_2603_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2599_, v___x_2602_, v_x_2600_);
return v___x_2603_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2599_ = stack[0].m_obj;
lean_object* v_x_2600_ = stack[1].m_obj;
uint8_t v_res_2604_;
v_res_2604_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2599_, v_x_2600_);
stack->m_num = v_res_2604_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2605_, lean_object* v_x_2606_){
_start:
{
uint8_t v_res_2607_; lean_object* v_r_2608_; 
v_res_2607_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2605_, v_x_2606_);
lean_dec_ref(v_x_2606_);
lean_dec_ref(v_x_2605_);
v_r_2608_ = lean_box(v_res_2607_);
return v_r_2608_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_method_2610_, lean_object* v_completeness_2611_, lean_object* v_inst_2612_, lean_object* v_initState_2613_, lean_object* v_handler_2614_, lean_object* v_onDidChange_2615_){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; uint8_t v___x_2619_; 
v___x_2617_ = l_Lean_Server_requestHandlers;
v___x_2618_ = lean_st_ref_get(v___x_2617_);
v___x_2619_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_2618_, v_method_2610_);
lean_dec(v___x_2618_);
if (v___x_2619_ == 0)
{
lean_object* v___x_2620_; 
v___x_2620_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2610_, v_completeness_2611_, v_inst_2612_, v_initState_2613_, v_handler_2614_, v_onDidChange_2615_);
return v___x_2620_;
}
else
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v_onDidChange_2615_);
lean_dec_ref(v_handler_2614_);
lean_dec(v_initState_2613_);
lean_dec(v_inst_2612_);
lean_dec(v_completeness_2611_);
v___x_2621_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2622_ = lean_string_append(v___x_2621_, v_method_2610_);
lean_dec_ref(v_method_2610_);
v___x_2623_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_2624_ = lean_string_append(v___x_2622_, v___x_2623_);
v___x_2625_ = lean_mk_io_user_error(v___x_2624_);
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2625_);
return v___x_2626_;
}
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2610_ = stack[0].m_obj;
lean_object* v_completeness_2611_ = stack[1].m_obj;
lean_object* v_inst_2612_ = stack[2].m_obj;
lean_object* v_initState_2613_ = stack[3].m_obj;
lean_object* v_handler_2614_ = stack[4].m_obj;
lean_object* v_onDidChange_2615_ = stack[5].m_obj;
lean_object* v_res_2627_;
v_res_2627_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2610_, v_completeness_2611_, v_inst_2612_, v_initState_2613_, v_handler_2614_, v_onDidChange_2615_);
stack->m_obj
 = v_res_2627_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_method_2628_, lean_object* v_completeness_2629_, lean_object* v_inst_2630_, lean_object* v_initState_2631_, lean_object* v_handler_2632_, lean_object* v_onDidChange_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2628_, v_completeness_2629_, v_inst_2630_, v_initState_2631_, v_handler_2632_, v_onDidChange_2633_);
return v_res_2635_;
}
}
lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(lean_object* v_method_2636_, lean_object* v_refreshMethod_2637_, lean_object* v_refreshIntervalMs_2638_, lean_object* v_inst_2639_, lean_object* v_initState_2640_, lean_object* v_handler_2641_, lean_object* v_onDidChange_2642_){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2644_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2644_, 0, v_refreshMethod_2637_);
lean_ctor_set(v___x_2644_, 1, v_refreshIntervalMs_2638_);
v___x_2645_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2636_, v___x_2644_, v_inst_2639_, v_initState_2640_, v_handler_2641_, v_onDidChange_2642_);
return v___x_2645_;
}
}
LEAN_EXPORT void l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2636_ = stack[0].m_obj;
lean_object* v_refreshMethod_2637_ = stack[1].m_obj;
lean_object* v_refreshIntervalMs_2638_ = stack[2].m_obj;
lean_object* v_inst_2639_ = stack[3].m_obj;
lean_object* v_initState_2640_ = stack[4].m_obj;
lean_object* v_handler_2641_ = stack[5].m_obj;
lean_object* v_onDidChange_2642_ = stack[6].m_obj;
lean_object* v_res_2646_;
v_res_2646_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2636_, v_refreshMethod_2637_, v_refreshIntervalMs_2638_, v_inst_2639_, v_initState_2640_, v_handler_2641_, v_onDidChange_2642_);
stack->m_obj
 = v_res_2646_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_method_2647_, lean_object* v_refreshMethod_2648_, lean_object* v_refreshIntervalMs_2649_, lean_object* v_inst_2650_, lean_object* v_initState_2651_, lean_object* v_handler_2652_, lean_object* v_onDidChange_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2647_, v_refreshMethod_2648_, v_refreshIntervalMs_2649_, v_inst_2650_, v_initState_2651_, v_handler_2652_, v_onDidChange_2653_);
return v_res_2655_;
}
}
lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2661_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_));
v___x_2662_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2663_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2664_ = lean_unsigned_to_nat(500u);
v___x_2665_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init));
v___x_2666_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2667_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2668_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v___x_2662_, v___x_2663_, v___x_2664_, v___x_2661_, v___x_2665_, v___x_2666_, v___x_2667_);
return v___x_2668_;
}
}
LEAN_EXPORT void l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2669_;
v_res_2669_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
stack->m_obj
 = v_res_2669_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2____boxed(lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
return v_res_2671_;
}
}
lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(lean_object* v_method_2672_, lean_object* v_refreshMethod_2673_, lean_object* v_refreshIntervalMs_2674_, lean_object* v_stateType_2675_, lean_object* v_inst_2676_, lean_object* v_initState_2677_, lean_object* v_handler_2678_, lean_object* v_onDidChange_2679_){
_start:
{
lean_object* v___x_2681_; 
v___x_2681_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2672_, v_refreshMethod_2673_, v_refreshIntervalMs_2674_, v_inst_2676_, v_initState_2677_, v_handler_2678_, v_onDidChange_2679_);
return v___x_2681_;
}
}
LEAN_EXPORT void l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2672_ = stack[0].m_obj;
lean_object* v_refreshMethod_2673_ = stack[1].m_obj;
lean_object* v_refreshIntervalMs_2674_ = stack[2].m_obj;
lean_object* v_inst_2676_ = stack[4].m_obj;
lean_object* v_initState_2677_ = stack[5].m_obj;
lean_object* v_handler_2678_ = stack[6].m_obj;
lean_object* v_onDidChange_2679_ = stack[7].m_obj;
lean_object* v_res_2682_;
v_res_2682_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(v_method_2672_, v_refreshMethod_2673_, v_refreshIntervalMs_2674_, lean_box(0), v_inst_2676_, v_initState_2677_, v_handler_2678_, v_onDidChange_2679_);
stack->m_obj
 = v_res_2682_;
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2683_, lean_object* v_refreshMethod_2684_, lean_object* v_refreshIntervalMs_2685_, lean_object* v_stateType_2686_, lean_object* v_inst_2687_, lean_object* v_initState_2688_, lean_object* v_handler_2689_, lean_object* v_onDidChange_2690_, lean_object* v_a_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(v_method_2683_, v_refreshMethod_2684_, v_refreshIntervalMs_2685_, v_stateType_2686_, v_inst_2687_, v_initState_2688_, v_handler_2689_, v_onDidChange_2690_);
return v_res_2692_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_2693_, lean_object* v_completeness_2694_, lean_object* v_stateType_2695_, lean_object* v_inst_2696_, lean_object* v_initState_2697_, lean_object* v_handler_2698_, lean_object* v_onDidChange_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2693_, v_completeness_2694_, v_inst_2696_, v_initState_2697_, v_handler_2698_, v_onDidChange_2699_);
return v___x_2701_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2693_ = stack[0].m_obj;
lean_object* v_completeness_2694_ = stack[1].m_obj;
lean_object* v_inst_2696_ = stack[3].m_obj;
lean_object* v_initState_2697_ = stack[4].m_obj;
lean_object* v_handler_2698_ = stack[5].m_obj;
lean_object* v_onDidChange_2699_ = stack[6].m_obj;
lean_object* v_res_2702_;
v_res_2702_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(v_method_2693_, v_completeness_2694_, lean_box(0), v_inst_2696_, v_initState_2697_, v_handler_2698_, v_onDidChange_2699_);
stack->m_obj
 = v_res_2702_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_method_2703_, lean_object* v_completeness_2704_, lean_object* v_stateType_2705_, lean_object* v_inst_2706_, lean_object* v_initState_2707_, lean_object* v_handler_2708_, lean_object* v_onDidChange_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(v_method_2703_, v_completeness_2704_, v_stateType_2705_, v_inst_2706_, v_initState_2707_, v_handler_2708_, v_onDidChange_2709_);
return v_res_2711_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2712_, lean_object* v_x_2713_, lean_object* v_x_2714_){
_start:
{
uint8_t v___x_2715_; 
v___x_2715_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2713_, v_x_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2713_ = stack[1].m_obj;
lean_object* v_x_2714_ = stack[2].m_obj;
uint8_t v_res_2716_;
v_res_2716_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_box(0), v_x_2713_, v_x_2714_);
stack->m_num = v_res_2716_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_){
_start:
{
uint8_t v_res_2720_; lean_object* v_r_2721_; 
v_res_2720_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2717_, v_x_2718_, v_x_2719_);
lean_dec_ref(v_x_2719_);
lean_dec_ref(v_x_2718_);
v_r_2721_ = lean_box(v_res_2720_);
return v_r_2721_;
}
}
lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b1_2722_, lean_object* v_00_u03b2_2723_, lean_object* v_mutex_2724_, lean_object* v_k_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v___x_2728_; 
v___x_2728_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2724_, v_k_2725_, v___y_2726_);
return v___x_2728_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_2724_ = stack[2].m_obj;
lean_object* v_k_2725_ = stack[3].m_obj;
lean_object* v___y_2726_ = stack[4].m_obj;
lean_object* v_res_2729_;
v_res_2729_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(lean_box(0), lean_box(0), v_mutex_2724_, v_k_2725_, v___y_2726_);
stack->m_obj
 = v_res_2729_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2730_, lean_object* v_00_u03b2_2731_, lean_object* v_mutex_2732_, lean_object* v_k_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(v_00_u03b1_2730_, v_00_u03b2_2731_, v_mutex_2732_, v_k_2733_, v___y_2734_);
lean_dec_ref(v___y_2734_);
return v_res_2736_;
}
}
lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_method_2737_, lean_object* v_completeness_2738_, lean_object* v_stateType_2739_, lean_object* v_inst_2740_, lean_object* v_initState_2741_, lean_object* v_handler_2742_, lean_object* v_onDidChange_2743_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2737_, v_completeness_2738_, v_inst_2740_, v_initState_2741_, v_handler_2742_, v_onDidChange_2743_);
return v___x_2745_;
}
}
LEAN_EXPORT void l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_method_2737_ = stack[0].m_obj;
lean_object* v_completeness_2738_ = stack[1].m_obj;
lean_object* v_inst_2740_ = stack[3].m_obj;
lean_object* v_initState_2741_ = stack[4].m_obj;
lean_object* v_handler_2742_ = stack[5].m_obj;
lean_object* v_onDidChange_2743_ = stack[6].m_obj;
lean_object* v_res_2746_;
v_res_2746_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_method_2737_, v_completeness_2738_, lean_box(0), v_inst_2740_, v_initState_2741_, v_handler_2742_, v_onDidChange_2743_);
stack->m_obj
 = v_res_2746_;
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_method_2747_, lean_object* v_completeness_2748_, lean_object* v_stateType_2749_, lean_object* v_inst_2750_, lean_object* v_initState_2751_, lean_object* v_handler_2752_, lean_object* v_onDidChange_2753_, lean_object* v_a_2754_){
_start:
{
lean_object* v_res_2755_; 
v_res_2755_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_method_2747_, v_completeness_2748_, v_stateType_2749_, v_inst_2750_, v_initState_2751_, v_handler_2752_, v_onDidChange_2753_);
return v_res_2755_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2756_, lean_object* v_x_2757_, size_t v_x_2758_, lean_object* v_x_2759_){
_start:
{
uint8_t v___x_2760_; 
v___x_2760_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2757_, v_x_2758_, v_x_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2757_ = stack[1].m_obj;
size_t v_x_2758_ = stack[2].m_num;
lean_object* v_x_2759_ = stack[3].m_obj;
uint8_t v_res_2761_;
v_res_2761_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_box(0), v_x_2757_, v_x_2758_, v_x_2759_);
stack->m_num = v_res_2761_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2762_, lean_object* v_x_2763_, lean_object* v_x_2764_, lean_object* v_x_2765_){
_start:
{
size_t v_x_4129__boxed_2766_; uint8_t v_res_2767_; lean_object* v_r_2768_; 
v_x_4129__boxed_2766_ = lean_unbox_usize(v_x_2764_);
lean_dec(v_x_2764_);
v_res_2767_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2762_, v_x_2763_, v_x_4129__boxed_2766_, v_x_2765_);
lean_dec_ref(v_x_2765_);
lean_dec_ref(v_x_2763_);
v_r_2768_ = lean_box(v_res_2767_);
return v_r_2768_;
}
}
lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_params_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2769_);
return v___x_2772_;
}
}
LEAN_EXPORT void l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_params_2769_ = stack[0].m_obj;
lean_object* v_a_2770_ = stack[1].m_obj;
lean_object* v_res_2773_;
v_res_2773_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_params_2769_, v_a_2770_);
stack->m_obj
 = v_res_2773_;
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_params_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_params_2774_, v_a_2775_);
lean_dec_ref(v_a_2775_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_2778_, lean_object* v_x_2779_, lean_object* v_x_2780_, lean_object* v_x_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v_x_2779_, v_x_2780_, v_x_2781_);
return v___x_2782_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2783_, lean_object* v_keys_2784_, lean_object* v_vals_2785_, lean_object* v_heq_2786_, lean_object* v_i_2787_, lean_object* v_k_2788_){
_start:
{
uint8_t v___x_2789_; 
v___x_2789_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2784_, v_i_2787_, v_k_2788_);
return v___x_2789_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_2784_ = stack[1].m_obj;
lean_object* v_vals_2785_ = stack[2].m_obj;
lean_object* v_i_2787_ = stack[4].m_obj;
lean_object* v_k_2788_ = stack[5].m_obj;
uint8_t v_res_2790_;
v_res_2790_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(lean_box(0), v_keys_2784_, v_vals_2785_, lean_box(0), v_i_2787_, v_k_2788_);
stack->m_num = v_res_2790_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2791_, lean_object* v_keys_2792_, lean_object* v_vals_2793_, lean_object* v_heq_2794_, lean_object* v_i_2795_, lean_object* v_k_2796_){
_start:
{
uint8_t v_res_2797_; lean_object* v_r_2798_; 
v_res_2797_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_2791_, v_keys_2792_, v_vals_2793_, v_heq_2794_, v_i_2795_, v_k_2796_);
lean_dec_ref(v_k_2796_);
lean_dec_ref(v_vals_2793_);
lean_dec_ref(v_keys_2792_);
v_r_2798_ = lean_box(v_res_2797_);
return v_r_2798_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_2799_, lean_object* v_x_2800_, size_t v_x_2801_, size_t v_x_2802_, lean_object* v_x_2803_, lean_object* v_x_2804_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_2800_, v_x_2801_, v_x_2802_, v_x_2803_, v_x_2804_);
return v___x_2805_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2800_ = stack[1].m_obj;
size_t v_x_2801_ = stack[2].m_num;
size_t v_x_2802_ = stack[3].m_num;
lean_object* v_x_2803_ = stack[4].m_obj;
lean_object* v_x_2804_ = stack[5].m_obj;
lean_object* v_res_2806_;
v_res_2806_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(lean_box(0), v_x_2800_, v_x_2801_, v_x_2802_, v_x_2803_, v_x_2804_);
stack->m_obj
 = v_res_2806_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2807_, lean_object* v_x_2808_, lean_object* v_x_2809_, lean_object* v_x_2810_, lean_object* v_x_2811_, lean_object* v_x_2812_){
_start:
{
size_t v_x_4170__boxed_2813_; size_t v_x_4171__boxed_2814_; lean_object* v_res_2815_; 
v_x_4170__boxed_2813_ = lean_unbox_usize(v_x_2809_);
lean_dec(v_x_2809_);
v_x_4171__boxed_2814_ = lean_unbox_usize(v_x_2810_);
lean_dec(v_x_2810_);
v_res_2815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(v_00_u03b2_2807_, v_x_2808_, v_x_4170__boxed_2813_, v_x_4171__boxed_2814_, v_x_2811_, v_x_2812_);
return v_res_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_2816_, lean_object* v_n_2817_, lean_object* v_k_2818_, lean_object* v_v_2819_){
_start:
{
lean_object* v___x_2820_; 
v___x_2820_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v_n_2817_, v_k_2818_, v_v_2819_);
return v___x_2820_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(lean_object* v_00_u03b2_2821_, size_t v_depth_2822_, lean_object* v_keys_2823_, lean_object* v_vals_2824_, lean_object* v_heq_2825_, lean_object* v_i_2826_, lean_object* v_entries_2827_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_2822_, v_keys_2823_, v_vals_2824_, v_i_2826_, v_entries_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13_0interp(lean_interpreter_value* stack)
{
size_t v_depth_2822_ = stack[1].m_num;
lean_object* v_keys_2823_ = stack[2].m_obj;
lean_object* v_vals_2824_ = stack[3].m_obj;
lean_object* v_i_2826_ = stack[5].m_obj;
lean_object* v_entries_2827_ = stack[6].m_obj;
lean_object* v_res_2829_;
v_res_2829_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(lean_box(0), v_depth_2822_, v_keys_2823_, v_vals_2824_, lean_box(0), v_i_2826_, v_entries_2827_);
stack->m_obj
 = v_res_2829_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___boxed(lean_object* v_00_u03b2_2830_, lean_object* v_depth_2831_, lean_object* v_keys_2832_, lean_object* v_vals_2833_, lean_object* v_heq_2834_, lean_object* v_i_2835_, lean_object* v_entries_2836_){
_start:
{
size_t v_depth_boxed_2837_; lean_object* v_res_2838_; 
v_depth_boxed_2837_ = lean_unbox_usize(v_depth_2831_);
lean_dec(v_depth_2831_);
v_res_2838_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(v_00_u03b2_2830_, v_depth_boxed_2837_, v_keys_2832_, v_vals_2833_, v_heq_2834_, v_i_2835_, v_entries_2836_);
lean_dec_ref(v_vals_2833_);
lean_dec_ref(v_keys_2832_);
return v_res_2838_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_2839_, lean_object* v_x_2840_, lean_object* v_x_2841_, lean_object* v_x_2842_, lean_object* v_x_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_x_2840_, v_x_2841_, v_x_2842_, v_x_2843_);
return v___x_2844_;
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
