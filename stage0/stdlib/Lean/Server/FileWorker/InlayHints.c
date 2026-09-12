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
lean_object* v_v_96_; lean_object* v___x_97_; lean_object* v_bs_x27_98_; lean_object* v___x_99_; 
v_v_96_ = lean_array_uget(v_bs_92_, v_i_91_);
v___x_97_ = lean_unsigned_to_nat(0u);
v_bs_x27_98_ = lean_array_uset(v_bs_92_, v_i_91_, v___x_97_);
lean_inc_ref(v_text_89_);
v___x_99_ = l_Lean_Elab_InlayHintLabelPart_toLspInlayHintLabelPart(v_text_89_, v_v_96_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_99_, 1);
v___x_101_ = ((size_t)1ULL);
v___x_102_ = lean_usize_add(v_i_91_, v___x_101_);
v___x_103_ = lean_array_uset(v_bs_x27_98_, v_i_91_, v_a_100_);
v_i_91_ = v___x_102_;
v_bs_92_ = v___x_103_;
goto _start;
}
else
{
lean_object* v_a_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_112_; 
lean_dec_ref(v_bs_x27_98_);
lean_dec_ref(v_text_89_);
v_a_105_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_112_ == 0)
{
v___x_107_ = v___x_99_;
v_isShared_108_ = v_isSharedCheck_112_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_a_105_);
lean_dec(v___x_99_);
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
lean_object* v_start_283_; lean_object* v_stop_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_start_283_ = lean_ctor_get(v_range_280_, 0);
lean_inc(v_start_283_);
v_stop_284_ = lean_ctor_get(v_range_280_, 1);
lean_inc(v_stop_284_);
lean_dec_ref(v_range_280_);
v___x_285_ = lean_unsigned_to_nat(1u);
v___x_286_ = lean_nat_add(v_stop_284_, v___x_285_);
v___x_287_ = lean_nat_dec_le(v___x_286_, v_p_282_);
lean_dec(v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; uint8_t v___x_289_; 
v___x_288_ = lean_nat_add(v_p_282_, v___x_285_);
v___x_289_ = lean_nat_dec_le(v___x_288_, v_start_283_);
lean_dec(v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1));
v___x_292_ = lean_unsigned_to_nat(87u);
v___x_293_ = lean_unsigned_to_nat(6u);
v___x_294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2));
v___x_295_ = l_Nat_reprFast(v_p_282_);
v___x_296_ = lean_string_append(v___x_294_, v___x_295_);
lean_dec_ref(v___x_295_);
v___x_297_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3));
v___x_298_ = lean_string_append(v___x_296_, v___x_297_);
v___x_299_ = l_Nat_reprFast(v_start_283_);
v___x_300_ = lean_string_append(v___x_298_, v___x_299_);
lean_dec_ref(v___x_299_);
v___x_301_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4));
v___x_302_ = lean_string_append(v___x_300_, v___x_301_);
v___x_303_ = l_Nat_reprFast(v_stop_284_);
v___x_304_ = lean_string_append(v___x_302_, v___x_303_);
lean_dec_ref(v___x_303_);
v___x_305_ = l_mkPanicMessageWithDecl(v___x_290_, v___x_291_, v___x_292_, v___x_293_, v___x_304_);
lean_dec_ref(v___x_304_);
v___x_306_ = l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(v___x_305_);
return v___x_306_;
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
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v_stop_284_);
lean_dec(v_start_283_);
v___x_307_ = lean_nat_to_int(v_p_282_);
v___x_308_ = lean_int_add(v___x_307_, v_byteOffset_281_);
lean_dec(v___x_307_);
v___x_309_ = l_Int_toNat(v___x_308_);
lean_dec(v___x_308_);
return v___x_309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___boxed(lean_object* v_range_310_, lean_object* v_byteOffset_311_, lean_object* v_p_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_310_, v_byteOffset_311_, v_p_312_);
lean_dec(v_byteOffset_311_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(lean_object* v_hintMod_314_, lean_object* v_range_315_, lean_object* v_byteOffset_316_, size_t v_sz_317_, size_t v_i_318_, lean_object* v_bs_319_){
_start:
{
uint8_t v___x_320_; 
v___x_320_ = lean_usize_dec_lt(v_i_318_, v_sz_317_);
if (v___x_320_ == 0)
{
lean_dec_ref(v_range_315_);
return v_bs_319_;
}
else
{
lean_object* v_v_321_; lean_object* v_value_322_; lean_object* v_tooltip_x3f_323_; lean_object* v_location_x3f_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_367_; 
v_v_321_ = lean_array_uget(v_bs_319_, v_i_318_);
v_value_322_ = lean_ctor_get(v_v_321_, 0);
v_tooltip_x3f_323_ = lean_ctor_get(v_v_321_, 1);
v_location_x3f_324_ = lean_ctor_get(v_v_321_, 2);
v_isSharedCheck_367_ = !lean_is_exclusive(v_v_321_);
if (v_isSharedCheck_367_ == 0)
{
v___x_326_ = v_v_321_;
v_isShared_327_ = v_isSharedCheck_367_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_location_x3f_324_);
lean_inc(v_tooltip_x3f_323_);
lean_inc(v_value_322_);
lean_dec(v_v_321_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_367_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v_bs_x27_329_; lean_object* v___y_331_; lean_object* v___y_337_; 
v___x_328_ = lean_unsigned_to_nat(0u);
v_bs_x27_329_ = lean_array_uset(v_bs_319_, v_i_318_, v___x_328_);
if (lean_obj_tag(v_location_x3f_324_) == 0)
{
lean_object* v___x_342_; 
lean_del_object(v___x_326_);
v___x_342_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_342_, 0, v_value_322_);
lean_ctor_set(v___x_342_, 1, v_tooltip_x3f_323_);
lean_ctor_set(v___x_342_, 2, v_location_x3f_324_);
v___y_331_ = v___x_342_;
goto v___jp_330_;
}
else
{
lean_object* v_val_343_; lean_object* v_module_344_; lean_object* v_range_345_; uint8_t v___x_346_; 
v_val_343_ = lean_ctor_get(v_location_x3f_324_, 0);
lean_inc(v_val_343_);
lean_dec_ref_known(v_location_x3f_324_, 1);
v_module_344_ = lean_ctor_get(v_val_343_, 0);
v_range_345_ = lean_ctor_get(v_val_343_, 1);
lean_inc_ref(v_range_345_);
v___x_346_ = lean_name_eq(v_module_344_, v_hintMod_314_);
if (v___x_346_ == 0)
{
lean_dec_ref(v_range_345_);
v___y_337_ = v_val_343_;
goto v___jp_336_;
}
else
{
lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_364_; 
lean_inc(v_module_344_);
v_isSharedCheck_364_ = !lean_is_exclusive(v_val_343_);
if (v_isSharedCheck_364_ == 0)
{
lean_object* v_unused_365_; lean_object* v_unused_366_; 
v_unused_365_ = lean_ctor_get(v_val_343_, 1);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_val_343_, 0);
lean_dec(v_unused_366_);
v___x_348_ = v_val_343_;
v_isShared_349_ = v_isSharedCheck_364_;
goto v_resetjp_347_;
}
else
{
lean_dec(v_val_343_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_364_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v_start_350_; lean_object* v_stop_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_363_; 
v_start_350_ = lean_ctor_get(v_range_345_, 0);
v_stop_351_ = lean_ctor_get(v_range_345_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_range_345_);
if (v_isSharedCheck_363_ == 0)
{
v___x_353_ = v_range_345_;
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_stop_351_);
lean_inc(v_start_350_);
lean_dec(v_range_345_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
lean_inc_ref_n(v_range_315_, 2);
v___x_355_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_315_, v_byteOffset_316_, v_start_350_);
v___x_356_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_315_, v_byteOffset_316_, v_stop_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_356_);
lean_ctor_set(v___x_353_, 0, v___x_355_);
v___x_358_ = v___x_353_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_355_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_356_);
v___x_358_ = v_reuseFailAlloc_362_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_360_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_358_);
v___x_360_ = v___x_348_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_module_344_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_358_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
v___y_337_ = v___x_360_;
goto v___jp_336_;
}
}
}
}
}
}
v___jp_330_:
{
size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; 
v___x_332_ = ((size_t)1ULL);
v___x_333_ = lean_usize_add(v_i_318_, v___x_332_);
v___x_334_ = lean_array_uset(v_bs_x27_329_, v_i_318_, v___y_331_);
v_i_318_ = v___x_333_;
v_bs_319_ = v___x_334_;
goto _start;
}
v___jp_336_:
{
lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_338_, 0, v___y_337_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 2, v___x_338_);
v___x_340_ = v___x_326_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_value_322_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_tooltip_x3f_323_);
lean_ctor_set(v_reuseFailAlloc_341_, 2, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
v___y_331_ = v___x_340_;
goto v___jp_330_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4___boxed(lean_object* v_hintMod_368_, lean_object* v_range_369_, lean_object* v_byteOffset_370_, lean_object* v_sz_371_, lean_object* v_i_372_, lean_object* v_bs_373_){
_start:
{
size_t v_sz_boxed_374_; size_t v_i_boxed_375_; lean_object* v_res_376_; 
v_sz_boxed_374_ = lean_unbox_usize(v_sz_371_);
lean_dec(v_sz_371_);
v_i_boxed_375_ = lean_unbox_usize(v_i_372_);
lean_dec(v_i_372_);
v_res_376_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_368_, v_range_369_, v_byteOffset_370_, v_sz_boxed_374_, v_i_boxed_375_, v_bs_373_);
lean_dec(v_byteOffset_370_);
lean_dec(v_hintMod_368_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(lean_object* v_hintMod_377_, lean_object* v_range_378_, lean_object* v_byteOffset_379_, size_t v_sz_380_, size_t v_i_381_, lean_object* v_bs_382_){
_start:
{
uint8_t v___x_383_; 
v___x_383_ = lean_usize_dec_lt(v_i_381_, v_sz_380_);
if (v___x_383_ == 0)
{
lean_dec_ref(v_range_378_);
return v_bs_382_;
}
else
{
lean_object* v_v_384_; lean_object* v_value_385_; lean_object* v_tooltip_x3f_386_; lean_object* v_location_x3f_387_; lean_object* v___x_389_; uint8_t v_isShared_390_; uint8_t v_isSharedCheck_430_; 
v_v_384_ = lean_array_uget(v_bs_382_, v_i_381_);
v_value_385_ = lean_ctor_get(v_v_384_, 0);
v_tooltip_x3f_386_ = lean_ctor_get(v_v_384_, 1);
v_location_x3f_387_ = lean_ctor_get(v_v_384_, 2);
v_isSharedCheck_430_ = !lean_is_exclusive(v_v_384_);
if (v_isSharedCheck_430_ == 0)
{
v___x_389_ = v_v_384_;
v_isShared_390_ = v_isSharedCheck_430_;
goto v_resetjp_388_;
}
else
{
lean_inc(v_location_x3f_387_);
lean_inc(v_tooltip_x3f_386_);
lean_inc(v_value_385_);
lean_dec(v_v_384_);
v___x_389_ = lean_box(0);
v_isShared_390_ = v_isSharedCheck_430_;
goto v_resetjp_388_;
}
v_resetjp_388_:
{
lean_object* v___x_391_; lean_object* v_bs_x27_392_; lean_object* v___y_394_; lean_object* v___y_400_; 
v___x_391_ = lean_unsigned_to_nat(0u);
v_bs_x27_392_ = lean_array_uset(v_bs_382_, v_i_381_, v___x_391_);
if (lean_obj_tag(v_location_x3f_387_) == 0)
{
lean_object* v___x_405_; 
lean_del_object(v___x_389_);
v___x_405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_405_, 0, v_value_385_);
lean_ctor_set(v___x_405_, 1, v_tooltip_x3f_386_);
lean_ctor_set(v___x_405_, 2, v_location_x3f_387_);
v___y_394_ = v___x_405_;
goto v___jp_393_;
}
else
{
lean_object* v_val_406_; lean_object* v_module_407_; lean_object* v_range_408_; uint8_t v___x_409_; 
v_val_406_ = lean_ctor_get(v_location_x3f_387_, 0);
lean_inc(v_val_406_);
lean_dec_ref_known(v_location_x3f_387_, 1);
v_module_407_ = lean_ctor_get(v_val_406_, 0);
v_range_408_ = lean_ctor_get(v_val_406_, 1);
lean_inc_ref(v_range_408_);
v___x_409_ = lean_name_eq(v_module_407_, v_hintMod_377_);
if (v___x_409_ == 0)
{
lean_dec_ref(v_range_408_);
v___y_400_ = v_val_406_;
goto v___jp_399_;
}
else
{
lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_427_; 
lean_inc(v_module_407_);
v_isSharedCheck_427_ = !lean_is_exclusive(v_val_406_);
if (v_isSharedCheck_427_ == 0)
{
lean_object* v_unused_428_; lean_object* v_unused_429_; 
v_unused_428_ = lean_ctor_get(v_val_406_, 1);
lean_dec(v_unused_428_);
v_unused_429_ = lean_ctor_get(v_val_406_, 0);
lean_dec(v_unused_429_);
v___x_411_ = v_val_406_;
v_isShared_412_ = v_isSharedCheck_427_;
goto v_resetjp_410_;
}
else
{
lean_dec(v_val_406_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_427_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v_start_413_; lean_object* v_stop_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_426_; 
v_start_413_ = lean_ctor_get(v_range_408_, 0);
v_stop_414_ = lean_ctor_get(v_range_408_, 1);
v_isSharedCheck_426_ = !lean_is_exclusive(v_range_408_);
if (v_isSharedCheck_426_ == 0)
{
v___x_416_ = v_range_408_;
v_isShared_417_ = v_isSharedCheck_426_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_stop_414_);
lean_inc(v_start_413_);
lean_dec(v_range_408_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_426_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
lean_inc_ref_n(v_range_378_, 2);
v___x_418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_378_, v_byteOffset_379_, v_start_413_);
v___x_419_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_378_, v_byteOffset_379_, v_stop_414_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 1, v___x_419_);
lean_ctor_set(v___x_416_, 0, v___x_418_);
v___x_421_ = v___x_416_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v___x_418_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v___x_419_);
v___x_421_ = v_reuseFailAlloc_425_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
lean_object* v___x_423_; 
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v___x_421_);
v___x_423_ = v___x_411_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_module_407_);
lean_ctor_set(v_reuseFailAlloc_424_, 1, v___x_421_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
v___y_400_ = v___x_423_;
goto v___jp_399_;
}
}
}
}
}
}
v___jp_393_:
{
size_t v___x_395_; size_t v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_add(v_i_381_, v___x_395_);
v___x_397_ = lean_array_uset(v_bs_x27_392_, v_i_381_, v___y_394_);
v___x_398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_377_, v_range_378_, v_byteOffset_379_, v_sz_380_, v___x_396_, v___x_397_);
return v___x_398_;
}
v___jp_399_:
{
lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_401_, 0, v___y_400_);
if (v_isShared_390_ == 0)
{
lean_ctor_set(v___x_389_, 2, v___x_401_);
v___x_403_ = v___x_389_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_value_385_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_tooltip_x3f_386_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
v___y_394_ = v___x_403_;
goto v___jp_393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3___boxed(lean_object* v_hintMod_431_, lean_object* v_range_432_, lean_object* v_byteOffset_433_, lean_object* v_sz_434_, lean_object* v_i_435_, lean_object* v_bs_436_){
_start:
{
size_t v_sz_boxed_437_; size_t v_i_boxed_438_; lean_object* v_res_439_; 
v_sz_boxed_437_ = lean_unbox_usize(v_sz_434_);
lean_dec(v_sz_434_);
v_i_boxed_438_ = lean_unbox_usize(v_i_435_);
lean_dec(v_i_435_);
v_res_439_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_431_, v_range_432_, v_byteOffset_433_, v_sz_boxed_437_, v_i_boxed_438_, v_bs_436_);
lean_dec(v_byteOffset_433_);
lean_dec(v_hintMod_431_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(lean_object* v_range_440_, lean_object* v_byteOffset_441_, size_t v_sz_442_, size_t v_i_443_, lean_object* v_bs_444_){
_start:
{
uint8_t v___x_445_; 
v___x_445_ = lean_usize_dec_lt(v_i_443_, v_sz_442_);
if (v___x_445_ == 0)
{
lean_dec_ref(v_range_440_);
return v_bs_444_;
}
else
{
lean_object* v_v_446_; lean_object* v_range_447_; lean_object* v_newText_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_472_; 
v_v_446_ = lean_array_uget(v_bs_444_, v_i_443_);
v_range_447_ = lean_ctor_get(v_v_446_, 0);
v_newText_448_ = lean_ctor_get(v_v_446_, 1);
v_isSharedCheck_472_ = !lean_is_exclusive(v_v_446_);
if (v_isSharedCheck_472_ == 0)
{
v___x_450_ = v_v_446_;
v_isShared_451_ = v_isSharedCheck_472_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_newText_448_);
lean_inc(v_range_447_);
lean_dec(v_v_446_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_472_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v_start_452_; lean_object* v_stop_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_471_; 
v_start_452_ = lean_ctor_get(v_range_447_, 0);
v_stop_453_ = lean_ctor_get(v_range_447_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_range_447_);
if (v_isSharedCheck_471_ == 0)
{
v___x_455_ = v_range_447_;
v_isShared_456_ = v_isSharedCheck_471_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_stop_453_);
lean_inc(v_start_452_);
lean_dec(v_range_447_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_471_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; lean_object* v_bs_x27_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v_bs_x27_458_ = lean_array_uset(v_bs_444_, v_i_443_, v___x_457_);
lean_inc_ref_n(v_range_440_, 2);
v___x_459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_440_, v_byteOffset_441_, v_start_452_);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_440_, v_byteOffset_441_, v_stop_453_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_460_);
lean_ctor_set(v___x_455_, 0, v___x_459_);
v___x_462_ = v___x_455_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_470_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
lean_object* v___x_464_; 
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 0, v___x_462_);
v___x_464_ = v___x_450_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_462_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_newText_448_);
v___x_464_ = v_reuseFailAlloc_469_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
size_t v___x_465_; size_t v___x_466_; lean_object* v___x_467_; 
v___x_465_ = ((size_t)1ULL);
v___x_466_ = lean_usize_add(v_i_443_, v___x_465_);
v___x_467_ = lean_array_uset(v_bs_x27_458_, v_i_443_, v___x_464_);
v_i_443_ = v___x_466_;
v_bs_444_ = v___x_467_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2___boxed(lean_object* v_range_473_, lean_object* v_byteOffset_474_, lean_object* v_sz_475_, lean_object* v_i_476_, lean_object* v_bs_477_){
_start:
{
size_t v_sz_boxed_478_; size_t v_i_boxed_479_; lean_object* v_res_480_; 
v_sz_boxed_478_ = lean_unbox_usize(v_sz_475_);
lean_dec(v_sz_475_);
v_i_boxed_479_ = lean_unbox_usize(v_i_476_);
lean_dec(v_i_476_);
v_res_480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_473_, v_byteOffset_474_, v_sz_boxed_478_, v_i_boxed_479_, v_bs_477_);
lean_dec(v_byteOffset_474_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(lean_object* v_range_481_, lean_object* v_byteOffset_482_, size_t v_sz_483_, size_t v_i_484_, lean_object* v_bs_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = lean_usize_dec_lt(v_i_484_, v_sz_483_);
if (v___x_486_ == 0)
{
lean_dec_ref(v_range_481_);
return v_bs_485_;
}
else
{
lean_object* v_v_487_; lean_object* v_range_488_; lean_object* v_newText_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_513_; 
v_v_487_ = lean_array_uget(v_bs_485_, v_i_484_);
v_range_488_ = lean_ctor_get(v_v_487_, 0);
v_newText_489_ = lean_ctor_get(v_v_487_, 1);
v_isSharedCheck_513_ = !lean_is_exclusive(v_v_487_);
if (v_isSharedCheck_513_ == 0)
{
v___x_491_ = v_v_487_;
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_newText_489_);
lean_inc(v_range_488_);
lean_dec(v_v_487_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_513_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_start_493_; lean_object* v_stop_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_512_; 
v_start_493_ = lean_ctor_get(v_range_488_, 0);
v_stop_494_ = lean_ctor_get(v_range_488_, 1);
v_isSharedCheck_512_ = !lean_is_exclusive(v_range_488_);
if (v_isSharedCheck_512_ == 0)
{
v___x_496_ = v_range_488_;
v_isShared_497_ = v_isSharedCheck_512_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_stop_494_);
lean_inc(v_start_493_);
lean_dec(v_range_488_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_512_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v_bs_x27_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_503_; 
v___x_498_ = lean_unsigned_to_nat(0u);
v_bs_x27_499_ = lean_array_uset(v_bs_485_, v_i_484_, v___x_498_);
lean_inc_ref_n(v_range_481_, 2);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_481_, v_byteOffset_482_, v_start_493_);
v___x_501_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_481_, v_byteOffset_482_, v_stop_494_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v___x_501_);
lean_ctor_set(v___x_496_, 0, v___x_500_);
v___x_503_ = v___x_496_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v___x_501_);
v___x_503_ = v_reuseFailAlloc_511_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_505_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v___x_503_);
v___x_505_ = v___x_491_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v___x_503_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_newText_489_);
v___x_505_ = v_reuseFailAlloc_510_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
size_t v___x_506_; size_t v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v___x_506_ = ((size_t)1ULL);
v___x_507_ = lean_usize_add(v_i_484_, v___x_506_);
v___x_508_ = lean_array_uset(v_bs_x27_499_, v_i_484_, v___x_505_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_481_, v_byteOffset_482_, v_sz_483_, v___x_507_, v___x_508_);
return v___x_509_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___boxed(lean_object* v_range_514_, lean_object* v_byteOffset_515_, lean_object* v_sz_516_, lean_object* v_i_517_, lean_object* v_bs_518_){
_start:
{
size_t v_sz_boxed_519_; size_t v_i_boxed_520_; lean_object* v_res_521_; 
v_sz_boxed_519_ = lean_unbox_usize(v_sz_516_);
lean_dec(v_sz_516_);
v_i_boxed_520_ = lean_unbox_usize(v_i_517_);
lean_dec(v_i_517_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_514_, v_byteOffset_515_, v_sz_boxed_519_, v_i_boxed_520_, v_bs_518_);
lean_dec(v_byteOffset_515_);
return v_res_521_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(lean_object* v_hintMod_522_, lean_object* v_range_523_, lean_object* v_as_524_, size_t v_i_525_, size_t v_stop_526_){
_start:
{
uint8_t v___x_531_; 
v___x_531_ = lean_usize_dec_eq(v_i_525_, v_stop_526_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v_location_x3f_533_; 
v___x_532_ = lean_array_uget_borrowed(v_as_524_, v_i_525_);
v_location_x3f_533_ = lean_ctor_get(v___x_532_, 2);
if (lean_obj_tag(v_location_x3f_533_) == 0)
{
goto v___jp_527_;
}
else
{
lean_object* v_val_534_; lean_object* v_module_535_; lean_object* v_range_536_; uint8_t v___x_537_; uint8_t v___y_539_; uint8_t v___x_540_; 
v_val_534_ = lean_ctor_get(v_location_x3f_533_, 0);
v_module_535_ = lean_ctor_get(v_val_534_, 0);
v_range_536_ = lean_ctor_get(v_val_534_, 1);
v___x_537_ = 1;
v___x_540_ = lean_name_eq(v_module_535_, v_hintMod_522_);
if (v___x_540_ == 0)
{
v___y_539_ = v___x_540_;
goto v___jp_538_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = l_Lean_Syntax_Range_overlaps(v_range_523_, v_range_536_, v___x_540_, v___x_531_);
v___y_539_ = v___x_541_;
goto v___jp_538_;
}
v___jp_538_:
{
if (v___y_539_ == 0)
{
goto v___jp_527_;
}
else
{
return v___x_537_;
}
}
}
}
else
{
uint8_t v___x_542_; 
v___x_542_ = 0;
return v___x_542_;
}
v___jp_527_:
{
size_t v___x_528_; size_t v___x_529_; 
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_525_, v___x_528_);
v_i_525_ = v___x_529_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5___boxed(lean_object* v_hintMod_543_, lean_object* v_range_544_, lean_object* v_as_545_, lean_object* v_i_546_, lean_object* v_stop_547_){
_start:
{
size_t v_i_boxed_548_; size_t v_stop_boxed_549_; uint8_t v_res_550_; lean_object* v_r_551_; 
v_i_boxed_548_ = lean_unbox_usize(v_i_546_);
lean_dec(v_i_546_);
v_stop_boxed_549_ = lean_unbox_usize(v_stop_547_);
lean_dec(v_stop_547_);
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_543_, v_range_544_, v_as_545_, v_i_boxed_548_, v_stop_boxed_549_);
lean_dec_ref(v_as_545_);
lean_dec_ref(v_range_544_);
lean_dec(v_hintMod_543_);
v_r_551_ = lean_box(v_res_550_);
return v_r_551_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(lean_object* v_range_552_, uint8_t v___x_553_, lean_object* v_as_554_, size_t v_i_555_, size_t v_stop_556_){
_start:
{
uint8_t v___x_557_; 
v___x_557_ = lean_usize_dec_eq(v_i_555_, v_stop_556_);
if (v___x_557_ == 0)
{
lean_object* v___x_558_; lean_object* v_range_559_; uint8_t v___x_560_; uint8_t v___x_561_; 
v___x_558_ = lean_array_uget_borrowed(v_as_554_, v_i_555_);
v_range_559_ = lean_ctor_get(v___x_558_, 0);
v___x_560_ = 1;
v___x_561_ = l_Lean_Syntax_Range_overlaps(v_range_552_, v_range_559_, v___x_560_, v___x_553_);
if (v___x_561_ == 0)
{
size_t v___x_562_; size_t v___x_563_; 
v___x_562_ = ((size_t)1ULL);
v___x_563_ = lean_usize_add(v_i_555_, v___x_562_);
v_i_555_ = v___x_563_;
goto _start;
}
else
{
return v___x_560_;
}
}
else
{
uint8_t v___x_565_; 
v___x_565_ = 0;
return v___x_565_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4___boxed(lean_object* v_range_566_, lean_object* v___x_567_, lean_object* v_as_568_, lean_object* v_i_569_, lean_object* v_stop_570_){
_start:
{
uint8_t v___x_2538__boxed_571_; size_t v_i_boxed_572_; size_t v_stop_boxed_573_; uint8_t v_res_574_; lean_object* v_r_575_; 
v___x_2538__boxed_571_ = lean_unbox(v___x_567_);
v_i_boxed_572_ = lean_unbox_usize(v_i_569_);
lean_dec(v_i_569_);
v_stop_boxed_573_ = lean_unbox_usize(v_stop_570_);
lean_dec(v_stop_570_);
v_res_574_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_566_, v___x_2538__boxed_571_, v_as_568_, v_i_boxed_572_, v_stop_boxed_573_);
lean_dec_ref(v_as_568_);
lean_dec_ref(v_range_566_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f(lean_object* v_hintMod_576_, lean_object* v_ihi_577_, lean_object* v_range_578_, lean_object* v_newText_579_){
_start:
{
lean_object* v_position_580_; lean_object* v_label_581_; lean_object* v_kind_x3f_582_; lean_object* v_textEdits_583_; lean_object* v_tooltip_x3f_584_; uint8_t v_paddingLeft_585_; uint8_t v_paddingRight_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_672_; 
v_position_580_ = lean_ctor_get(v_ihi_577_, 0);
v_label_581_ = lean_ctor_get(v_ihi_577_, 1);
v_kind_x3f_582_ = lean_ctor_get(v_ihi_577_, 2);
v_textEdits_583_ = lean_ctor_get(v_ihi_577_, 3);
v_tooltip_x3f_584_ = lean_ctor_get(v_ihi_577_, 4);
v_paddingLeft_585_ = lean_ctor_get_uint8(v_ihi_577_, sizeof(void*)*5);
v_paddingRight_586_ = lean_ctor_get_uint8(v_ihi_577_, sizeof(void*)*5 + 1);
v_isSharedCheck_672_ = !lean_is_exclusive(v_ihi_577_);
if (v_isSharedCheck_672_ == 0)
{
v___x_588_ = v_ihi_577_;
v_isShared_589_ = v_isSharedCheck_672_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_tooltip_x3f_584_);
lean_inc(v_textEdits_583_);
lean_inc(v_kind_x3f_582_);
lean_inc(v_label_581_);
lean_inc(v_position_580_);
lean_dec(v_ihi_577_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_672_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_602_; lean_object* v___y_603_; uint8_t v___y_616_; uint8_t v___y_651_; uint8_t v___y_652_; uint8_t v___y_655_; 
if (lean_obj_tag(v_label_581_) == 0)
{
uint8_t v___x_664_; 
v___x_664_ = 0;
v___y_655_ = v___x_664_;
goto v___jp_654_;
}
else
{
lean_object* v_p_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_p_665_ = lean_ctor_get(v_label_581_, 0);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_array_get_size(v_p_665_);
v___x_668_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
v___y_655_ = v___x_668_;
goto v___jp_654_;
}
else
{
if (v___x_668_ == 0)
{
v___y_655_ = v___x_668_;
goto v___jp_654_;
}
else
{
size_t v___x_669_; size_t v___x_670_; uint8_t v___x_671_; 
v___x_669_ = ((size_t)0ULL);
v___x_670_ = lean_usize_of_nat(v___x_667_);
v___x_671_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_576_, v_range_578_, v_p_665_, v___x_669_, v___x_670_);
v___y_655_ = v___x_671_;
goto v___jp_654_;
}
}
}
v___jp_590_:
{
size_t v_sz_594_; size_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_598_; 
v_sz_594_ = lean_array_size(v_textEdits_583_);
v___x_595_ = ((size_t)0ULL);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_578_, v___y_591_, v_sz_594_, v___x_595_, v_textEdits_583_);
lean_dec(v___y_591_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 3, v___x_596_);
lean_ctor_set(v___x_588_, 1, v___y_593_);
lean_ctor_set(v___x_588_, 0, v___y_592_);
v___x_598_ = v___x_588_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___y_592_);
lean_ctor_set(v_reuseFailAlloc_600_, 1, v___y_593_);
lean_ctor_set(v_reuseFailAlloc_600_, 2, v_kind_x3f_582_);
lean_ctor_set(v_reuseFailAlloc_600_, 3, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_600_, 4, v_tooltip_x3f_584_);
lean_ctor_set_uint8(v_reuseFailAlloc_600_, sizeof(void*)*5, v_paddingLeft_585_);
lean_ctor_set_uint8(v_reuseFailAlloc_600_, sizeof(void*)*5 + 1, v_paddingRight_586_);
v___x_598_ = v_reuseFailAlloc_600_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; 
v___x_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_599_, 0, v___x_598_);
return v___x_599_;
}
}
v___jp_601_:
{
if (lean_obj_tag(v_label_581_) == 0)
{
v___y_591_ = v___y_602_;
v___y_592_ = v___y_603_;
v___y_593_ = v_label_581_;
goto v___jp_590_;
}
else
{
lean_object* v_p_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_614_; 
v_p_604_ = lean_ctor_get(v_label_581_, 0);
v_isSharedCheck_614_ = !lean_is_exclusive(v_label_581_);
if (v_isSharedCheck_614_ == 0)
{
v___x_606_ = v_label_581_;
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_p_604_);
lean_dec(v_label_581_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
size_t v_sz_608_; size_t v___x_609_; lean_object* v___x_610_; lean_object* v___x_612_; 
v_sz_608_ = lean_array_size(v_p_604_);
v___x_609_ = ((size_t)0ULL);
lean_inc_ref(v_range_578_);
v___x_610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_576_, v_range_578_, v___y_602_, v_sz_608_, v___x_609_, v_p_604_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_610_);
v___x_612_ = v___x_606_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
v___y_591_ = v___y_602_;
v___y_592_ = v___y_603_;
v___y_593_ = v___x_612_;
goto v___jp_590_;
}
}
}
}
v___jp_615_:
{
if (v___y_616_ == 0)
{
lean_object* v_start_617_; lean_object* v_stop_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_byteOffset_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_start_617_ = lean_ctor_get(v_range_578_, 0);
v_stop_618_ = lean_ctor_get(v_range_578_, 1);
v___x_619_ = lean_string_utf8_byte_size(v_newText_579_);
v___x_620_ = lean_nat_to_int(v___x_619_);
v___x_621_ = l_Lean_Syntax_Range_bsize(v_range_578_);
v___x_622_ = lean_nat_to_int(v___x_621_);
v_byteOffset_623_ = lean_int_sub(v___x_620_, v___x_622_);
lean_dec(v___x_622_);
lean_dec(v___x_620_);
v___x_624_ = lean_unsigned_to_nat(1u);
v___x_625_ = lean_nat_add(v_stop_618_, v___x_624_);
v___x_626_ = lean_nat_dec_le(v___x_625_, v_position_580_);
lean_dec(v___x_625_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_627_ = lean_nat_add(v_position_580_, v___x_624_);
v___x_628_ = lean_nat_dec_le(v___x_627_, v_start_617_);
lean_dec(v___x_627_);
if (v___x_628_ == 0)
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1));
v___x_631_ = lean_unsigned_to_nat(87u);
v___x_632_ = lean_unsigned_to_nat(6u);
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2));
v___x_634_ = l_Nat_reprFast(v_position_580_);
v___x_635_ = lean_string_append(v___x_633_, v___x_634_);
lean_dec_ref(v___x_634_);
v___x_636_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3));
v___x_637_ = lean_string_append(v___x_635_, v___x_636_);
lean_inc(v_start_617_);
v___x_638_ = l_Nat_reprFast(v_start_617_);
v___x_639_ = lean_string_append(v___x_637_, v___x_638_);
lean_dec_ref(v___x_638_);
v___x_640_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4));
v___x_641_ = lean_string_append(v___x_639_, v___x_640_);
lean_inc(v_stop_618_);
v___x_642_ = l_Nat_reprFast(v_stop_618_);
v___x_643_ = lean_string_append(v___x_641_, v___x_642_);
lean_dec_ref(v___x_642_);
v___x_644_ = l_mkPanicMessageWithDecl(v___x_629_, v___x_630_, v___x_631_, v___x_632_, v___x_643_);
lean_dec_ref(v___x_643_);
v___x_645_ = l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(v___x_644_);
v___y_602_ = v_byteOffset_623_;
v___y_603_ = v___x_645_;
goto v___jp_601_;
}
else
{
v___y_602_ = v_byteOffset_623_;
v___y_603_ = v_position_580_;
goto v___jp_601_;
}
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_nat_to_int(v_position_580_);
v___x_647_ = lean_int_add(v___x_646_, v_byteOffset_623_);
lean_dec(v___x_646_);
v___x_648_ = l_Int_toNat(v___x_647_);
lean_dec(v___x_647_);
v___y_602_ = v_byteOffset_623_;
v___y_603_ = v___x_648_;
goto v___jp_601_;
}
}
else
{
lean_object* v___x_649_; 
lean_del_object(v___x_588_);
lean_dec(v_tooltip_x3f_584_);
lean_dec_ref(v_textEdits_583_);
lean_dec(v_kind_x3f_582_);
lean_dec_ref(v_label_581_);
lean_dec(v_position_580_);
lean_dec_ref(v_range_578_);
v___x_649_ = lean_box(0);
return v___x_649_;
}
}
v___jp_650_:
{
if (v___y_652_ == 0)
{
v___y_616_ = v___y_651_;
goto v___jp_615_;
}
else
{
lean_object* v___x_653_; 
lean_del_object(v___x_588_);
lean_dec(v_tooltip_x3f_584_);
lean_dec_ref(v_textEdits_583_);
lean_dec(v_kind_x3f_582_);
lean_dec_ref(v_label_581_);
lean_dec(v_position_580_);
lean_dec_ref(v_range_578_);
v___x_653_ = lean_box(0);
return v___x_653_;
}
}
v___jp_654_:
{
uint8_t v___x_656_; uint8_t v___x_657_; 
v___x_656_ = 1;
v___x_657_ = l_Lean_Syntax_Range_contains(v_range_578_, v_position_580_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_unsigned_to_nat(0u);
v___x_659_ = lean_array_get_size(v_textEdits_583_);
v___x_660_ = lean_nat_dec_lt(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
v___y_616_ = v___y_655_;
goto v___jp_615_;
}
else
{
if (v___x_660_ == 0)
{
v___y_616_ = v___y_655_;
goto v___jp_615_;
}
else
{
size_t v___x_661_; size_t v___x_662_; uint8_t v___x_663_; 
v___x_661_ = ((size_t)0ULL);
v___x_662_ = lean_usize_of_nat(v___x_659_);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_578_, v___x_657_, v_textEdits_583_, v___x_661_, v___x_662_);
v___y_651_ = v___y_655_;
v___y_652_ = v___x_663_;
goto v___jp_650_;
}
}
}
else
{
v___y_651_ = v___y_655_;
v___y_652_ = v___x_657_;
goto v___jp_650_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___boxed(lean_object* v_hintMod_673_, lean_object* v_ihi_674_, lean_object* v_range_675_, lean_object* v_newText_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(v_hintMod_673_, v_ihi_674_, v_range_675_, v_newText_676_);
lean_dec_ref(v_newText_676_);
lean_dec(v_hintMod_673_);
return v_res_677_;
}
}
static lean_object* _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0(void){
_start:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_707_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_707_, 0, lean_box(0));
lean_closure_set(v___x_707_, 1, lean_box(0));
lean_closure_set(v___x_707_, 2, v___x_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(lean_object* v_msg_708_, lean_object* v___y_709_){
_start:
{
lean_object* v___x_711_; lean_object* v___f_712_; lean_object* v___x_14663__overap_713_; lean_object* v___x_714_; 
v___x_711_ = lean_obj_once(&l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0, &l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0_once, _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0);
v___f_712_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_712_, 0, v___x_711_);
v___x_14663__overap_713_ = lean_panic_fn_borrowed(v___f_712_, v_msg_708_);
lean_dec_ref(v___f_712_);
lean_inc_ref(v___y_709_);
v___x_714_ = lean_apply_2(v___x_14663__overap_713_, v___y_709_, lean_box(0));
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___boxed(lean_object* v_msg_715_, lean_object* v___y_716_, lean_object* v___y_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v_msg_715_, v___y_716_);
lean_dec_ref(v___y_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(uint8_t v___x_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_726_ = lean_box(v___x_719_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v___y_723_);
v___x_728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed(lean_object* v___x_729_, lean_object* v_x_730_, lean_object* v_x_731_, lean_object* v_x_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
uint8_t v___x_17626__boxed_736_; lean_object* v_res_737_; 
v___x_17626__boxed_736_ = lean_unbox(v___x_729_);
v_res_737_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(v___x_17626__boxed_736_, v_x_730_, v_x_731_, v_x_732_, v___y_733_, v___y_734_);
lean_dec_ref(v___y_734_);
lean_dec_ref(v_x_732_);
lean_dec_ref(v_x_731_);
lean_dec_ref(v_x_730_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(lean_object* v_ci_738_, lean_object* v_i_739_, lean_object* v_x_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
if (lean_obj_tag(v_i_739_) == 10)
{
lean_object* v_i_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_779_; 
v_i_744_ = lean_ctor_get(v_i_739_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v_i_739_);
if (v_isSharedCheck_779_ == 0)
{
v___x_746_ = v_i_739_;
v_isShared_747_ = v_isSharedCheck_779_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_i_744_);
lean_dec(v_i_739_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_779_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; 
v___x_748_ = l_Lean_Elab_InlayHint_ofCustomInfo_x3f(v_i_744_);
lean_dec_ref(v_i_744_);
if (lean_obj_tag(v___x_748_) == 1)
{
lean_object* v_val_749_; lean_object* v_lctx_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_del_object(v___x_746_);
v_val_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_val_749_);
lean_dec_ref_known(v___x_748_, 1);
v_lctx_750_ = lean_ctor_get(v_val_749_, 1);
lean_inc_ref(v_lctx_750_);
v___x_751_ = lean_alloc_closure((void*)(l_Lean_Elab_InlayHint_resolveDeferred___boxed), 6, 1);
lean_closure_set(v___x_751_, 0, v_val_749_);
v___x_752_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_738_, v_lctx_750_, v___x_751_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_764_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_764_ == 0)
{
v___x_755_ = v___x_752_;
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_752_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_toInlayHintInfo_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_762_; 
v_toInlayHintInfo_757_ = lean_ctor_get(v_a_753_, 0);
lean_inc_ref(v_toInlayHintInfo_757_);
lean_dec(v_a_753_);
v___x_758_ = lean_box(0);
v___x_759_ = lean_array_push(v___y_741_, v_toInlayHintInfo_757_);
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v___x_760_);
v___x_762_ = v___x_755_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v___y_741_);
v_a_765_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_773_ == 0)
{
v___x_767_ = v___x_752_;
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_752_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = l_Lean_Server_RequestError_ofIoError(v_a_765_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 0, v___x_769_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
else
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_777_; 
lean_dec(v___x_748_);
lean_dec_ref(v_ci_738_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___y_741_);
if (v_isShared_747_ == 0)
{
lean_ctor_set_tag(v___x_746_, 0);
lean_ctor_set(v___x_746_, 0, v___x_775_);
v___x_777_ = v___x_746_;
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
}
else
{
lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
lean_dec_ref(v_i_739_);
lean_dec_ref(v_ci_738_);
v___x_780_ = lean_box(0);
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v___x_780_);
lean_ctor_set(v___x_781_, 1, v___y_741_);
v___x_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_782_, 0, v___x_781_);
return v___x_782_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed(lean_object* v_ci_783_, lean_object* v_i_784_, lean_object* v_x_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(v_ci_783_, v_i_784_, v_x_785_, v___y_786_, v___y_787_);
lean_dec_ref(v___y_787_);
lean_dec_ref(v_x_785_);
return v_res_789_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_instMonadEIO___redArg();
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(lean_object* v_msg_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___f_797_; lean_object* v___f_798_; lean_object* v___f_799_; lean_object* v___f_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_17034__overap_809_; lean_object* v___x_810_; 
v___x_795_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_796_ = l_ReaderT_instMonad___redArg(v___x_795_);
lean_inc_ref_n(v___x_796_, 6);
v___f_797_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_797_, 0, v___x_796_);
v___f_798_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_798_, 0, v___x_796_);
v___f_799_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_799_, 0, v___x_796_);
v___f_800_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_800_, 0, v___x_796_);
v___x_801_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_801_, 0, lean_box(0));
lean_closure_set(v___x_801_, 1, lean_box(0));
lean_closure_set(v___x_801_, 2, v___x_796_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v___f_797_);
v___x_803_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_803_, 0, lean_box(0));
lean_closure_set(v___x_803_, 1, lean_box(0));
lean_closure_set(v___x_803_, 2, v___x_796_);
v___x_804_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_804_, 0, v___x_802_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
lean_ctor_set(v___x_804_, 2, v___f_798_);
lean_ctor_set(v___x_804_, 3, v___f_799_);
lean_ctor_set(v___x_804_, 4, v___f_800_);
v___x_805_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_805_, 0, lean_box(0));
lean_closure_set(v___x_805_, 1, lean_box(0));
lean_closure_set(v___x_805_, 2, v___x_796_);
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = lean_box(0);
v___x_808_ = l_instInhabitedOfMonad___redArg(v___x_806_, v___x_807_);
v___x_17034__overap_809_ = lean_panic_fn_borrowed(v___x_808_, v_msg_791_);
lean_dec(v___x_808_);
lean_inc_ref(v___y_793_);
v___x_810_ = lean_apply_3(v___x_17034__overap_809_, v___y_792_, v___y_793_, lean_box(0));
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_msg_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_811_, v___y_812_, v___y_813_);
lean_dec_ref(v___y_813_);
return v_res_815_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_819_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2));
v___x_820_ = lean_unsigned_to_nat(21u);
v___x_821_ = lean_unsigned_to_nat(65u);
v___x_822_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1));
v___x_823_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0));
v___x_824_ = l_mkPanicMessageWithDecl(v___x_823_, v___x_822_, v___x_821_, v___x_820_, v___x_819_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(lean_object* v_preNode_825_, lean_object* v_postNode_826_, lean_object* v_x_827_, lean_object* v_x_828_, lean_object* v___y_829_, lean_object* v___y_830_){
_start:
{
switch(lean_obj_tag(v_x_828_))
{
case 0:
{
lean_object* v_i_832_; lean_object* v_t_833_; lean_object* v___x_834_; 
v_i_832_ = lean_ctor_get(v_x_828_, 0);
lean_inc_ref(v_i_832_);
v_t_833_ = lean_ctor_get(v_x_828_, 1);
lean_inc_ref(v_t_833_);
lean_dec_ref_known(v_x_828_, 2);
v___x_834_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_832_, v_x_827_);
v_x_827_ = v___x_834_;
v_x_828_ = v_t_833_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_827_) == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; 
lean_dec_ref_known(v_x_828_, 2);
lean_dec_ref(v_postNode_826_);
lean_dec_ref(v_preNode_825_);
v___x_836_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3);
v___x_837_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v___x_836_, v___y_829_, v___y_830_);
return v___x_837_;
}
else
{
lean_object* v_i_838_; lean_object* v_children_839_; lean_object* v_val_840_; lean_object* v___x_841_; 
v_i_838_ = lean_ctor_get(v_x_828_, 0);
lean_inc_ref_n(v_i_838_, 2);
v_children_839_ = lean_ctor_get(v_x_828_, 1);
lean_inc_ref_n(v_children_839_, 2);
lean_dec_ref_known(v_x_828_, 2);
v_val_840_ = lean_ctor_get(v_x_827_, 0);
lean_inc_n(v_val_840_, 2);
lean_inc_ref(v_preNode_825_);
lean_inc_ref(v___y_830_);
v___x_841_ = lean_apply_6(v_preNode_825_, v_val_840_, v_i_838_, v_children_839_, v___y_829_, v___y_830_, lean_box(0));
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v_fst_843_; uint8_t v___x_844_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
v_fst_843_ = lean_ctor_get(v_a_842_, 0);
v___x_844_ = lean_unbox(v_fst_843_);
if (v___x_844_ == 0)
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_879_; 
lean_dec_ref(v_preNode_825_);
v_isSharedCheck_879_ = !lean_is_exclusive(v_x_827_);
if (v_isSharedCheck_879_ == 0)
{
lean_object* v_unused_880_; 
v_unused_880_ = lean_ctor_get(v_x_827_, 0);
lean_dec(v_unused_880_);
v___x_846_ = v_x_827_;
v_isShared_847_ = v_isSharedCheck_879_;
goto v_resetjp_845_;
}
else
{
lean_dec(v_x_827_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_879_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v_snd_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_snd_848_ = lean_ctor_get(v_a_842_, 1);
lean_inc(v_snd_848_);
lean_dec(v_a_842_);
v___x_849_ = lean_box(0);
lean_inc_ref(v___y_830_);
v___x_850_ = lean_apply_7(v_postNode_826_, v_val_840_, v_i_838_, v_children_839_, v___x_849_, v_snd_848_, v___y_830_, lean_box(0));
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_870_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_870_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_870_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_870_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v_fst_855_; lean_object* v_snd_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_869_; 
v_fst_855_ = lean_ctor_get(v_a_851_, 0);
v_snd_856_ = lean_ctor_get(v_a_851_, 1);
v_isSharedCheck_869_ = !lean_is_exclusive(v_a_851_);
if (v_isSharedCheck_869_ == 0)
{
v___x_858_ = v_a_851_;
v_isShared_859_ = v_isSharedCheck_869_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_snd_856_);
lean_inc(v_fst_855_);
lean_dec(v_a_851_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_869_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v_fst_855_);
v___x_861_ = v___x_846_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_fst_855_);
v___x_861_ = v_reuseFailAlloc_868_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_867_, 1, v_snd_856_);
v___x_863_ = v_reuseFailAlloc_867_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_865_; 
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_863_);
v___x_865_ = v___x_853_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
else
{
lean_object* v_a_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_878_; 
lean_del_object(v___x_846_);
v_a_871_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_878_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_878_ == 0)
{
v___x_873_ = v___x_850_;
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_a_871_);
lean_dec(v___x_850_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_878_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_877_; 
v_reuseFailAlloc_877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_877_, 0, v_a_871_);
v___x_876_ = v_reuseFailAlloc_877_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
return v___x_876_;
}
}
}
}
}
else
{
lean_object* v_snd_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_snd_881_ = lean_ctor_get(v_a_842_, 1);
lean_inc(v_snd_881_);
lean_dec(v_a_842_);
v___x_882_ = l_Lean_Elab_Info_updateContext_x3f(v_x_827_, v_i_838_);
v___x_883_ = l_Lean_PersistentArray_toList___redArg(v_children_839_);
v___x_884_ = lean_box(0);
lean_inc_ref(v_postNode_826_);
v___x_885_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_825_, v_postNode_826_, v___x_882_, v___x_883_, v___x_884_, v_snd_881_, v___y_830_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v_fst_887_; lean_object* v_snd_888_; lean_object* v___x_889_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v_fst_887_ = lean_ctor_get(v_a_886_, 0);
lean_inc(v_fst_887_);
v_snd_888_ = lean_ctor_get(v_a_886_, 1);
lean_inc(v_snd_888_);
lean_dec(v_a_886_);
lean_inc_ref(v___y_830_);
v___x_889_ = lean_apply_7(v_postNode_826_, v_val_840_, v_i_838_, v_children_839_, v_fst_887_, v_snd_888_, v___y_830_, lean_box(0));
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_907_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_907_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_907_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_907_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v_fst_894_; lean_object* v_snd_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_906_; 
v_fst_894_ = lean_ctor_get(v_a_890_, 0);
v_snd_895_ = lean_ctor_get(v_a_890_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_a_890_);
if (v_isSharedCheck_906_ == 0)
{
v___x_897_ = v_a_890_;
v_isShared_898_ = v_isSharedCheck_906_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_snd_895_);
lean_inc(v_fst_894_);
lean_dec(v_a_890_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_906_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; lean_object* v___x_901_; 
v___x_899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_899_, 0, v_fst_894_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 0, v___x_899_);
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_899_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_snd_895_);
v___x_901_ = v_reuseFailAlloc_905_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
lean_object* v___x_903_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_901_);
v___x_903_ = v___x_892_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
else
{
lean_object* v_a_908_; lean_object* v___x_910_; uint8_t v_isShared_911_; uint8_t v_isSharedCheck_915_; 
v_a_908_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_915_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_915_ == 0)
{
v___x_910_ = v___x_889_;
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
else
{
lean_inc(v_a_908_);
lean_dec(v___x_889_);
v___x_910_ = lean_box(0);
v_isShared_911_ = v_isSharedCheck_915_;
goto v_resetjp_909_;
}
v_resetjp_909_:
{
lean_object* v___x_913_; 
if (v_isShared_911_ == 0)
{
v___x_913_ = v___x_910_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_a_908_);
v___x_913_ = v_reuseFailAlloc_914_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
return v___x_913_;
}
}
}
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
lean_dec(v_val_840_);
lean_dec_ref(v_children_839_);
lean_dec_ref(v_i_838_);
lean_dec_ref(v_postNode_826_);
v_a_916_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_885_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_885_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_val_840_);
lean_dec_ref(v_children_839_);
lean_dec_ref(v_i_838_);
lean_dec_ref_known(v_x_827_, 1);
lean_dec_ref(v_postNode_826_);
lean_dec_ref(v_preNode_825_);
v_a_924_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_841_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_841_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
default: 
{
lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_x_827_);
lean_dec_ref(v_postNode_826_);
lean_dec_ref(v_preNode_825_);
v_isSharedCheck_940_ = !lean_is_exclusive(v_x_828_);
if (v_isSharedCheck_940_ == 0)
{
lean_object* v_unused_941_; 
v_unused_941_ = lean_ctor_get(v_x_828_, 0);
lean_dec(v_unused_941_);
v___x_933_ = v_x_828_;
v_isShared_934_ = v_isSharedCheck_940_;
goto v_resetjp_932_;
}
else
{
lean_dec(v_x_828_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_940_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_935_ = lean_box(0);
v___x_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v___y_829_);
if (v_isShared_934_ == 0)
{
lean_ctor_set_tag(v___x_933_, 0);
lean_ctor_set(v___x_933_, 0, v___x_936_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(lean_object* v_preNode_942_, lean_object* v_postNode_943_, lean_object* v___x_944_, lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
if (lean_obj_tag(v_x_945_) == 0)
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v___x_944_);
lean_dec_ref(v_postNode_943_);
lean_dec_ref(v_preNode_942_);
v___x_950_ = l_List_reverse___redArg(v_x_946_);
v___x_951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_951_, 0, v___x_950_);
lean_ctor_set(v___x_951_, 1, v___y_947_);
v___x_952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
return v___x_952_;
}
else
{
lean_object* v_head_953_; lean_object* v_tail_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_974_; 
v_head_953_ = lean_ctor_get(v_x_945_, 0);
v_tail_954_ = lean_ctor_get(v_x_945_, 1);
v_isSharedCheck_974_ = !lean_is_exclusive(v_x_945_);
if (v_isSharedCheck_974_ == 0)
{
v___x_956_ = v_x_945_;
v_isShared_957_ = v_isSharedCheck_974_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_tail_954_);
lean_inc(v_head_953_);
lean_dec(v_x_945_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_974_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_958_; 
lean_inc(v___x_944_);
lean_inc_ref(v_postNode_943_);
lean_inc_ref(v_preNode_942_);
v___x_958_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_942_, v_postNode_943_, v___x_944_, v_head_953_, v___y_947_, v___y_948_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v_fst_960_; lean_object* v_snd_961_; lean_object* v___x_963_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v_fst_960_ = lean_ctor_get(v_a_959_, 0);
lean_inc(v_fst_960_);
v_snd_961_ = lean_ctor_get(v_a_959_, 1);
lean_inc(v_snd_961_);
lean_dec(v_a_959_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v_x_946_);
lean_ctor_set(v___x_956_, 0, v_fst_960_);
v___x_963_ = v___x_956_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_fst_960_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_x_946_);
v___x_963_ = v_reuseFailAlloc_965_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
v_x_945_ = v_tail_954_;
v_x_946_ = v___x_963_;
v___y_947_ = v_snd_961_;
goto _start;
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_del_object(v___x_956_);
lean_dec(v_tail_954_);
lean_dec(v_x_946_);
lean_dec(v___x_944_);
lean_dec_ref(v_postNode_943_);
lean_dec_ref(v_preNode_942_);
v_a_966_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_958_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_958_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_preNode_975_, lean_object* v_postNode_976_, lean_object* v___x_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_975_, v_postNode_976_, v___x_977_, v_x_978_, v_x_979_, v___y_980_, v___y_981_);
lean_dec_ref(v___y_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___boxed(lean_object* v_preNode_984_, lean_object* v_postNode_985_, lean_object* v_x_986_, lean_object* v_x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_984_, v_postNode_985_, v_x_986_, v_x_987_, v___y_988_, v___y_989_);
lean_dec_ref(v___y_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(lean_object* v_postNode_992_, lean_object* v_ci_993_, lean_object* v_i_994_, lean_object* v_cs_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
lean_inc_ref(v___y_998_);
v___x_1000_ = lean_apply_6(v_postNode_992_, v_ci_993_, v_i_994_, v_cs_995_, v___y_997_, v___y_998_, lean_box(0));
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed(lean_object* v_postNode_1001_, lean_object* v_ci_1002_, lean_object* v_i_1003_, lean_object* v_cs_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(v_postNode_1001_, v_ci_1002_, v_i_1003_, v_cs_1004_, v_x_1005_, v___y_1006_, v___y_1007_);
lean_dec_ref(v___y_1007_);
lean_dec(v_x_1005_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(lean_object* v_preNode_1010_, lean_object* v_postNode_1011_, lean_object* v_ctx_x3f_1012_, lean_object* v_t_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v___f_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___f_1017_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1017_, 0, v_postNode_1011_);
v___x_1018_ = lean_box(0);
v___x_1019_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_1010_, v___f_1017_, v_ctx_x3f_1012_, v_t_1013_, v___y_1014_, v___y_1015_);
if (lean_obj_tag(v___x_1019_) == 0)
{
lean_object* v_a_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1036_; 
v_a_1020_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1022_ = v___x_1019_;
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_a_1020_);
lean_dec(v___x_1019_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1036_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v_snd_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1034_; 
v_snd_1024_ = lean_ctor_get(v_a_1020_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_a_1020_);
if (v_isSharedCheck_1034_ == 0)
{
lean_object* v_unused_1035_; 
v_unused_1035_ = lean_ctor_get(v_a_1020_, 0);
lean_dec(v_unused_1035_);
v___x_1026_ = v_a_1020_;
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_snd_1024_);
lean_dec(v_a_1020_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1034_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 0, v___x_1018_);
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_snd_1024_);
v___x_1029_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
lean_object* v___x_1031_; 
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 0, v___x_1029_);
v___x_1031_ = v___x_1022_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v___x_1029_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
v_a_1037_ = lean_ctor_get(v___x_1019_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1019_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_1019_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_1019_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___boxed(lean_object* v_preNode_1045_, lean_object* v_postNode_1046_, lean_object* v_ctx_x3f_1047_, lean_object* v_t_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
lean_object* v_res_1052_; 
v_res_1052_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v_preNode_1045_, v_postNode_1046_, v_ctx_x3f_1047_, v_t_1048_, v___y_1049_, v___y_1050_);
lean_dec_ref(v___y_1050_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(lean_object* v_a_1054_, lean_object* v_b_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v_array_1059_; lean_object* v_start_1060_; lean_object* v_stop_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1084_; 
v_array_1059_ = lean_ctor_get(v_a_1054_, 0);
v_start_1060_ = lean_ctor_get(v_a_1054_, 1);
v_stop_1061_ = lean_ctor_get(v_a_1054_, 2);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_a_1054_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1063_ = v_a_1054_;
v_isShared_1064_ = v_isSharedCheck_1084_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_stop_1061_);
lean_inc(v_start_1060_);
lean_inc(v_array_1059_);
lean_dec(v_a_1054_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1084_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
uint8_t v___x_1065_; 
v___x_1065_ = lean_nat_dec_lt(v_start_1060_, v_stop_1061_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_del_object(v___x_1063_);
lean_dec(v_stop_1061_);
lean_dec(v_start_1060_);
lean_dec_ref(v_array_1059_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v_b_1055_);
lean_ctor_set(v___x_1066_, 1, v___y_1056_);
v___x_1067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1067_, 0, v___x_1066_);
return v___x_1067_;
}
else
{
lean_object* v___f_1068_; lean_object* v___x_1069_; lean_object* v___f_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1075_; 
v___f_1068_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0));
v___x_1069_ = lean_box(v___x_1065_);
v___f_1070_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1070_, 0, v___x_1069_);
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_nat_add(v_start_1060_, v___x_1072_);
lean_inc_ref(v_array_1059_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 1, v___x_1073_);
v___x_1075_ = v___x_1063_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_array_1059_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v___x_1073_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_stop_1061_);
v___x_1075_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1076_ = lean_array_fget(v_array_1059_, v_start_1060_);
lean_dec(v_start_1060_);
lean_dec_ref(v_array_1059_);
v___x_1077_ = lean_box(0);
v___x_1078_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v___x_1076_);
v___x_1079_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v___f_1070_, v___f_1068_, v___x_1077_, v___x_1078_, v___y_1056_, v___y_1057_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v_snd_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
v_snd_1081_ = lean_ctor_get(v_a_1080_, 1);
lean_inc(v_snd_1081_);
lean_dec(v_a_1080_);
v_a_1054_ = v___x_1075_;
v_b_1055_ = v___x_1071_;
v___y_1056_ = v_snd_1081_;
goto _start;
}
else
{
lean_dec_ref(v___x_1075_);
return v___x_1079_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___boxed(lean_object* v_a_1085_, lean_object* v_b_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v_res_1090_; 
v_res_1090_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_1085_, v_b_1086_, v___y_1087_, v___y_1088_);
lean_dec_ref(v___y_1088_);
return v_res_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(lean_object* v___x_1091_, uint8_t v_val_1092_, lean_object* v_as_1093_, size_t v_i_1094_, size_t v_stop_1095_, lean_object* v_b_1096_){
_start:
{
lean_object* v___y_1098_; uint8_t v___x_1102_; 
v___x_1102_ = lean_usize_dec_eq(v_i_1094_, v_stop_1095_);
if (v___x_1102_ == 0)
{
lean_object* v___x_1103_; lean_object* v_position_1104_; uint8_t v___x_1105_; 
v___x_1103_ = lean_array_uget_borrowed(v_as_1093_, v_i_1094_);
v_position_1104_ = lean_ctor_get(v___x_1103_, 0);
v___x_1105_ = l_Lean_Syntax_Range_contains(v___x_1091_, v_position_1104_, v_val_1092_);
if (v___x_1105_ == 0)
{
lean_object* v___x_1106_; 
lean_inc(v___x_1103_);
v___x_1106_ = lean_array_push(v_b_1096_, v___x_1103_);
v___y_1098_ = v___x_1106_;
goto v___jp_1097_;
}
else
{
v___y_1098_ = v_b_1096_;
goto v___jp_1097_;
}
}
else
{
return v_b_1096_;
}
v___jp_1097_:
{
size_t v___x_1099_; size_t v___x_1100_; 
v___x_1099_ = ((size_t)1ULL);
v___x_1100_ = lean_usize_add(v_i_1094_, v___x_1099_);
v_i_1094_ = v___x_1100_;
v_b_1096_ = v___y_1098_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5___boxed(lean_object* v___x_1107_, lean_object* v_val_1108_, lean_object* v_as_1109_, lean_object* v_i_1110_, lean_object* v_stop_1111_, lean_object* v_b_1112_){
_start:
{
uint8_t v_val_18253__boxed_1113_; size_t v_i_boxed_1114_; size_t v_stop_boxed_1115_; lean_object* v_res_1116_; 
v_val_18253__boxed_1113_ = lean_unbox(v_val_1108_);
v_i_boxed_1114_ = lean_unbox_usize(v_i_1110_);
lean_dec(v_i_1110_);
v_stop_boxed_1115_ = lean_unbox_usize(v_stop_1111_);
lean_dec(v_stop_1111_);
v_res_1116_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1107_, v_val_18253__boxed_1113_, v_as_1109_, v_i_boxed_1114_, v_stop_boxed_1115_, v_b_1112_);
lean_dec_ref(v_as_1109_);
lean_dec_ref(v___x_1107_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(lean_object* v___x_1117_, lean_object* v_as_1118_, size_t v_i_1119_, size_t v_stop_1120_, lean_object* v_b_1121_){
_start:
{
lean_object* v___y_1123_; uint8_t v___x_1127_; 
v___x_1127_ = lean_usize_dec_eq(v_i_1119_, v_stop_1120_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v_position_1129_; uint8_t v___x_1130_; uint8_t v___x_1131_; 
v___x_1128_ = lean_array_uget_borrowed(v_as_1118_, v_i_1119_);
v_position_1129_ = lean_ctor_get(v___x_1128_, 0);
v___x_1130_ = 1;
v___x_1131_ = l_Lean_Syntax_Range_contains(v___x_1117_, v_position_1129_, v___x_1130_);
if (v___x_1131_ == 0)
{
v___y_1123_ = v_b_1121_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1132_; 
lean_inc(v___x_1128_);
v___x_1132_ = lean_array_push(v_b_1121_, v___x_1128_);
v___y_1123_ = v___x_1132_;
goto v___jp_1122_;
}
}
else
{
return v_b_1121_;
}
v___jp_1122_:
{
size_t v___x_1124_; size_t v___x_1125_; 
v___x_1124_ = ((size_t)1ULL);
v___x_1125_ = lean_usize_add(v_i_1119_, v___x_1124_);
v_i_1119_ = v___x_1125_;
v_b_1121_ = v___y_1123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___boxed(lean_object* v___x_1133_, lean_object* v_as_1134_, lean_object* v_i_1135_, lean_object* v_stop_1136_, lean_object* v_b_1137_){
_start:
{
size_t v_i_boxed_1138_; size_t v_stop_boxed_1139_; lean_object* v_res_1140_; 
v_i_boxed_1138_ = lean_unbox_usize(v_i_1135_);
lean_dec(v_i_1135_);
v_stop_boxed_1139_ = lean_unbox_usize(v_stop_1136_);
lean_dec(v_stop_1136_);
v_res_1140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1133_, v_as_1134_, v_i_boxed_1138_, v_stop_boxed_1139_, v_b_1137_);
lean_dec_ref(v_as_1134_);
lean_dec_ref(v___x_1133_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(lean_object* v___x_1141_, size_t v_sz_1142_, size_t v_i_1143_, lean_object* v_bs_1144_){
_start:
{
uint8_t v___x_1146_; 
v___x_1146_ = lean_usize_dec_lt(v_i_1143_, v_sz_1142_);
if (v___x_1146_ == 0)
{
lean_object* v___x_1147_; 
lean_dec_ref(v___x_1141_);
v___x_1147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_bs_1144_);
return v___x_1147_;
}
else
{
lean_object* v_v_1148_; lean_object* v___x_1149_; lean_object* v_bs_x27_1150_; lean_object* v___x_1151_; 
v_v_1148_ = lean_array_uget(v_bs_1144_, v_i_1143_);
v___x_1149_ = lean_unsigned_to_nat(0u);
v_bs_x27_1150_ = lean_array_uset(v_bs_1144_, v_i_1143_, v___x_1149_);
lean_inc_ref(v___x_1141_);
v___x_1151_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v___x_1141_, v_v_1148_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; size_t v___x_1153_; size_t v___x_1154_; lean_object* v___x_1155_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
lean_inc(v_a_1152_);
lean_dec_ref_known(v___x_1151_, 1);
v___x_1153_ = ((size_t)1ULL);
v___x_1154_ = lean_usize_add(v_i_1143_, v___x_1153_);
v___x_1155_ = lean_array_uset(v_bs_x27_1150_, v_i_1143_, v_a_1152_);
v_i_1143_ = v___x_1154_;
v_bs_1144_ = v___x_1155_;
goto _start;
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
lean_dec_ref(v_bs_x27_1150_);
lean_dec_ref(v___x_1141_);
v_a_1157_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1159_ = v___x_1151_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1151_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_Server_RequestError_ofIoError(v_a_1157_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg___boxed(lean_object* v___x_1166_, lean_object* v_sz_1167_, lean_object* v_i_1168_, lean_object* v_bs_1169_, lean_object* v___y_1170_){
_start:
{
size_t v_sz_boxed_1171_; size_t v_i_boxed_1172_; lean_object* v_res_1173_; 
v_sz_boxed_1171_ = lean_unbox_usize(v_sz_1167_);
lean_dec(v_sz_1167_);
v_i_boxed_1172_ = lean_unbox_usize(v_i_1168_);
lean_dec(v_i_1168_);
v_res_1173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_1166_, v_sz_boxed_1171_, v_i_boxed_1172_, v_bs_1169_);
return v_res_1173_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2(void){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1176_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__1));
v___x_1177_ = lean_unsigned_to_nat(2u);
v___x_1178_ = lean_unsigned_to_nat(162u);
v___x_1179_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__0));
v___x_1180_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_1181_ = l_mkPanicMessageWithDecl(v___x_1180_, v___x_1179_, v___x_1178_, v___x_1177_, v___x_1176_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints(lean_object* v_p_1182_, lean_object* v_s_1183_, lean_object* v_a_1184_){
_start:
{
lean_object* v_doc_1186_; lean_object* v_toEditableDocumentCore_1187_; lean_object* v_meta_1188_; lean_object* v_cancelTk_1189_; lean_object* v_cmdSnaps_1190_; lean_object* v_text_1191_; lean_object* v_oldInlayHints_1192_; lean_object* v_oldFinishedSnaps_1193_; lean_object* v_lastEditTimestamp_x3f_1194_; uint8_t v_isFirstRequestAfterEdit_1195_; lean_object* v___y_1197_; lean_object* v___y_1198_; uint8_t v___y_1199_; lean_object* v___y_1200_; 
v_doc_1186_ = lean_ctor_get(v_a_1184_, 1);
v_toEditableDocumentCore_1187_ = lean_ctor_get(v_doc_1186_, 0);
v_meta_1188_ = lean_ctor_get(v_toEditableDocumentCore_1187_, 0);
v_cancelTk_1189_ = lean_ctor_get(v_a_1184_, 4);
v_cmdSnaps_1190_ = lean_ctor_get(v_toEditableDocumentCore_1187_, 2);
v_text_1191_ = lean_ctor_get(v_meta_1188_, 3);
v_oldInlayHints_1192_ = lean_ctor_get(v_s_1183_, 0);
v_oldFinishedSnaps_1193_ = lean_ctor_get(v_s_1183_, 1);
v_lastEditTimestamp_x3f_1194_ = lean_ctor_get(v_s_1183_, 2);
v_isFirstRequestAfterEdit_1195_ = lean_ctor_get_uint8(v_s_1183_, sizeof(void*)*3);
if (v_isFirstRequestAfterEdit_1195_ == 0)
{
lean_object* v_range_1223_; lean_object* v___x_1224_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v_snd_1230_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; uint8_t v___y_1246_; lean_object* v___y_1247_; lean_object* v_lower_1248_; lean_object* v_upper_1249_; lean_object* v___y_1267_; lean_object* v___y_1268_; uint8_t v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; uint8_t v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; uint8_t v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; uint8_t v___y_1293_; lean_object* v___y_1294_; uint8_t v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___y_1307_; 
v_range_1223_ = lean_ctor_get(v_p_1182_, 2);
lean_inc_ref(v_range_1223_);
lean_dec_ref(v_p_1182_);
v___x_1224_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_1191_, v_range_1223_);
v___x_1304_ = lean_unsigned_to_nat(3000u);
v___x_1305_ = lean_io_mono_ms_now();
if (lean_obj_tag(v_lastEditTimestamp_x3f_1194_) == 0)
{
lean_object* v___x_1356_; 
lean_dec(v___x_1305_);
v___x_1356_ = lean_unsigned_to_nat(0u);
v___y_1307_ = v___x_1356_;
goto v___jp_1306_;
}
else
{
lean_object* v_val_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v_val_1357_ = lean_ctor_get(v_lastEditTimestamp_x3f_1194_, 0);
v___x_1358_ = lean_nat_sub(v___x_1305_, v_val_1357_);
lean_dec(v___x_1305_);
v___x_1359_ = lean_nat_sub(v___x_1304_, v___x_1358_);
lean_dec(v___x_1358_);
v___y_1307_ = v___x_1359_;
goto v___jp_1306_;
}
v___jp_1225_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v___x_1231_ = l_Array_append___redArg(v_snd_1230_, v___y_1228_);
lean_dec_ref(v___y_1228_);
v___x_1232_ = lean_array_get_size(v___x_1231_);
v___x_1233_ = lean_mk_empty_array_with_capacity(v___y_1226_);
v___x_1234_ = lean_nat_dec_lt(v___y_1226_, v___x_1232_);
lean_dec(v___y_1226_);
if (v___x_1234_ == 0)
{
lean_dec_ref(v___x_1224_);
v___y_1197_ = v___x_1231_;
v___y_1198_ = v___y_1227_;
v___y_1199_ = v___y_1229_;
v___y_1200_ = v___x_1233_;
goto v___jp_1196_;
}
else
{
uint8_t v___x_1235_; 
v___x_1235_ = lean_nat_dec_le(v___x_1232_, v___x_1232_);
if (v___x_1235_ == 0)
{
if (v___x_1234_ == 0)
{
lean_dec_ref(v___x_1224_);
v___y_1197_ = v___x_1231_;
v___y_1198_ = v___y_1227_;
v___y_1199_ = v___y_1229_;
v___y_1200_ = v___x_1233_;
goto v___jp_1196_;
}
else
{
size_t v___x_1236_; size_t v___x_1237_; lean_object* v___x_1238_; 
v___x_1236_ = ((size_t)0ULL);
v___x_1237_ = lean_usize_of_nat(v___x_1232_);
v___x_1238_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1224_, v___x_1231_, v___x_1236_, v___x_1237_, v___x_1233_);
lean_dec_ref(v___x_1224_);
v___y_1197_ = v___x_1231_;
v___y_1198_ = v___y_1227_;
v___y_1199_ = v___y_1229_;
v___y_1200_ = v___x_1238_;
goto v___jp_1196_;
}
}
else
{
size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = lean_usize_of_nat(v___x_1232_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1224_, v___x_1231_, v___x_1239_, v___x_1240_, v___x_1233_);
lean_dec_ref(v___x_1224_);
v___y_1197_ = v___x_1231_;
v___y_1198_ = v___y_1227_;
v___y_1199_ = v___y_1229_;
v___y_1200_ = v___x_1241_;
goto v___jp_1196_;
}
}
}
v___jp_1242_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1250_ = l_Array_toSubarray___redArg(v___y_1247_, v_lower_1248_, v_upper_1249_);
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_mk_empty_array_with_capacity(v___y_1243_);
v___x_1253_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v___x_1250_, v___x_1251_, v___x_1252_, v_a_1184_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v_snd_1255_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v_snd_1255_ = lean_ctor_get(v_a_1254_, 1);
lean_inc(v_snd_1255_);
lean_dec(v_a_1254_);
v___y_1226_ = v___y_1243_;
v___y_1227_ = v___y_1244_;
v___y_1228_ = v___y_1245_;
v___y_1229_ = v___y_1246_;
v_snd_1230_ = v_snd_1255_;
goto v___jp_1225_;
}
else
{
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1256_; lean_object* v_snd_1257_; 
v_a_1256_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1256_);
lean_dec_ref_known(v___x_1253_, 1);
v_snd_1257_ = lean_ctor_get(v_a_1256_, 1);
lean_inc(v_snd_1257_);
lean_dec(v_a_1256_);
v___y_1226_ = v___y_1243_;
v___y_1227_ = v___y_1244_;
v___y_1228_ = v___y_1245_;
v___y_1229_ = v___y_1246_;
v_snd_1230_ = v_snd_1257_;
goto v___jp_1225_;
}
else
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1265_; 
lean_dec_ref(v___y_1245_);
lean_dec(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___x_1224_);
lean_dec(v_lastEditTimestamp_x3f_1194_);
v_a_1258_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1260_ = v___x_1253_;
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1253_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1265_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1263_; 
if (v_isShared_1261_ == 0)
{
v___x_1263_ = v___x_1260_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1258_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
}
v___jp_1266_:
{
uint8_t v___x_1272_; 
v___x_1272_ = lean_nat_dec_le(v_oldFinishedSnaps_1193_, v___y_1267_);
if (v___x_1272_ == 0)
{
lean_inc(v___y_1268_);
v___y_1243_ = v___y_1267_;
v___y_1244_ = v___y_1268_;
v___y_1245_ = v___y_1271_;
v___y_1246_ = v___y_1269_;
v___y_1247_ = v___y_1270_;
v_lower_1248_ = v_oldFinishedSnaps_1193_;
v_upper_1249_ = v___y_1268_;
goto v___jp_1242_;
}
else
{
lean_dec(v_oldFinishedSnaps_1193_);
lean_inc(v___y_1268_);
lean_inc(v___y_1267_);
v___y_1243_ = v___y_1267_;
v___y_1244_ = v___y_1268_;
v___y_1245_ = v___y_1271_;
v___y_1246_ = v___y_1269_;
v___y_1247_ = v___y_1270_;
v_lower_1248_ = v___y_1267_;
v_upper_1249_ = v___y_1268_;
goto v___jp_1242_;
}
}
v___jp_1273_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_array_get_size(v_oldInlayHints_1192_);
v___x_1282_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init___closed__0));
v___x_1283_ = lean_nat_dec_lt(v___x_1280_, v___x_1281_);
if (v___x_1283_ == 0)
{
lean_dec(v___y_1279_);
lean_dec(v___y_1276_);
lean_dec_ref(v_oldInlayHints_1192_);
v___y_1267_ = v___x_1280_;
v___y_1268_ = v___y_1275_;
v___y_1269_ = v___y_1277_;
v___y_1270_ = v___y_1278_;
v___y_1271_ = v___x_1282_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___y_1276_);
lean_ctor_set(v___x_1284_, 1, v___y_1279_);
v___x_1285_ = lean_nat_dec_le(v___x_1281_, v___x_1281_);
if (v___x_1285_ == 0)
{
if (v___x_1283_ == 0)
{
lean_dec_ref_known(v___x_1284_, 2);
lean_dec_ref(v_oldInlayHints_1192_);
v___y_1267_ = v___x_1280_;
v___y_1268_ = v___y_1275_;
v___y_1269_ = v___y_1277_;
v___y_1270_ = v___y_1278_;
v___y_1271_ = v___x_1282_;
goto v___jp_1266_;
}
else
{
size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = lean_usize_of_nat(v___x_1281_);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1284_, v___y_1274_, v_oldInlayHints_1192_, v___x_1286_, v___x_1287_, v___x_1282_);
lean_dec_ref(v_oldInlayHints_1192_);
lean_dec_ref_known(v___x_1284_, 2);
v___y_1267_ = v___x_1280_;
v___y_1268_ = v___y_1275_;
v___y_1269_ = v___y_1277_;
v___y_1270_ = v___y_1278_;
v___y_1271_ = v___x_1288_;
goto v___jp_1266_;
}
}
else
{
size_t v___x_1289_; size_t v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = ((size_t)0ULL);
v___x_1290_ = lean_usize_of_nat(v___x_1281_);
v___x_1291_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1284_, v___y_1274_, v_oldInlayHints_1192_, v___x_1289_, v___x_1290_, v___x_1282_);
lean_dec_ref(v_oldInlayHints_1192_);
lean_dec_ref_known(v___x_1284_, 2);
v___y_1267_ = v___x_1280_;
v___y_1268_ = v___y_1275_;
v___y_1269_ = v___y_1277_;
v___y_1270_ = v___y_1278_;
v___y_1271_ = v___x_1291_;
goto v___jp_1266_;
}
}
}
v___jp_1292_:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = lean_nat_sub(v___y_1294_, v___y_1296_);
v___x_1300_ = lean_nat_dec_lt(v___x_1299_, v___y_1294_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; 
lean_dec(v___x_1299_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___y_1274_ = v___y_1293_;
v___y_1275_ = v___y_1294_;
v___y_1276_ = v___y_1298_;
v___y_1277_ = v___y_1295_;
v___y_1278_ = v___y_1297_;
v___y_1279_ = v___x_1301_;
goto v___jp_1273_;
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = lean_array_fget_borrowed(v___y_1297_, v___x_1299_);
lean_dec(v___x_1299_);
v___x_1303_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1302_);
v___y_1274_ = v___y_1293_;
v___y_1275_ = v___y_1294_;
v___y_1276_ = v___y_1298_;
v___y_1277_ = v___y_1295_;
v___y_1278_ = v___y_1297_;
v___y_1279_ = v___x_1303_;
goto v___jp_1273_;
}
}
v___jp_1306_:
{
uint32_t v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v_snd_1311_; lean_object* v_fst_1312_; lean_object* v_snd_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1354_; 
v___x_1308_ = lean_uint32_of_nat(v___y_1307_);
lean_dec(v___y_1307_);
v___x_1309_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_1189_);
lean_inc(v_cmdSnaps_1190_);
v___x_1310_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_cmdSnaps_1190_, v___x_1308_, v___x_1309_);
v_snd_1311_ = lean_ctor_get(v___x_1310_, 1);
lean_inc(v_snd_1311_);
v_fst_1312_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_fst_1312_);
lean_dec_ref(v___x_1310_);
v_snd_1313_ = lean_ctor_get(v_snd_1311_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_snd_1311_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v_snd_1311_, 0);
lean_dec(v_unused_1355_);
v___x_1315_ = v_snd_1311_;
v_isShared_1316_ = v_isSharedCheck_1354_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_snd_1313_);
lean_dec(v_snd_1311_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1354_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
uint8_t v___x_1317_; 
v___x_1317_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_cancelTk_1189_);
if (v___x_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
lean_inc(v_lastEditTimestamp_x3f_1194_);
lean_inc(v_oldFinishedSnaps_1193_);
lean_inc_ref(v_oldInlayHints_1192_);
lean_del_object(v___x_1315_);
lean_dec_ref(v_s_1183_);
v___x_1318_ = lean_array_mk(v_fst_1312_);
v___x_1319_ = lean_array_get_size(v___x_1318_);
v___x_1320_ = lean_nat_dec_le(v_oldFinishedSnaps_1193_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; lean_object* v___x_1322_; 
lean_dec_ref(v___x_1318_);
lean_dec(v_snd_1313_);
lean_dec_ref(v___x_1224_);
lean_dec(v_lastEditTimestamp_x3f_1194_);
lean_dec(v_oldFinishedSnaps_1193_);
lean_dec_ref(v_oldInlayHints_1192_);
v___x_1321_ = lean_obj_once(&l_Lean_Server_FileWorker_handleInlayHints___closed__2, &l_Lean_Server_FileWorker_handleInlayHints___closed__2_once, _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2);
v___x_1322_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v___x_1321_, v_a_1184_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1323_ = lean_unsigned_to_nat(1u);
v___x_1324_ = lean_nat_sub(v_oldFinishedSnaps_1193_, v___x_1323_);
v___x_1325_ = lean_nat_dec_lt(v___x_1324_, v___x_1319_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
lean_dec(v___x_1324_);
v___x_1326_ = lean_unsigned_to_nat(0u);
v___x_1327_ = lean_unbox(v_snd_1313_);
lean_dec(v_snd_1313_);
v___y_1293_ = v___x_1317_;
v___y_1294_ = v___x_1319_;
v___y_1295_ = v___x_1327_;
v___y_1296_ = v___x_1323_;
v___y_1297_ = v___x_1318_;
v___y_1298_ = v___x_1326_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1328_; lean_object* v___x_1329_; uint8_t v___x_1330_; 
v___x_1328_ = lean_array_fget(v___x_1318_, v___x_1324_);
lean_dec(v___x_1324_);
v___x_1329_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1328_);
lean_dec(v___x_1328_);
v___x_1330_ = lean_unbox(v_snd_1313_);
lean_dec(v_snd_1313_);
v___y_1293_ = v___x_1317_;
v___y_1294_ = v___x_1319_;
v___y_1295_ = v___x_1330_;
v___y_1296_ = v___x_1323_;
v___y_1297_ = v___x_1318_;
v___y_1298_ = v___x_1329_;
goto v___jp_1292_;
}
}
}
else
{
size_t v_sz_1331_; size_t v___x_1332_; lean_object* v___x_1333_; 
lean_dec(v_snd_1313_);
lean_dec(v_fst_1312_);
lean_dec_ref(v___x_1224_);
v_sz_1331_ = lean_array_size(v_oldInlayHints_1192_);
v___x_1332_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1192_);
lean_inc_ref(v_text_1191_);
v___x_1333_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1191_, v_sz_1331_, v___x_1332_, v_oldInlayHints_1192_);
if (lean_obj_tag(v___x_1333_) == 0)
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1345_; 
v_a_1334_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1336_ = v___x_1333_;
v_isShared_1337_ = v_isSharedCheck_1345_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1333_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1345_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___x_1340_; 
v___x_1338_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1338_, 0, v_a_1334_);
lean_ctor_set_uint8(v___x_1338_, sizeof(void*)*1, v_isFirstRequestAfterEdit_1195_);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 1, v_s_1183_);
lean_ctor_set(v___x_1315_, 0, v___x_1338_);
v___x_1340_ = v___x_1315_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1344_, 1, v_s_1183_);
v___x_1340_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
lean_object* v___x_1342_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v___x_1340_);
v___x_1342_ = v___x_1336_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v___x_1340_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_del_object(v___x_1315_);
lean_dec_ref(v_s_1183_);
v_a_1346_ = lean_ctor_get(v___x_1333_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1333_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1333_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1388_; 
lean_inc(v_lastEditTimestamp_x3f_1194_);
lean_inc(v_oldFinishedSnaps_1193_);
lean_inc_ref(v_oldInlayHints_1192_);
lean_dec_ref(v_p_1182_);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_s_1183_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; lean_object* v_unused_1390_; lean_object* v_unused_1391_; 
v_unused_1389_ = lean_ctor_get(v_s_1183_, 2);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v_s_1183_, 1);
lean_dec(v_unused_1390_);
v_unused_1391_ = lean_ctor_get(v_s_1183_, 0);
lean_dec(v_unused_1391_);
v___x_1361_ = v_s_1183_;
v_isShared_1362_ = v_isSharedCheck_1388_;
goto v_resetjp_1360_;
}
else
{
lean_dec(v_s_1183_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1388_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
size_t v_sz_1363_; size_t v___x_1364_; lean_object* v___x_1365_; 
v_sz_1363_ = lean_array_size(v_oldInlayHints_1192_);
v___x_1364_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1192_);
lean_inc_ref(v_text_1191_);
v___x_1365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1191_, v_sz_1363_, v___x_1364_, v_oldInlayHints_1192_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1379_; 
v_a_1366_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1368_ = v___x_1365_;
v_isShared_1369_ = v_isSharedCheck_1379_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1365_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1379_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
uint8_t v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1373_; 
v___x_1370_ = 0;
v___x_1371_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1371_, 0, v_a_1366_);
lean_ctor_set_uint8(v___x_1371_, sizeof(void*)*1, v___x_1370_);
if (v_isShared_1362_ == 0)
{
v___x_1373_ = v___x_1361_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_oldInlayHints_1192_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v_oldFinishedSnaps_1193_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_lastEditTimestamp_x3f_1194_);
v___x_1373_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3, v___x_1370_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1371_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1374_);
v___x_1376_ = v___x_1368_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1374_);
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
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_del_object(v___x_1361_);
lean_dec(v_lastEditTimestamp_x3f_1194_);
lean_dec(v_oldFinishedSnaps_1193_);
lean_dec_ref(v_oldInlayHints_1192_);
v_a_1380_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1365_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1365_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
}
v___jp_1196_:
{
size_t v_sz_1201_; size_t v___x_1202_; lean_object* v___x_1203_; 
v_sz_1201_ = lean_array_size(v___y_1200_);
v___x_1202_ = ((size_t)0ULL);
lean_inc_ref(v_text_1191_);
v___x_1203_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1191_, v_sz_1201_, v___x_1202_, v___y_1200_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1214_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1206_ = v___x_1203_;
v_isShared_1207_ = v_isSharedCheck_1214_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1203_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1214_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1208_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1208_, 0, v_a_1204_);
lean_ctor_set_uint8(v___x_1208_, sizeof(void*)*1, v___y_1199_);
v___x_1209_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1209_, 0, v___y_1197_);
lean_ctor_set(v___x_1209_, 1, v___y_1198_);
lean_ctor_set(v___x_1209_, 2, v_lastEditTimestamp_x3f_1194_);
lean_ctor_set_uint8(v___x_1209_, sizeof(void*)*3, v_isFirstRequestAfterEdit_1195_);
v___x_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
if (v_isShared_1207_ == 0)
{
lean_ctor_set(v___x_1206_, 0, v___x_1210_);
v___x_1212_ = v___x_1206_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v_lastEditTimestamp_x3f_1194_);
v_a_1215_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1203_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1203_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints___boxed(lean_object* v_p_1392_, lean_object* v_s_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Server_FileWorker_handleInlayHints(v_p_1392_, v_s_1393_, v_a_1394_);
lean_dec_ref(v_a_1394_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(lean_object* v___x_1397_, size_t v_sz_1398_, size_t v_i_1399_, lean_object* v_bs_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_1397_, v_sz_1398_, v_i_1399_, v_bs_1400_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___boxed(lean_object* v___x_1404_, lean_object* v_sz_1405_, lean_object* v_i_1406_, lean_object* v_bs_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
size_t v_sz_boxed_1410_; size_t v_i_boxed_1411_; lean_object* v_res_1412_; 
v_sz_boxed_1410_ = lean_unbox_usize(v_sz_1405_);
lean_dec(v_sz_1405_);
v_i_boxed_1411_ = lean_unbox_usize(v_i_1406_);
lean_dec(v_i_1406_);
v_res_1412_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(v___x_1404_, v_sz_boxed_1410_, v_i_boxed_1411_, v_bs_1407_, v___y_1408_);
lean_dec_ref(v___y_1408_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(lean_object* v_inst_1413_, lean_object* v_R_1414_, lean_object* v_a_1415_, lean_object* v_b_1416_, lean_object* v_c_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_1415_, v_b_1416_, v___y_1418_, v___y_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___boxed(lean_object* v_inst_1422_, lean_object* v_R_1423_, lean_object* v_a_1424_, lean_object* v_b_1425_, lean_object* v_c_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_res_1430_; 
v_res_1430_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(v_inst_1422_, v_R_1423_, v_a_1424_, v_b_1425_, v_c_1426_, v___y_1427_, v___y_1428_);
lean_dec_ref(v___y_1428_);
return v_res_1430_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_1431_, lean_object* v_msg_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_1432_, v___y_1433_, v___y_1434_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_msg_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(v_00_u03b1_1437_, v_msg_1438_, v___y_1439_, v___y_1440_);
lean_dec_ref(v___y_1440_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(lean_object* v_00_u03b1_1443_, lean_object* v_preNode_1444_, lean_object* v_postNode_1445_, lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_1444_, v_postNode_1445_, v_x_1446_, v_x_1447_, v___y_1448_, v___y_1449_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1452_, lean_object* v_preNode_1453_, lean_object* v_postNode_1454_, lean_object* v_x_1455_, lean_object* v_x_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(v_00_u03b1_1452_, v_preNode_1453_, v_postNode_1454_, v_x_1455_, v_x_1456_, v___y_1457_, v___y_1458_);
lean_dec_ref(v___y_1458_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(lean_object* v_00_u03b1_1461_, lean_object* v_preNode_1462_, lean_object* v_postNode_1463_, lean_object* v___x_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_1462_, v_postNode_1463_, v___x_1464_, v_x_1465_, v_x_1466_, v___y_1467_, v___y_1468_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1471_, lean_object* v_preNode_1472_, lean_object* v_postNode_1473_, lean_object* v___x_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(v_00_u03b1_1471_, v_preNode_1472_, v_postNode_1473_, v___x_1474_, v_x_1475_, v_x_1476_, v___y_1477_, v___y_1478_);
lean_dec_ref(v___y_1478_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(lean_object* v___x_1483_, lean_object* v___x_1484_, lean_object* v_as_1485_, size_t v_sz_1486_, size_t v_i_1487_, lean_object* v_b_1488_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1487_, v_sz_1486_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_b_1488_);
return v___x_1491_;
}
else
{
lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1535_; 
v_snd_1492_ = lean_ctor_get(v_b_1488_, 1);
v_isSharedCheck_1535_ = !lean_is_exclusive(v_b_1488_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v_b_1488_, 0);
lean_dec(v_unused_1536_);
v___x_1494_ = v_b_1488_;
v_isShared_1495_ = v_isSharedCheck_1535_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_dec(v_b_1488_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1535_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_fst_1496_; lean_object* v_snd_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1534_; 
v_fst_1496_ = lean_ctor_get(v_snd_1492_, 0);
v_snd_1497_ = lean_ctor_get(v_snd_1492_, 1);
v_isSharedCheck_1534_ = !lean_is_exclusive(v_snd_1492_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1499_ = v_snd_1492_;
v_isShared_1500_ = v_isSharedCheck_1534_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_snd_1497_);
lean_inc(v_fst_1496_);
lean_dec(v_snd_1492_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1534_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v_a_1501_; 
v_a_1501_ = lean_array_uget_borrowed(v_as_1485_, v_i_1487_);
if (lean_obj_tag(v_a_1501_) == 0)
{
lean_object* v_range_1502_; lean_object* v_text_1503_; lean_object* v_mod_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v_range_1502_ = lean_ctor_get(v_a_1501_, 0);
v_text_1503_ = lean_ctor_get(v_a_1501_, 1);
v_mod_1504_ = lean_ctor_get(v___x_1484_, 1);
v___x_1505_ = lean_box(0);
lean_inc_ref(v_range_1502_);
v___x_1506_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1483_, v_range_1502_);
lean_inc(v_fst_1496_);
v___x_1507_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(v_mod_1504_, v_fst_1496_, v___x_1506_, v_text_1503_);
if (lean_obj_tag(v___x_1507_) == 1)
{
lean_object* v_val_1508_; lean_object* v___x_1510_; 
lean_dec(v_fst_1496_);
v_val_1508_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_val_1508_);
lean_dec_ref_known(v___x_1507_, 1);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 0, v_val_1508_);
v___x_1510_ = v___x_1499_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_val_1508_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v_snd_1497_);
v___x_1510_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
lean_object* v___x_1512_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1510_);
lean_ctor_set(v___x_1494_, 0, v___x_1505_);
v___x_1512_ = v___x_1494_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
size_t v___x_1513_; size_t v___x_1514_; 
v___x_1513_ = ((size_t)1ULL);
v___x_1514_ = lean_usize_add(v_i_1487_, v___x_1513_);
v_i_1487_ = v___x_1514_;
v_b_1488_ = v___x_1512_;
goto _start;
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
lean_dec(v___x_1507_);
lean_dec(v_snd_1497_);
v___x_1518_ = lean_box(v___x_1490_);
if (v_isShared_1500_ == 0)
{
lean_ctor_set(v___x_1499_, 1, v___x_1518_);
v___x_1520_ = v___x_1499_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_fst_1496_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___x_1518_);
v___x_1520_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1520_);
lean_ctor_set(v___x_1494_, 0, v___x_1505_);
v___x_1522_ = v___x_1494_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1505_);
lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1520_);
v___x_1522_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1521_;
}
v_reusejp_1521_:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
}
}
else
{
lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0));
if (v_isShared_1500_ == 0)
{
v___x_1528_ = v___x_1499_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_fst_1496_);
lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_snd_1497_);
v___x_1528_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1530_; 
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1528_);
lean_ctor_set(v___x_1494_, 0, v___x_1526_);
v___x_1530_ = v___x_1494_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1532_, 1, v___x_1528_);
v___x_1530_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
return v___x_1531_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___boxed(lean_object* v___x_1537_, lean_object* v___x_1538_, lean_object* v_as_1539_, lean_object* v_sz_1540_, lean_object* v_i_1541_, lean_object* v_b_1542_, lean_object* v___y_1543_){
_start:
{
size_t v_sz_boxed_1544_; size_t v_i_boxed_1545_; lean_object* v_res_1546_; 
v_sz_boxed_1544_ = lean_unbox_usize(v_sz_1540_);
lean_dec(v_sz_1540_);
v_i_boxed_1545_ = lean_unbox_usize(v_i_1541_);
lean_dec(v_i_1541_);
v_res_1546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1537_, v___x_1538_, v_as_1539_, v_sz_boxed_1544_, v_i_boxed_1545_, v_b_1542_);
lean_dec_ref(v_as_1539_);
lean_dec_ref(v___x_1538_);
lean_dec_ref(v___x_1537_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(lean_object* v_p_1547_, lean_object* v___x_1548_, lean_object* v___x_1549_, lean_object* v_as_1550_, size_t v_sz_1551_, size_t v_i_1552_, lean_object* v_b_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_a_1557_; uint8_t v___x_1561_; 
v___x_1561_ = lean_usize_dec_lt(v_i_1552_, v_sz_1551_);
if (v___x_1561_ == 0)
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v_b_1553_);
return v___x_1562_;
}
else
{
lean_object* v_snd_1563_; lean_object* v___x_1565_; uint8_t v_isShared_1566_; uint8_t v_isSharedCheck_1627_; 
v_snd_1563_ = lean_ctor_get(v_b_1553_, 1);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_b_1553_);
if (v_isSharedCheck_1627_ == 0)
{
lean_object* v_unused_1628_; 
v_unused_1628_ = lean_ctor_get(v_b_1553_, 0);
lean_dec(v_unused_1628_);
v___x_1565_ = v_b_1553_;
v_isShared_1566_ = v_isSharedCheck_1627_;
goto v_resetjp_1564_;
}
else
{
lean_inc(v_snd_1563_);
lean_dec(v_b_1553_);
v___x_1565_ = lean_box(0);
v_isShared_1566_ = v_isSharedCheck_1627_;
goto v_resetjp_1564_;
}
v_resetjp_1564_:
{
lean_object* v_contentChanges_1567_; lean_object* v___x_1568_; lean_object* v_a_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1573_; 
v_contentChanges_1567_ = lean_ctor_get(v_p_1547_, 1);
v___x_1568_ = lean_box(0);
v_a_1569_ = lean_array_uget_borrowed(v_as_1550_, v_i_1552_);
v___x_1570_ = 0;
v___x_1571_ = lean_box(v___x_1570_);
lean_inc(v_a_1569_);
if (v_isShared_1566_ == 0)
{
lean_ctor_set(v___x_1565_, 1, v___x_1571_);
lean_ctor_set(v___x_1565_, 0, v_a_1569_);
v___x_1573_ = v___x_1565_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1569_);
lean_ctor_set(v_reuseFailAlloc_1626_, 1, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
lean_object* v___x_1574_; size_t v_sz_1575_; size_t v___x_1576_; lean_object* v___x_1577_; 
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1568_);
lean_ctor_set(v___x_1574_, 1, v___x_1573_);
v_sz_1575_ = lean_array_size(v_contentChanges_1567_);
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1548_, v___x_1549_, v_contentChanges_1567_, v_sz_1575_, v___x_1576_, v___x_1574_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1617_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1617_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1617_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1617_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1617_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v_fst_1582_; 
v_fst_1582_ = lean_ctor_get(v_a_1578_, 0);
if (lean_obj_tag(v_fst_1582_) == 0)
{
lean_object* v_snd_1583_; lean_object* v_snd_1584_; uint8_t v___x_1585_; 
lean_del_object(v___x_1580_);
v_snd_1583_ = lean_ctor_get(v_a_1578_, 1);
lean_inc(v_snd_1583_);
lean_dec(v_a_1578_);
v_snd_1584_ = lean_ctor_get(v_snd_1583_, 1);
v___x_1585_ = lean_unbox(v_snd_1584_);
if (v___x_1585_ == 0)
{
lean_object* v_fst_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1594_; 
v_fst_1586_ = lean_ctor_get(v_snd_1583_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_snd_1583_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v_snd_1583_, 1);
lean_dec(v_unused_1595_);
v___x_1588_ = v_snd_1583_;
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_fst_1586_);
lean_dec(v_snd_1583_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = lean_array_push(v_snd_1563_, v_fst_1586_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v___x_1590_);
lean_ctor_set(v___x_1588_, 0, v___x_1568_);
v___x_1592_ = v___x_1588_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
v_a_1557_ = v___x_1592_;
goto v___jp_1556_;
}
}
}
else
{
lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1602_; 
v_isSharedCheck_1602_ = !lean_is_exclusive(v_snd_1583_);
if (v_isSharedCheck_1602_ == 0)
{
lean_object* v_unused_1603_; lean_object* v_unused_1604_; 
v_unused_1603_ = lean_ctor_get(v_snd_1583_, 1);
lean_dec(v_unused_1603_);
v_unused_1604_ = lean_ctor_get(v_snd_1583_, 0);
lean_dec(v_unused_1604_);
v___x_1597_ = v_snd_1583_;
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
else
{
lean_dec(v_snd_1583_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1602_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1600_; 
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 1, v_snd_1563_);
lean_ctor_set(v___x_1597_, 0, v___x_1568_);
v___x_1600_ = v___x_1597_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_snd_1563_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
v_a_1557_ = v___x_1600_;
goto v___jp_1556_;
}
}
}
}
else
{
lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1614_; 
lean_inc_ref(v_fst_1582_);
v_isSharedCheck_1614_ = !lean_is_exclusive(v_a_1578_);
if (v_isSharedCheck_1614_ == 0)
{
lean_object* v_unused_1615_; lean_object* v_unused_1616_; 
v_unused_1615_ = lean_ctor_get(v_a_1578_, 1);
lean_dec(v_unused_1615_);
v_unused_1616_ = lean_ctor_get(v_a_1578_, 0);
lean_dec(v_unused_1616_);
v___x_1606_ = v_a_1578_;
v_isShared_1607_ = v_isSharedCheck_1614_;
goto v_resetjp_1605_;
}
else
{
lean_dec(v_a_1578_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1614_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 1, v_snd_1563_);
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v_fst_1582_);
lean_ctor_set(v_reuseFailAlloc_1613_, 1, v_snd_1563_);
v___x_1609_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
lean_object* v___x_1611_; 
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1609_);
v___x_1611_ = v___x_1580_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
}
}
}
else
{
lean_object* v_a_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1625_; 
lean_dec(v_snd_1563_);
v_a_1618_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1620_ = v___x_1577_;
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_a_1618_);
lean_dec(v___x_1577_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1625_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1623_; 
if (v_isShared_1621_ == 0)
{
v___x_1623_ = v___x_1620_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_a_1618_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
}
}
v___jp_1556_:
{
size_t v___x_1558_; size_t v___x_1559_; 
v___x_1558_ = ((size_t)1ULL);
v___x_1559_ = lean_usize_add(v_i_1552_, v___x_1558_);
v_i_1552_ = v___x_1559_;
v_b_1553_ = v_a_1557_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1___boxed(lean_object* v_p_1629_, lean_object* v___x_1630_, lean_object* v___x_1631_, lean_object* v_as_1632_, lean_object* v_sz_1633_, lean_object* v_i_1634_, lean_object* v_b_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_){
_start:
{
size_t v_sz_boxed_1638_; size_t v_i_boxed_1639_; lean_object* v_res_1640_; 
v_sz_boxed_1638_ = lean_unbox_usize(v_sz_1633_);
lean_dec(v_sz_1633_);
v_i_boxed_1639_ = lean_unbox_usize(v_i_1634_);
lean_dec(v_i_1634_);
v_res_1640_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1629_, v___x_1630_, v___x_1631_, v_as_1632_, v_sz_boxed_1638_, v_i_boxed_1639_, v_b_1635_, v___y_1636_);
lean_dec_ref(v___y_1636_);
lean_dec_ref(v_as_1632_);
lean_dec_ref(v___x_1631_);
lean_dec_ref(v___x_1630_);
lean_dec_ref(v_p_1629_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(lean_object* v_p_1644_, lean_object* v_oldInlayHints_1645_, lean_object* v_a_1646_){
_start:
{
lean_object* v_doc_1648_; lean_object* v_toEditableDocumentCore_1649_; lean_object* v_meta_1650_; lean_object* v_text_1651_; lean_object* v___x_1652_; size_t v_sz_1653_; size_t v___x_1654_; lean_object* v___x_1655_; 
v_doc_1648_ = lean_ctor_get(v_a_1646_, 1);
v_toEditableDocumentCore_1649_ = lean_ctor_get(v_doc_1648_, 0);
v_meta_1650_ = lean_ctor_get(v_toEditableDocumentCore_1649_, 0);
v_text_1651_ = lean_ctor_get(v_meta_1650_, 3);
v___x_1652_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0));
v_sz_1653_ = lean_array_size(v_oldInlayHints_1645_);
v___x_1654_ = ((size_t)0ULL);
v___x_1655_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1644_, v_text_1651_, v_meta_1650_, v_oldInlayHints_1645_, v_sz_1653_, v___x_1654_, v___x_1652_, v_a_1646_);
if (lean_obj_tag(v___x_1655_) == 0)
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1669_; 
v_a_1656_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1658_ = v___x_1655_;
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1655_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1669_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v_fst_1660_; 
v_fst_1660_ = lean_ctor_get(v_a_1656_, 0);
if (lean_obj_tag(v_fst_1660_) == 0)
{
lean_object* v_snd_1661_; lean_object* v___x_1663_; 
v_snd_1661_ = lean_ctor_get(v_a_1656_, 1);
lean_inc(v_snd_1661_);
lean_dec(v_a_1656_);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v_snd_1661_);
v___x_1663_ = v___x_1658_;
goto v_reusejp_1662_;
}
else
{
lean_object* v_reuseFailAlloc_1664_; 
v_reuseFailAlloc_1664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_snd_1661_);
v___x_1663_ = v_reuseFailAlloc_1664_;
goto v_reusejp_1662_;
}
v_reusejp_1662_:
{
return v___x_1663_;
}
}
else
{
lean_object* v_val_1665_; lean_object* v___x_1667_; 
lean_inc_ref(v_fst_1660_);
lean_dec(v_a_1656_);
v_val_1665_ = lean_ctor_get(v_fst_1660_, 0);
lean_inc(v_val_1665_);
lean_dec_ref_known(v_fst_1660_, 1);
if (v_isShared_1659_ == 0)
{
lean_ctor_set(v___x_1658_, 0, v_val_1665_);
v___x_1667_ = v___x_1658_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_val_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
v_a_1670_ = lean_ctor_get(v___x_1655_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1655_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1655_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___boxed(lean_object* v_p_1678_, lean_object* v_oldInlayHints_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1678_, v_oldInlayHints_1679_, v_a_1680_);
lean_dec_ref(v_a_1680_);
lean_dec_ref(v_oldInlayHints_1679_);
lean_dec_ref(v_p_1678_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(lean_object* v___x_1683_, lean_object* v___x_1684_, lean_object* v_as_1685_, size_t v_sz_1686_, size_t v_i_1687_, lean_object* v_b_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1683_, v___x_1684_, v_as_1685_, v_sz_1686_, v_i_1687_, v_b_1688_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___boxed(lean_object* v___x_1692_, lean_object* v___x_1693_, lean_object* v_as_1694_, lean_object* v_sz_1695_, lean_object* v_i_1696_, lean_object* v_b_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
size_t v_sz_boxed_1700_; size_t v_i_boxed_1701_; lean_object* v_res_1702_; 
v_sz_boxed_1700_ = lean_unbox_usize(v_sz_1695_);
lean_dec(v_sz_1695_);
v_i_boxed_1701_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(v___x_1692_, v___x_1693_, v_as_1694_, v_sz_boxed_1700_, v_i_boxed_1701_, v_b_1697_, v___y_1698_);
lean_dec_ref(v___y_1698_);
lean_dec_ref(v_as_1694_);
lean_dec_ref(v___x_1693_);
lean_dec_ref(v___x_1692_);
return v_res_1702_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(lean_object* v_a_1703_, lean_object* v_as_1704_, size_t v_i_1705_, size_t v_stop_1706_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_eq(v_i_1705_, v_stop_1706_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1708_ = lean_array_uget_borrowed(v_as_1704_, v_i_1705_);
v___x_1709_ = l_Lean_Elab_instBEqInlayHintTextEdit_beq(v_a_1703_, v___x_1708_);
if (v___x_1709_ == 0)
{
size_t v___x_1710_; size_t v___x_1711_; 
v___x_1710_ = ((size_t)1ULL);
v___x_1711_ = lean_usize_add(v_i_1705_, v___x_1710_);
v_i_1705_ = v___x_1711_;
goto _start;
}
else
{
return v___x_1709_;
}
}
else
{
uint8_t v___x_1713_; 
v___x_1713_ = 0;
return v___x_1713_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0___boxed(lean_object* v_a_1714_, lean_object* v_as_1715_, lean_object* v_i_1716_, lean_object* v_stop_1717_){
_start:
{
size_t v_i_boxed_1718_; size_t v_stop_boxed_1719_; uint8_t v_res_1720_; lean_object* v_r_1721_; 
v_i_boxed_1718_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_stop_boxed_1719_ = lean_unbox_usize(v_stop_1717_);
lean_dec(v_stop_1717_);
v_res_1720_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1714_, v_as_1715_, v_i_boxed_1718_, v_stop_boxed_1719_);
lean_dec_ref(v_as_1715_);
lean_dec_ref(v_a_1714_);
v_r_1721_ = lean_box(v_res_1720_);
return v_r_1721_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(lean_object* v_as_1722_, lean_object* v_a_1723_){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1724_ = lean_unsigned_to_nat(0u);
v___x_1725_ = lean_array_get_size(v_as_1722_);
v___x_1726_ = lean_nat_dec_lt(v___x_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
return v___x_1726_;
}
else
{
if (v___x_1726_ == 0)
{
return v___x_1726_;
}
else
{
size_t v___x_1727_; size_t v___x_1728_; uint8_t v___x_1729_; 
v___x_1727_ = ((size_t)0ULL);
v___x_1728_ = lean_usize_of_nat(v___x_1725_);
v___x_1729_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1723_, v_as_1722_, v___x_1727_, v___x_1728_);
return v___x_1729_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0___boxed(lean_object* v_as_1730_, lean_object* v_a_1731_){
_start:
{
uint8_t v_res_1732_; lean_object* v_r_1733_; 
v_res_1732_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_as_1730_, v_a_1731_);
lean_dec_ref(v_a_1731_);
lean_dec_ref(v_as_1730_);
v_r_1733_ = lean_box(v_res_1732_);
return v_r_1733_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(lean_object* v___x_1734_, lean_object* v_as_1735_, size_t v_i_1736_, size_t v_stop_1737_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_eq(v_i_1736_, v_stop_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v_textEdits_1740_; uint8_t v___x_1741_; 
v___x_1739_ = lean_array_uget_borrowed(v_as_1735_, v_i_1736_);
v_textEdits_1740_ = lean_ctor_get(v___x_1739_, 3);
v___x_1741_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_textEdits_1740_, v___x_1734_);
if (v___x_1741_ == 0)
{
size_t v___x_1742_; size_t v___x_1743_; 
v___x_1742_ = ((size_t)1ULL);
v___x_1743_ = lean_usize_add(v_i_1736_, v___x_1742_);
v_i_1736_ = v___x_1743_;
goto _start;
}
else
{
return v___x_1741_;
}
}
else
{
uint8_t v___x_1745_; 
v___x_1745_ = 0;
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1___boxed(lean_object* v___x_1746_, lean_object* v_as_1747_, lean_object* v_i_1748_, lean_object* v_stop_1749_){
_start:
{
size_t v_i_boxed_1750_; size_t v_stop_boxed_1751_; uint8_t v_res_1752_; lean_object* v_r_1753_; 
v_i_boxed_1750_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_stop_boxed_1751_ = lean_unbox_usize(v_stop_1749_);
lean_dec(v_stop_1749_);
v_res_1752_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1746_, v_as_1747_, v_i_boxed_1750_, v_stop_boxed_1751_);
lean_dec_ref(v_as_1747_);
lean_dec_ref(v___x_1746_);
v_r_1753_ = lean_box(v_res_1752_);
return v_r_1753_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(lean_object* v_oldInlayHints_1754_, lean_object* v___x_1755_, lean_object* v___x_1756_, lean_object* v_as_1757_, size_t v_i_1758_, size_t v_stop_1759_){
_start:
{
uint8_t v___x_1764_; 
v___x_1764_ = lean_usize_dec_eq(v_i_1758_, v_stop_1759_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; uint8_t v___x_1766_; uint8_t v___x_1767_; lean_object* v___x_1769_; 
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_nat_dec_lt(v___x_1765_, v___x_1755_);
v___x_1767_ = 1;
v___x_1769_ = lean_array_uget(v_as_1757_, v_i_1758_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_range_1770_; lean_object* v_text_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1784_; 
v_range_1770_ = lean_ctor_get(v___x_1769_, 0);
v_text_1771_ = lean_ctor_get(v___x_1769_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1773_ = v___x_1769_;
v_isShared_1774_ = v_isSharedCheck_1784_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_text_1771_);
lean_inc(v_range_1770_);
lean_dec(v___x_1769_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1784_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___x_1775_ = lean_array_get_size(v_oldInlayHints_1754_);
v___x_1776_ = lean_nat_dec_lt(v___x_1765_, v___x_1775_);
if (v___x_1776_ == 0)
{
lean_del_object(v___x_1773_);
lean_dec_ref(v_text_1771_);
lean_dec_ref(v_range_1770_);
goto v___jp_1768_;
}
else
{
if (v___x_1776_ == 0)
{
lean_del_object(v___x_1773_);
lean_dec_ref(v_text_1771_);
lean_dec_ref(v_range_1770_);
return v___x_1767_;
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1779_; 
v___x_1777_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1756_, v_range_1770_);
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1777_);
v___x_1779_ = v___x_1773_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_text_1771_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
size_t v___x_1780_; size_t v___x_1781_; uint8_t v___x_1782_; 
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = lean_usize_of_nat(v___x_1775_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1779_, v_oldInlayHints_1754_, v___x_1780_, v___x_1781_);
lean_dec_ref(v___x_1779_);
if (v___x_1782_ == 0)
{
return v___x_1767_;
}
else
{
goto v___jp_1760_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1769_);
goto v___jp_1768_;
}
v___jp_1768_:
{
if (v___x_1766_ == 0)
{
goto v___jp_1760_;
}
else
{
return v___x_1767_;
}
}
}
else
{
uint8_t v___x_1785_; 
v___x_1785_ = 0;
return v___x_1785_;
}
v___jp_1760_:
{
size_t v___x_1761_; size_t v___x_1762_; 
v___x_1761_ = ((size_t)1ULL);
v___x_1762_ = lean_usize_add(v_i_1758_, v___x_1761_);
v_i_1758_ = v___x_1762_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2___boxed(lean_object* v_oldInlayHints_1786_, lean_object* v___x_1787_, lean_object* v___x_1788_, lean_object* v_as_1789_, lean_object* v_i_1790_, lean_object* v_stop_1791_){
_start:
{
size_t v_i_boxed_1792_; size_t v_stop_boxed_1793_; uint8_t v_res_1794_; lean_object* v_r_1795_; 
v_i_boxed_1792_ = lean_unbox_usize(v_i_1790_);
lean_dec(v_i_1790_);
v_stop_boxed_1793_ = lean_unbox_usize(v_stop_1791_);
lean_dec(v_stop_1791_);
v_res_1794_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1786_, v___x_1787_, v___x_1788_, v_as_1789_, v_i_boxed_1792_, v_stop_boxed_1793_);
lean_dec_ref(v_as_1789_);
lean_dec_ref(v___x_1788_);
lean_dec(v___x_1787_);
lean_dec_ref(v_oldInlayHints_1786_);
v_r_1795_ = lean_box(v_res_1794_);
return v_r_1795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(lean_object* v_p_1796_, lean_object* v_oldInlayHints_1797_, lean_object* v_a_1798_){
_start:
{
uint8_t v___y_1801_; lean_object* v_contentChanges_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v_contentChanges_1807_ = lean_ctor_get(v_p_1796_, 1);
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_array_get_size(v_contentChanges_1807_);
v___x_1810_ = lean_nat_dec_lt(v___x_1808_, v___x_1809_);
if (v___x_1810_ == 0)
{
uint8_t v___x_1811_; 
v___x_1811_ = 1;
v___y_1801_ = v___x_1811_;
goto v___jp_1800_;
}
else
{
if (v___x_1810_ == 0)
{
v___y_1801_ = v___x_1810_;
goto v___jp_1800_;
}
else
{
lean_object* v_doc_1812_; lean_object* v_toEditableDocumentCore_1813_; lean_object* v_meta_1814_; lean_object* v_text_1815_; size_t v___x_1816_; size_t v___x_1817_; uint8_t v___x_1818_; 
v_doc_1812_ = lean_ctor_get(v_a_1798_, 1);
v_toEditableDocumentCore_1813_ = lean_ctor_get(v_doc_1812_, 0);
v_meta_1814_ = lean_ctor_get(v_toEditableDocumentCore_1813_, 0);
v_text_1815_ = lean_ctor_get(v_meta_1814_, 3);
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = lean_usize_of_nat(v___x_1809_);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1797_, v___x_1809_, v_text_1815_, v_contentChanges_1807_, v___x_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
v___y_1801_ = v___x_1810_;
goto v___jp_1800_;
}
else
{
uint8_t v___x_1819_; 
v___x_1819_ = 0;
v___y_1801_ = v___x_1819_;
goto v___jp_1800_;
}
}
}
v___jp_1800_:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_io_mono_ms_now();
if (v___y_1801_ == 0)
{
lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
return v___x_1804_;
}
else
{
lean_object* v___x_1805_; lean_object* v___x_1806_; 
lean_dec(v___x_1802_);
v___x_1805_ = lean_box(0);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___boxed(lean_object* v_p_1820_, lean_object* v_oldInlayHints_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1820_, v_oldInlayHints_1821_, v_a_1822_);
lean_dec_ref(v_a_1822_);
lean_dec_ref(v_oldInlayHints_1821_);
lean_dec_ref(v_p_1820_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange(lean_object* v_p_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_oldInlayHints_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1859_; 
v_oldInlayHints_1829_ = lean_ctor_get(v_a_1826_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_a_1826_);
if (v_isSharedCheck_1859_ == 0)
{
lean_object* v_unused_1860_; lean_object* v_unused_1861_; 
v_unused_1860_ = lean_ctor_get(v_a_1826_, 2);
lean_dec(v_unused_1860_);
v_unused_1861_ = lean_ctor_get(v_a_1826_, 1);
lean_dec(v_unused_1861_);
v___x_1831_ = v_a_1826_;
v_isShared_1832_ = v_isSharedCheck_1859_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_oldInlayHints_1829_);
lean_dec(v_a_1826_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1859_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; 
v___x_1833_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1825_, v_oldInlayHints_1829_, v_a_1827_);
if (lean_obj_tag(v___x_1833_) == 0)
{
lean_object* v_a_1834_; lean_object* v___x_1835_; lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1850_; 
v_a_1834_ = lean_ctor_get(v___x_1833_, 0);
lean_inc(v_a_1834_);
lean_dec_ref_known(v___x_1833_, 1);
v___x_1835_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1825_, v_oldInlayHints_1829_, v_a_1827_);
lean_dec_ref(v_oldInlayHints_1829_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1850_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1850_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; uint8_t v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = 1;
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 2, v_a_1836_);
lean_ctor_set(v___x_1831_, 1, v___x_1840_);
lean_ctor_set(v___x_1831_, 0, v_a_1834_);
v___x_1843_ = v___x_1831_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1834_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1840_);
lean_ctor_set(v_reuseFailAlloc_1849_, 2, v_a_1836_);
v___x_1843_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
lean_ctor_set_uint8(v___x_1843_, sizeof(void*)*3, v___x_1841_);
v___x_1844_ = lean_box(0);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1843_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1845_);
v___x_1847_ = v___x_1838_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_del_object(v___x_1831_);
lean_dec_ref(v_oldInlayHints_1829_);
v_a_1851_ = lean_ctor_get(v___x_1833_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1833_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1833_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1833_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed(lean_object* v_p_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_Server_FileWorker_handleInlayHintsDidChange(v_p_1862_, v_a_1863_, v_a_1864_);
lean_dec_ref(v_a_1864_);
lean_dec_ref(v_p_1862_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(lean_object* v___x_1867_, lean_object* v_x_1868_){
_start:
{
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed(lean_object* v___x_1869_, lean_object* v_x_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(v___x_1869_, v_x_1870_);
lean_dec_ref(v_x_1870_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v_ks_1876_; lean_object* v_vs_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1901_; 
v_ks_1876_ = lean_ctor_get(v_x_1872_, 0);
v_vs_1877_ = lean_ctor_get(v_x_1872_, 1);
v_isSharedCheck_1901_ = !lean_is_exclusive(v_x_1872_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1879_ = v_x_1872_;
v_isShared_1880_ = v_isSharedCheck_1901_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_vs_1877_);
lean_inc(v_ks_1876_);
lean_dec(v_x_1872_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1901_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1881_ = lean_array_get_size(v_ks_1876_);
v___x_1882_ = lean_nat_dec_lt(v_x_1873_, v___x_1881_);
if (v___x_1882_ == 0)
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1886_; 
lean_dec(v_x_1873_);
v___x_1883_ = lean_array_push(v_ks_1876_, v_x_1874_);
v___x_1884_ = lean_array_push(v_vs_1877_, v_x_1875_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1884_);
lean_ctor_set(v___x_1879_, 0, v___x_1883_);
v___x_1886_ = v___x_1879_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1883_);
lean_ctor_set(v_reuseFailAlloc_1887_, 1, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
else
{
lean_object* v_k_x27_1888_; uint8_t v___x_1889_; 
v_k_x27_1888_ = lean_array_fget_borrowed(v_ks_1876_, v_x_1873_);
v___x_1889_ = lean_string_dec_eq(v_x_1874_, v_k_x27_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1891_; 
if (v_isShared_1880_ == 0)
{
v___x_1891_ = v___x_1879_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_ks_1876_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v_vs_1877_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_unsigned_to_nat(1u);
v___x_1893_ = lean_nat_add(v_x_1873_, v___x_1892_);
lean_dec(v_x_1873_);
v_x_1872_ = v___x_1891_;
v_x_1873_ = v___x_1893_;
goto _start;
}
}
else
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1899_; 
v___x_1896_ = lean_array_fset(v_ks_1876_, v_x_1873_, v_x_1874_);
v___x_1897_ = lean_array_fset(v_vs_1877_, v_x_1873_, v_x_1875_);
lean_dec(v_x_1873_);
if (v_isShared_1880_ == 0)
{
lean_ctor_set(v___x_1879_, 1, v___x_1897_);
lean_ctor_set(v___x_1879_, 0, v___x_1896_);
v___x_1899_ = v___x_1879_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v___x_1896_);
lean_ctor_set(v_reuseFailAlloc_1900_, 1, v___x_1897_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(lean_object* v_n_1902_, lean_object* v_k_1903_, lean_object* v_v_1904_){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = lean_unsigned_to_nat(0u);
v___x_1906_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_n_1902_, v___x_1905_, v_k_1903_, v_v_1904_);
return v___x_1906_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(lean_object* v_x_1908_, size_t v_x_1909_, size_t v_x_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_){
_start:
{
if (lean_obj_tag(v_x_1908_) == 0)
{
lean_object* v_es_1913_; size_t v___x_1914_; size_t v___x_1915_; lean_object* v_j_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_es_1913_ = lean_ctor_get(v_x_1908_, 0);
v___x_1914_ = ((size_t)31ULL);
v___x_1915_ = lean_usize_land(v_x_1909_, v___x_1914_);
v_j_1916_ = lean_usize_to_nat(v___x_1915_);
v___x_1917_ = lean_array_get_size(v_es_1913_);
v___x_1918_ = lean_nat_dec_lt(v_j_1916_, v___x_1917_);
if (v___x_1918_ == 0)
{
lean_dec(v_j_1916_);
lean_dec(v_x_1912_);
lean_dec_ref(v_x_1911_);
return v_x_1908_;
}
else
{
lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1957_; 
lean_inc_ref(v_es_1913_);
v_isSharedCheck_1957_ = !lean_is_exclusive(v_x_1908_);
if (v_isSharedCheck_1957_ == 0)
{
lean_object* v_unused_1958_; 
v_unused_1958_ = lean_ctor_get(v_x_1908_, 0);
lean_dec(v_unused_1958_);
v___x_1920_ = v_x_1908_;
v_isShared_1921_ = v_isSharedCheck_1957_;
goto v_resetjp_1919_;
}
else
{
lean_dec(v_x_1908_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1957_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v_v_1922_; lean_object* v___x_1923_; lean_object* v_xs_x27_1924_; lean_object* v___y_1926_; 
v_v_1922_ = lean_array_fget(v_es_1913_, v_j_1916_);
v___x_1923_ = lean_box(0);
v_xs_x27_1924_ = lean_array_fset(v_es_1913_, v_j_1916_, v___x_1923_);
switch(lean_obj_tag(v_v_1922_))
{
case 0:
{
lean_object* v_key_1931_; lean_object* v_val_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1942_; 
v_key_1931_ = lean_ctor_get(v_v_1922_, 0);
v_val_1932_ = lean_ctor_get(v_v_1922_, 1);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_v_1922_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1934_ = v_v_1922_;
v_isShared_1935_ = v_isSharedCheck_1942_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_val_1932_);
lean_inc(v_key_1931_);
lean_dec(v_v_1922_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1942_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
uint8_t v___x_1936_; 
v___x_1936_ = lean_string_dec_eq(v_x_1911_, v_key_1931_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1937_; lean_object* v___x_1938_; 
lean_del_object(v___x_1934_);
v___x_1937_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1931_, v_val_1932_, v_x_1911_, v_x_1912_);
v___x_1938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1938_, 0, v___x_1937_);
v___y_1926_ = v___x_1938_;
goto v___jp_1925_;
}
else
{
lean_object* v___x_1940_; 
lean_dec(v_val_1932_);
lean_dec(v_key_1931_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v_x_1912_);
lean_ctor_set(v___x_1934_, 0, v_x_1911_);
v___x_1940_ = v___x_1934_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_x_1911_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_x_1912_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
v___y_1926_ = v___x_1940_;
goto v___jp_1925_;
}
}
}
}
case 1:
{
lean_object* v_node_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1955_; 
v_node_1943_ = lean_ctor_get(v_v_1922_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_v_1922_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1945_ = v_v_1922_;
v_isShared_1946_ = v_isSharedCheck_1955_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_node_1943_);
lean_dec(v_v_1922_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1955_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
size_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; size_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1947_ = ((size_t)5ULL);
v___x_1948_ = lean_usize_shift_right(v_x_1909_, v___x_1947_);
v___x_1949_ = ((size_t)1ULL);
v___x_1950_ = lean_usize_add(v_x_1910_, v___x_1949_);
v___x_1951_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_node_1943_, v___x_1948_, v___x_1950_, v_x_1911_, v_x_1912_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1951_);
v___x_1953_ = v___x_1945_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1951_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
v___y_1926_ = v___x_1953_;
goto v___jp_1925_;
}
}
}
default: 
{
lean_object* v___x_1956_; 
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v_x_1911_);
lean_ctor_set(v___x_1956_, 1, v_x_1912_);
v___y_1926_ = v___x_1956_;
goto v___jp_1925_;
}
}
v___jp_1925_:
{
lean_object* v___x_1927_; lean_object* v___x_1929_; 
v___x_1927_ = lean_array_fset(v_xs_x27_1924_, v_j_1916_, v___y_1926_);
lean_dec(v_j_1916_);
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1927_);
v___x_1929_ = v___x_1920_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v___x_1927_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
}
}
}
else
{
lean_object* v_ks_1959_; lean_object* v_vs_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1978_; 
v_ks_1959_ = lean_ctor_get(v_x_1908_, 0);
v_vs_1960_ = lean_ctor_get(v_x_1908_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_x_1908_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1962_ = v_x_1908_;
v_isShared_1963_ = v_isSharedCheck_1978_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_vs_1960_);
lean_inc(v_ks_1959_);
lean_dec(v_x_1908_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1978_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_ks_1959_);
lean_ctor_set(v_reuseFailAlloc_1977_, 1, v_vs_1960_);
v___x_1965_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v_newNode_1966_; size_t v___x_1967_; uint8_t v___x_1968_; 
v_newNode_1966_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v___x_1965_, v_x_1911_, v_x_1912_);
v___x_1967_ = ((size_t)7ULL);
v___x_1968_ = lean_usize_dec_le(v___x_1967_, v_x_1910_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1969_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1966_);
v___x_1970_ = lean_unsigned_to_nat(4u);
v___x_1971_ = lean_nat_dec_lt(v___x_1969_, v___x_1970_);
lean_dec(v___x_1969_);
if (v___x_1971_ == 0)
{
lean_object* v_ks_1972_; lean_object* v_vs_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v_ks_1972_ = lean_ctor_get(v_newNode_1966_, 0);
lean_inc_ref(v_ks_1972_);
v_vs_1973_ = lean_ctor_get(v_newNode_1966_, 1);
lean_inc_ref(v_vs_1973_);
lean_dec_ref(v_newNode_1966_);
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0);
v___x_1976_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_x_1910_, v_ks_1972_, v_vs_1973_, v___x_1974_, v___x_1975_);
lean_dec_ref(v_vs_1973_);
lean_dec_ref(v_ks_1972_);
return v___x_1976_;
}
else
{
return v_newNode_1966_;
}
}
else
{
return v_newNode_1966_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(size_t v_depth_1979_, lean_object* v_keys_1980_, lean_object* v_vals_1981_, lean_object* v_i_1982_, lean_object* v_entries_1983_){
_start:
{
lean_object* v___x_1984_; uint8_t v___x_1985_; 
v___x_1984_ = lean_array_get_size(v_keys_1980_);
v___x_1985_ = lean_nat_dec_lt(v_i_1982_, v___x_1984_);
if (v___x_1985_ == 0)
{
lean_dec(v_i_1982_);
return v_entries_1983_;
}
else
{
lean_object* v_k_1986_; lean_object* v_v_1987_; uint64_t v___x_1988_; size_t v_h_1989_; size_t v___x_1990_; lean_object* v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; size_t v___x_1994_; size_t v_h_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v_k_1986_ = lean_array_fget_borrowed(v_keys_1980_, v_i_1982_);
v_v_1987_ = lean_array_fget_borrowed(v_vals_1981_, v_i_1982_);
v___x_1988_ = lean_string_hash(v_k_1986_);
v_h_1989_ = lean_uint64_to_usize(v___x_1988_);
v___x_1990_ = ((size_t)5ULL);
v___x_1991_ = lean_unsigned_to_nat(1u);
v___x_1992_ = ((size_t)1ULL);
v___x_1993_ = lean_usize_sub(v_depth_1979_, v___x_1992_);
v___x_1994_ = lean_usize_mul(v___x_1990_, v___x_1993_);
v_h_1995_ = lean_usize_shift_right(v_h_1989_, v___x_1994_);
v___x_1996_ = lean_nat_add(v_i_1982_, v___x_1991_);
lean_dec(v_i_1982_);
lean_inc(v_v_1987_);
lean_inc(v_k_1986_);
v___x_1997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_entries_1983_, v_h_1995_, v_depth_1979_, v_k_1986_, v_v_1987_);
v_i_1982_ = v___x_1996_;
v_entries_1983_ = v___x_1997_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_depth_1999_, lean_object* v_keys_2000_, lean_object* v_vals_2001_, lean_object* v_i_2002_, lean_object* v_entries_2003_){
_start:
{
size_t v_depth_boxed_2004_; lean_object* v_res_2005_; 
v_depth_boxed_2004_ = lean_unbox_usize(v_depth_1999_);
lean_dec(v_depth_1999_);
v_res_2005_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_boxed_2004_, v_keys_2000_, v_vals_2001_, v_i_2002_, v_entries_2003_);
lean_dec_ref(v_vals_2001_);
lean_dec_ref(v_keys_2000_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_x_2006_, lean_object* v_x_2007_, lean_object* v_x_2008_, lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
size_t v_x_2384__boxed_2011_; size_t v_x_2385__boxed_2012_; lean_object* v_res_2013_; 
v_x_2384__boxed_2011_ = lean_unbox_usize(v_x_2007_);
lean_dec(v_x_2007_);
v_x_2385__boxed_2012_ = lean_unbox_usize(v_x_2008_);
lean_dec(v_x_2008_);
v_res_2013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_2006_, v_x_2384__boxed_2011_, v_x_2385__boxed_2012_, v_x_2009_, v_x_2010_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(lean_object* v_x_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
uint64_t v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; lean_object* v___x_2020_; 
v___x_2017_ = lean_string_hash(v_x_2015_);
v___x_2018_ = lean_uint64_to_usize(v___x_2017_);
v___x_2019_ = ((size_t)1ULL);
v___x_2020_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_2014_, v___x_2018_, v___x_2019_, v_x_2015_, v_x_2016_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(lean_object* v_mutex_2021_, lean_object* v_a_x3f_2022_){
_start:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; 
v___x_2024_ = lean_io_basemutex_unlock(v_mutex_2021_);
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0___boxed(lean_object* v_mutex_2026_, lean_object* v_a_x3f_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2026_, v_a_x3f_2027_);
lean_dec(v_a_x3f_2027_);
lean_dec(v_mutex_2026_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_mutex_2030_, lean_object* v_k_2031_, lean_object* v___y_2032_){
_start:
{
lean_object* v_ref_2034_; lean_object* v_mutex_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_ref_2034_ = lean_ctor_get(v_mutex_2030_, 0);
lean_inc(v_ref_2034_);
v_mutex_2035_ = lean_ctor_get(v_mutex_2030_, 1);
lean_inc(v_mutex_2035_);
lean_dec_ref(v_mutex_2030_);
v___x_2036_ = lean_io_basemutex_lock(v_mutex_2035_);
lean_inc_ref(v___y_2032_);
v___x_2037_ = lean_apply_3(v_k_2031_, v_ref_2034_, v___y_2032_, lean_box(0));
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2040_; uint8_t v_isShared_2041_; uint8_t v_isSharedCheck_2054_; 
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2040_ = v___x_2037_;
v_isShared_2041_ = v_isSharedCheck_2054_;
goto v_resetjp_2039_;
}
else
{
lean_inc(v_a_2038_);
lean_dec(v___x_2037_);
v___x_2040_ = lean_box(0);
v_isShared_2041_ = v_isSharedCheck_2054_;
goto v_resetjp_2039_;
}
v_resetjp_2039_:
{
lean_object* v___x_2043_; 
lean_inc(v_a_2038_);
if (v_isShared_2041_ == 0)
{
lean_ctor_set_tag(v___x_2040_, 1);
v___x_2043_ = v___x_2040_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2038_);
v___x_2043_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
lean_object* v___x_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v___x_2044_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2035_, v___x_2043_);
lean_dec_ref(v___x_2043_);
lean_dec(v_mutex_2035_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2044_, 0);
lean_dec(v_unused_2052_);
v___x_2046_ = v___x_2044_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_dec(v___x_2044_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
lean_ctor_set(v___x_2046_, 0, v_a_2038_);
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2038_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
v_a_2055_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2056_ = lean_box(0);
v___x_2057_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2035_, v___x_2056_);
lean_dec(v_mutex_2035_);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_2057_, 0);
lean_dec(v_unused_2065_);
v___x_2059_ = v___x_2057_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_dec(v___x_2057_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set_tag(v___x_2059_, 1);
lean_ctor_set(v___x_2059_, 0, v_a_2055_);
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2055_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_mutex_2066_, lean_object* v_k_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2066_, v_k_2067_, v___y_2068_);
lean_dec_ref(v___y_2068_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(lean_object* v_val_2071_, lean_object* v___f_2072_, lean_object* v_param_2073_, lean_object* v___x_2074_, lean_object* v_x_2075_, lean_object* v___y_2076_){
_start:
{
lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2078_ = lean_st_ref_get(v_val_2071_);
lean_inc_ref(v___y_2076_);
v___x_2079_ = lean_apply_4(v___f_2072_, v_param_2073_, v___x_2078_, v___y_2076_, lean_box(0));
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_object* v_a_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2089_; 
v_a_2080_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2089_ == 0)
{
v___x_2082_ = v___x_2079_;
v_isShared_2083_ = v_isSharedCheck_2089_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_a_2080_);
lean_dec(v___x_2079_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2089_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_snd_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
v_snd_2084_ = lean_ctor_get(v_a_2080_, 1);
lean_inc(v_snd_2084_);
lean_dec(v_a_2080_);
v___x_2085_ = lean_st_ref_swap(v_val_2071_, v_snd_2084_);
lean_dec(v___x_2085_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 0, v___x_2074_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2074_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
else
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2097_; 
v_a_2090_ = lean_ctor_get(v___x_2079_, 0);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2079_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2092_ = v___x_2079_;
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2079_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2097_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2095_; 
if (v_isShared_2093_ == 0)
{
v___x_2095_ = v___x_2092_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed(lean_object* v_val_2098_, lean_object* v___f_2099_, lean_object* v_param_2100_, lean_object* v___x_2101_, lean_object* v_x_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(v_val_2098_, v___f_2099_, v_param_2100_, v___x_2101_, v_x_2102_, v___y_2103_);
lean_dec_ref(v___y_2103_);
lean_dec(v_val_2098_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(lean_object* v___f_2106_, lean_object* v___f_2107_, lean_object* v___x_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = lean_st_ref_get(v___y_2109_);
v___x_2113_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_2112_, v___f_2106_, v___y_2110_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2123_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2116_ = v___x_2113_;
v_isShared_2117_ = v_isSharedCheck_2123_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_a_2114_);
lean_dec(v___x_2113_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2123_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2118_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2107_, v_a_2114_);
v___x_2119_ = lean_st_ref_swap(v___y_2109_, v___x_2118_);
lean_dec(v___x_2119_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 0, v___x_2108_);
v___x_2121_ = v___x_2116_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2108_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v___f_2107_);
v_a_2124_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2113_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2113_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed(lean_object* v___f_2132_, lean_object* v___f_2133_, lean_object* v___x_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(v___f_2132_, v___f_2133_, v___x_2134_, v___y_2135_, v___y_2136_);
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(lean_object* v_val_2139_, lean_object* v___f_2140_, lean_object* v___x_2141_, lean_object* v___f_2142_, lean_object* v_val_2143_, lean_object* v_param_2144_, lean_object* v___y_2145_){
_start:
{
lean_object* v___f_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; 
v___f_2147_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_2147_, 0, v_val_2139_);
lean_closure_set(v___f_2147_, 1, v___f_2140_);
lean_closure_set(v___f_2147_, 2, v_param_2144_);
lean_closure_set(v___f_2147_, 3, v___x_2141_);
v___f_2148_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_2148_, 0, v___f_2147_);
lean_closure_set(v___f_2148_, 1, v___f_2142_);
lean_closure_set(v___f_2148_, 2, v___x_2141_);
v___x_2149_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_2143_, v___f_2148_, v___y_2145_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed(lean_object* v_val_2150_, lean_object* v___f_2151_, lean_object* v___x_2152_, lean_object* v___f_2153_, lean_object* v_val_2154_, lean_object* v_param_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(v_val_2150_, v___f_2151_, v___x_2152_, v___f_2153_, v_val_2154_, v_param_2155_, v___y_2156_);
lean_dec_ref(v___y_2156_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(lean_object* v___x_2159_, lean_object* v_x_2160_){
_start:
{
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed(lean_object* v___x_2161_, lean_object* v_x_2162_){
_start:
{
lean_object* v_res_2163_; 
v_res_2163_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(v___x_2161_, v_x_2162_);
lean_dec_ref(v_x_2162_);
return v_res_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(lean_object* v_params_2166_){
_start:
{
lean_object* v___x_2167_; 
lean_inc(v_params_2166_);
v___x_2167_ = l_Lean_Lsp_instFromJsonInlayHintParams_fromJson(v_params_2166_);
if (lean_obj_tag(v___x_2167_) == 0)
{
lean_object* v_a_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2183_; 
v_a_2168_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2170_ = v___x_2167_;
v_isShared_2171_ = v_isSharedCheck_2183_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_a_2168_);
lean_dec(v___x_2167_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2183_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
uint8_t v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2181_; 
v___x_2172_ = 3;
v___x_2173_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2174_ = l_Lean_Json_compress(v_params_2166_);
v___x_2175_ = lean_string_append(v___x_2173_, v___x_2174_);
lean_dec_ref(v___x_2174_);
v___x_2176_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1));
v___x_2177_ = lean_string_append(v___x_2175_, v___x_2176_);
v___x_2178_ = lean_string_append(v___x_2177_, v_a_2168_);
lean_dec(v_a_2168_);
v___x_2179_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set_uint8(v___x_2179_, sizeof(void*)*1, v___x_2172_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 0, v___x_2179_);
v___x_2181_ = v___x_2170_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v___x_2179_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
return v___x_2181_;
}
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_params_2166_);
v_a_2184_ = lean_ctor_get(v___x_2167_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2167_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2167_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_j_2192_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_j_2192_);
if (lean_obj_tag(v___x_2193_) == 0)
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2193_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2193_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2210_; 
v_a_2202_ = lean_ctor_get(v___x_2193_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2204_ = v___x_2193_;
v_isShared_2205_ = v_isSharedCheck_2210_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2193_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2210_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v_textDocument_2206_; lean_object* v___x_2208_; 
v_textDocument_2206_ = lean_ctor_get(v_a_2202_, 1);
lean_inc_ref(v_textDocument_2206_);
lean_dec(v_a_2202_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v_textDocument_2206_);
v___x_2208_ = v___x_2204_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_textDocument_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(lean_object* v_method_2211_, lean_object* v_inst_2212_, lean_object* v_onDidChange_2213_, lean_object* v_param_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2211_, v___y_2215_, lean_box(0), v_inst_2212_, v___y_2216_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2220_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v___x_2218_, 1);
lean_inc_ref(v___y_2216_);
v___x_2220_ = lean_apply_4(v_onDidChange_2213_, v_param_2214_, v_a_2219_, v___y_2216_, lean_box(0));
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2239_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2223_ = v___x_2220_;
v_isShared_2224_ = v_isSharedCheck_2239_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2220_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2239_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v_snd_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2237_; 
v_snd_2225_ = lean_ctor_get(v_a_2221_, 1);
v_isSharedCheck_2237_ = !lean_is_exclusive(v_a_2221_);
if (v_isSharedCheck_2237_ == 0)
{
lean_object* v_unused_2238_; 
v_unused_2238_ = lean_ctor_get(v_a_2221_, 0);
lean_dec(v_unused_2238_);
v___x_2227_ = v_a_2221_;
v_isShared_2228_ = v_isSharedCheck_2237_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_snd_2225_);
lean_dec(v_a_2221_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2237_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v_inst_2212_);
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_inst_2212_);
lean_ctor_set(v_reuseFailAlloc_2236_, 1, v_snd_2225_);
v___x_2230_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2234_; 
v___x_2231_ = lean_box(0);
v___x_2232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2232_, 0, v___x_2231_);
lean_ctor_set(v___x_2232_, 1, v___x_2230_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2232_);
v___x_2234_ = v___x_2223_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2232_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_inst_2212_);
v_a_2240_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2220_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2220_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec_ref(v_param_2214_);
lean_dec_ref(v_onDidChange_2213_);
lean_dec(v_inst_2212_);
v_a_2248_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2218_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2218_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed(lean_object* v_method_2256_, lean_object* v_inst_2257_, lean_object* v_onDidChange_2258_, lean_object* v_param_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(v_method_2256_, v_inst_2257_, v_onDidChange_2258_, v_param_2259_, v___y_2260_, v___y_2261_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v_method_2256_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(size_t v_sz_2264_, size_t v_i_2265_, lean_object* v_bs_2266_){
_start:
{
uint8_t v___x_2267_; 
v___x_2267_ = lean_usize_dec_lt(v_i_2265_, v_sz_2264_);
if (v___x_2267_ == 0)
{
return v_bs_2266_;
}
else
{
lean_object* v_v_2268_; lean_object* v___x_2269_; lean_object* v_bs_x27_2270_; lean_object* v___x_2271_; size_t v___x_2272_; size_t v___x_2273_; lean_object* v___x_2274_; 
v_v_2268_ = lean_array_uget(v_bs_2266_, v_i_2265_);
v___x_2269_ = lean_unsigned_to_nat(0u);
v_bs_x27_2270_ = lean_array_uset(v_bs_2266_, v_i_2265_, v___x_2269_);
v___x_2271_ = l_Lean_Lsp_instToJsonInlayHint_toJson(v_v_2268_);
v___x_2272_ = ((size_t)1ULL);
v___x_2273_ = lean_usize_add(v_i_2265_, v___x_2272_);
v___x_2274_ = lean_array_uset(v_bs_x27_2270_, v_i_2265_, v___x_2271_);
v_i_2265_ = v___x_2273_;
v_bs_2266_ = v___x_2274_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8___boxed(lean_object* v_sz_2276_, lean_object* v_i_2277_, lean_object* v_bs_2278_){
_start:
{
size_t v_sz_boxed_2279_; size_t v_i_boxed_2280_; lean_object* v_res_2281_; 
v_sz_boxed_2279_ = lean_unbox_usize(v_sz_2276_);
lean_dec(v_sz_2276_);
v_i_boxed_2280_ = lean_unbox_usize(v_i_2277_);
lean_dec(v_i_2277_);
v_res_2281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_boxed_2279_, v_i_boxed_2280_, v_bs_2278_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object* v_a_2282_){
_start:
{
size_t v_sz_2283_; size_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; 
v_sz_2283_ = lean_array_size(v_a_2282_);
v___x_2284_ = ((size_t)0ULL);
v___x_2285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_2283_, v___x_2284_, v_a_2282_);
v___x_2286_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
return v___x_2286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_params_2287_){
_start:
{
lean_object* v___x_2289_; 
v___x_2289_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_params_2287_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2297_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2297_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2297_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2297_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v___x_2295_; 
if (v_isShared_2293_ == 0)
{
lean_ctor_set_tag(v___x_2292_, 1);
v___x_2295_ = v___x_2292_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v_a_2290_);
v___x_2295_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
return v___x_2295_;
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
v_a_2298_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2289_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2289_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
lean_ctor_set_tag(v___x_2300_, 0);
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_params_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2306_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(lean_object* v_method_2309_, lean_object* v_inst_2310_, lean_object* v_handler_2311_, lean_object* v_param_2312_, lean_object* v_state_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v___x_2316_; 
v___x_2316_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_param_2312_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2309_, v_state_2313_, lean_box(0), v_inst_2310_, v___y_2314_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
lean_inc_ref(v___y_2314_);
v___x_2320_ = lean_apply_4(v_handler_2311_, v_a_2317_, v_a_2319_, v___y_2314_, lean_box(0));
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2344_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2344_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2344_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_fst_2325_; lean_object* v_snd_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2343_; 
v_fst_2325_ = lean_ctor_get(v_a_2321_, 0);
v_snd_2326_ = lean_ctor_get(v_a_2321_, 1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_a_2321_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2328_ = v_a_2321_;
v_isShared_2329_ = v_isSharedCheck_2343_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_snd_2326_);
lean_inc(v_fst_2325_);
lean_dec(v_a_2321_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2343_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_response_2330_; uint8_t v_isComplete_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v_response_2330_ = lean_ctor_get(v_fst_2325_, 0);
lean_inc(v_response_2330_);
v_isComplete_2331_ = lean_ctor_get_uint8(v_fst_2325_, sizeof(void*)*1);
lean_dec(v_fst_2325_);
v___x_2332_ = l_Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(v_response_2330_);
lean_inc(v___x_2332_);
v___x_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
v___x_2334_ = l_Lean_Json_compress(v___x_2332_);
v___x_2335_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2335_, 0, v___x_2333_);
lean_ctor_set(v___x_2335_, 1, v___x_2334_);
lean_ctor_set_uint8(v___x_2335_, sizeof(void*)*2, v_isComplete_2331_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v_inst_2310_);
v___x_2337_ = v___x_2328_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_inst_2310_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_snd_2326_);
v___x_2337_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2335_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2338_);
v___x_2340_ = v___x_2323_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_inst_2310_);
v_a_2345_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2320_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2320_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec(v_a_2317_);
lean_dec_ref(v_handler_2311_);
lean_dec(v_inst_2310_);
v_a_2353_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2318_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2318_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec_ref(v_handler_2311_);
lean_dec(v_inst_2310_);
v_a_2361_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2316_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2316_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed(lean_object* v_method_2369_, lean_object* v_inst_2370_, lean_object* v_handler_2371_, lean_object* v_param_2372_, lean_object* v_state_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(v_method_2369_, v_inst_2370_, v_handler_2371_, v_param_2372_, v_state_2373_, v___y_2374_);
lean_dec_ref(v___y_2374_);
lean_dec(v_state_2373_);
lean_dec_ref(v_method_2369_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(lean_object* v___f_2377_, lean_object* v___f_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_st_ref_get(v___y_2379_);
v___x_2383_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_2382_, v___f_2377_, v___y_2380_);
if (lean_obj_tag(v___x_2383_) == 0)
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2393_; 
v_a_2384_ = lean_ctor_get(v___x_2383_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v___x_2383_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2386_ = v___x_2383_;
v_isShared_2387_ = v_isSharedCheck_2393_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2383_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2393_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2391_; 
lean_inc(v_a_2384_);
v___x_2388_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2378_, v_a_2384_);
v___x_2389_ = lean_st_ref_swap(v___y_2379_, v___x_2388_);
lean_dec(v___x_2389_);
if (v_isShared_2387_ == 0)
{
v___x_2391_ = v___x_2386_;
goto v_reusejp_2390_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_a_2384_);
v___x_2391_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2390_;
}
v_reusejp_2390_:
{
return v___x_2391_;
}
}
}
else
{
lean_dec_ref(v___f_2378_);
return v___x_2383_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed(lean_object* v___f_2394_, lean_object* v___f_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(v___f_2394_, v___f_2395_, v___y_2396_, v___y_2397_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(lean_object* v_val_2400_, lean_object* v___f_2401_, lean_object* v_param_2402_, lean_object* v_x_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = lean_st_ref_get(v_val_2400_);
lean_inc_ref(v___y_2404_);
v___x_2407_ = lean_apply_4(v___f_2401_, v_param_2402_, v___x_2406_, v___y_2404_, lean_box(0));
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2418_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2410_ = v___x_2407_;
v_isShared_2411_ = v_isSharedCheck_2418_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_a_2408_);
lean_dec(v___x_2407_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2418_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v_fst_2412_; lean_object* v_snd_2413_; lean_object* v___x_2414_; lean_object* v___x_2416_; 
v_fst_2412_ = lean_ctor_get(v_a_2408_, 0);
lean_inc(v_fst_2412_);
v_snd_2413_ = lean_ctor_get(v_a_2408_, 1);
lean_inc(v_snd_2413_);
lean_dec(v_a_2408_);
v___x_2414_ = lean_st_ref_swap(v_val_2400_, v_snd_2413_);
lean_dec(v___x_2414_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 0, v_fst_2412_);
v___x_2416_ = v___x_2410_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_fst_2412_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
v_a_2419_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2407_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2407_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed(lean_object* v_val_2427_, lean_object* v___f_2428_, lean_object* v_param_2429_, lean_object* v_x_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(v_val_2427_, v___f_2428_, v_param_2429_, v_x_2430_, v___y_2431_);
lean_dec_ref(v___y_2431_);
lean_dec(v_val_2427_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(lean_object* v_val_2434_, lean_object* v___f_2435_, lean_object* v___f_2436_, lean_object* v_val_2437_, lean_object* v_param_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___f_2441_; lean_object* v___f_2442_; lean_object* v___x_2443_; 
v___f_2441_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_2441_, 0, v_val_2434_);
lean_closure_set(v___f_2441_, 1, v___f_2435_);
lean_closure_set(v___f_2441_, 2, v_param_2438_);
v___f_2442_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_2442_, 0, v___f_2441_);
lean_closure_set(v___f_2442_, 1, v___f_2436_);
v___x_2443_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_2437_, v___f_2442_, v___y_2439_);
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed(lean_object* v_val_2444_, lean_object* v___f_2445_, lean_object* v___f_2446_, lean_object* v_val_2447_, lean_object* v_param_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(v_val_2444_, v___f_2445_, v___f_2446_, v_val_2447_, v_param_2448_, v___y_2449_);
lean_dec_ref(v___y_2449_);
return v_res_2451_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_box(0);
v___x_2460_ = lean_task_pure(v___x_2459_);
return v___x_2460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_method_2461_, lean_object* v_completeness_2462_, lean_object* v_inst_2463_, lean_object* v_initState_2464_, lean_object* v_handler_2465_, lean_object* v_onDidChange_2466_){
_start:
{
lean_object* v___f_2468_; lean_object* v___f_2469_; lean_object* v___f_2470_; uint8_t v___x_2471_; 
v___f_2468_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc_n(v_inst_2463_, 2);
lean_inc_ref_n(v_method_2461_, 2);
v___f_2469_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_2469_, 0, v_method_2461_);
lean_closure_set(v___f_2469_, 1, v_inst_2463_);
lean_closure_set(v___f_2469_, 2, v_handler_2465_);
v___f_2470_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_2470_, 0, v_method_2461_);
lean_closure_set(v___f_2470_, 1, v_inst_2463_);
lean_closure_set(v___f_2470_, 2, v_onDidChange_2466_);
v___x_2471_ = l_Lean_initializing();
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; 
lean_dec_ref(v___f_2470_);
lean_dec_ref(v___f_2469_);
lean_dec(v_initState_2464_);
lean_dec(v_inst_2463_);
lean_dec(v_completeness_2462_);
v___x_2472_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2473_ = lean_string_append(v___x_2472_, v_method_2461_);
lean_dec_ref(v_method_2461_);
v___x_2474_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2));
v___x_2475_ = lean_string_append(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_mk_io_user_error(v___x_2475_);
v___x_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2476_);
return v___x_2477_;
}
else
{
lean_object* v___x_2478_; lean_object* v___f_2479_; lean_object* v___f_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___f_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2478_ = lean_box(0);
v___f_2479_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3));
v___f_2480_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4));
v___x_2481_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5);
v___x_2482_ = l_Std_Mutex_new___redArg(v___x_2481_);
v___x_2483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2483_, 0, v_inst_2463_);
lean_ctor_set(v___x_2483_, 1, v_initState_2464_);
lean_inc_ref(v___x_2483_);
v___x_2484_ = lean_st_mk_ref(v___x_2483_);
lean_inc_ref_n(v___x_2482_, 2);
lean_inc_ref(v___f_2469_);
lean_inc_n(v___x_2484_, 2);
v___f_2485_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2485_, 0, v___x_2484_);
lean_closure_set(v___f_2485_, 1, v___f_2469_);
lean_closure_set(v___f_2485_, 2, v___f_2479_);
lean_closure_set(v___f_2485_, 3, v___x_2482_);
lean_inc_ref(v___f_2470_);
v___f_2486_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_2486_, 0, v___x_2484_);
lean_closure_set(v___f_2486_, 1, v___f_2470_);
lean_closure_set(v___f_2486_, 2, v___x_2478_);
lean_closure_set(v___f_2486_, 3, v___f_2480_);
lean_closure_set(v___f_2486_, 4, v___x_2482_);
v___x_2487_ = l_Lean_Server_statefulRequestHandlers;
v___x_2488_ = lean_st_ref_take(v___x_2487_);
v___x_2489_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2489_, 0, v___f_2468_);
lean_ctor_set(v___x_2489_, 1, v___f_2469_);
lean_ctor_set(v___x_2489_, 2, v___f_2485_);
lean_ctor_set(v___x_2489_, 3, v___f_2470_);
lean_ctor_set(v___x_2489_, 4, v___f_2486_);
lean_ctor_set(v___x_2489_, 5, v___x_2482_);
lean_ctor_set(v___x_2489_, 6, v___x_2483_);
lean_ctor_set(v___x_2489_, 7, v___x_2484_);
lean_ctor_set(v___x_2489_, 8, v_completeness_2462_);
v___x_2490_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v___x_2488_, v_method_2461_, v___x_2489_);
v___x_2491_ = lean_st_ref_put(v___x_2487_, v___x_2490_);
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
return v___x_2492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_method_2493_, lean_object* v_completeness_2494_, lean_object* v_inst_2495_, lean_object* v_initState_2496_, lean_object* v_handler_2497_, lean_object* v_onDidChange_2498_, lean_object* v_a_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2493_, v_completeness_2494_, v_inst_2495_, v_initState_2496_, v_handler_2497_, v_onDidChange_2498_);
return v_res_2500_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_2501_, lean_object* v_i_2502_, lean_object* v_k_2503_){
_start:
{
lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2504_ = lean_array_get_size(v_keys_2501_);
v___x_2505_ = lean_nat_dec_lt(v_i_2502_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_dec(v_i_2502_);
return v___x_2505_;
}
else
{
lean_object* v_k_x27_2506_; uint8_t v___x_2507_; 
v_k_x27_2506_ = lean_array_fget_borrowed(v_keys_2501_, v_i_2502_);
v___x_2507_ = lean_string_dec_eq(v_k_2503_, v_k_x27_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_unsigned_to_nat(1u);
v___x_2509_ = lean_nat_add(v_i_2502_, v___x_2508_);
lean_dec(v_i_2502_);
v_i_2502_ = v___x_2509_;
goto _start;
}
else
{
lean_dec(v_i_2502_);
return v___x_2505_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_2511_, lean_object* v_i_2512_, lean_object* v_k_2513_){
_start:
{
uint8_t v_res_2514_; lean_object* v_r_2515_; 
v_res_2514_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2511_, v_i_2512_, v_k_2513_);
lean_dec_ref(v_k_2513_);
lean_dec_ref(v_keys_2511_);
v_r_2515_ = lean_box(v_res_2514_);
return v_r_2515_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2516_, size_t v_x_2517_, lean_object* v_x_2518_){
_start:
{
if (lean_obj_tag(v_x_2516_) == 0)
{
lean_object* v_es_2519_; lean_object* v___x_2520_; size_t v___x_2521_; size_t v___x_2522_; lean_object* v_j_2523_; lean_object* v___x_2524_; 
v_es_2519_ = lean_ctor_get(v_x_2516_, 0);
v___x_2520_ = lean_box(2);
v___x_2521_ = ((size_t)31ULL);
v___x_2522_ = lean_usize_land(v_x_2517_, v___x_2521_);
v_j_2523_ = lean_usize_to_nat(v___x_2522_);
v___x_2524_ = lean_array_get_borrowed(v___x_2520_, v_es_2519_, v_j_2523_);
lean_dec(v_j_2523_);
switch(lean_obj_tag(v___x_2524_))
{
case 0:
{
lean_object* v_key_2525_; uint8_t v___x_2526_; 
v_key_2525_ = lean_ctor_get(v___x_2524_, 0);
v___x_2526_ = lean_string_dec_eq(v_x_2518_, v_key_2525_);
return v___x_2526_;
}
case 1:
{
lean_object* v_node_2527_; size_t v___x_2528_; size_t v___x_2529_; 
v_node_2527_ = lean_ctor_get(v___x_2524_, 0);
v___x_2528_ = ((size_t)5ULL);
v___x_2529_ = lean_usize_shift_right(v_x_2517_, v___x_2528_);
v_x_2516_ = v_node_2527_;
v_x_2517_ = v___x_2529_;
goto _start;
}
default: 
{
uint8_t v___x_2531_; 
v___x_2531_ = 0;
return v___x_2531_;
}
}
}
else
{
lean_object* v_ks_2532_; lean_object* v___x_2533_; uint8_t v___x_2534_; 
v_ks_2532_ = lean_ctor_get(v_x_2516_, 0);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_2532_, v___x_2533_, v_x_2518_);
return v___x_2534_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_2535_, lean_object* v_x_2536_, lean_object* v_x_2537_){
_start:
{
size_t v_x_3340__boxed_2538_; uint8_t v_res_2539_; lean_object* v_r_2540_; 
v_x_3340__boxed_2538_ = lean_unbox_usize(v_x_2536_);
lean_dec(v_x_2536_);
v_res_2539_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2535_, v_x_3340__boxed_2538_, v_x_2537_);
lean_dec_ref(v_x_2537_);
lean_dec_ref(v_x_2535_);
v_r_2540_ = lean_box(v_res_2539_);
return v_r_2540_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_2541_, lean_object* v_x_2542_){
_start:
{
uint64_t v___x_2543_; size_t v___x_2544_; uint8_t v___x_2545_; 
v___x_2543_ = lean_string_hash(v_x_2542_);
v___x_2544_ = lean_uint64_to_usize(v___x_2543_);
v___x_2545_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2541_, v___x_2544_, v_x_2542_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2546_, lean_object* v_x_2547_){
_start:
{
uint8_t v_res_2548_; lean_object* v_r_2549_; 
v_res_2548_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2546_, v_x_2547_);
lean_dec_ref(v_x_2547_);
lean_dec_ref(v_x_2546_);
v_r_2549_ = lean_box(v_res_2548_);
return v_r_2549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_method_2551_, lean_object* v_completeness_2552_, lean_object* v_inst_2553_, lean_object* v_initState_2554_, lean_object* v_handler_2555_, lean_object* v_onDidChange_2556_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; 
v___x_2558_ = l_Lean_Server_requestHandlers;
v___x_2559_ = lean_st_ref_get(v___x_2558_);
v___x_2560_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_2559_, v_method_2551_);
lean_dec(v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2561_; 
v___x_2561_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2551_, v_completeness_2552_, v_inst_2553_, v_initState_2554_, v_handler_2555_, v_onDidChange_2556_);
return v___x_2561_;
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec_ref(v_onDidChange_2556_);
lean_dec_ref(v_handler_2555_);
lean_dec(v_initState_2554_);
lean_dec(v_inst_2553_);
lean_dec(v_completeness_2552_);
v___x_2562_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2563_ = lean_string_append(v___x_2562_, v_method_2551_);
lean_dec_ref(v_method_2551_);
v___x_2564_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_2565_ = lean_string_append(v___x_2563_, v___x_2564_);
v___x_2566_ = lean_mk_io_user_error(v___x_2565_);
v___x_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
return v___x_2567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_method_2568_, lean_object* v_completeness_2569_, lean_object* v_inst_2570_, lean_object* v_initState_2571_, lean_object* v_handler_2572_, lean_object* v_onDidChange_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2568_, v_completeness_2569_, v_inst_2570_, v_initState_2571_, v_handler_2572_, v_onDidChange_2573_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(lean_object* v_method_2576_, lean_object* v_refreshMethod_2577_, lean_object* v_refreshIntervalMs_2578_, lean_object* v_inst_2579_, lean_object* v_initState_2580_, lean_object* v_handler_2581_, lean_object* v_onDidChange_2582_){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2584_, 0, v_refreshMethod_2577_);
lean_ctor_set(v___x_2584_, 1, v_refreshIntervalMs_2578_);
v___x_2585_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2576_, v___x_2584_, v_inst_2579_, v_initState_2580_, v_handler_2581_, v_onDidChange_2582_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_method_2586_, lean_object* v_refreshMethod_2587_, lean_object* v_refreshIntervalMs_2588_, lean_object* v_inst_2589_, lean_object* v_initState_2590_, lean_object* v_handler_2591_, lean_object* v_onDidChange_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2586_, v_refreshMethod_2587_, v_refreshIntervalMs_2588_, v_inst_2589_, v_initState_2590_, v_handler_2591_, v_onDidChange_2592_);
return v_res_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2600_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_));
v___x_2601_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2602_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2603_ = lean_unsigned_to_nat(500u);
v___x_2604_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init));
v___x_2605_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2606_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2607_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v___x_2601_, v___x_2602_, v___x_2603_, v___x_2600_, v___x_2604_, v___x_2605_, v___x_2606_);
return v___x_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2____boxed(lean_object* v_a_2608_){
_start:
{
lean_object* v_res_2609_; 
v_res_2609_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
return v_res_2609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(lean_object* v_method_2610_, lean_object* v_refreshMethod_2611_, lean_object* v_refreshIntervalMs_2612_, lean_object* v_stateType_2613_, lean_object* v_inst_2614_, lean_object* v_initState_2615_, lean_object* v_handler_2616_, lean_object* v_onDidChange_2617_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2610_, v_refreshMethod_2611_, v_refreshIntervalMs_2612_, v_inst_2614_, v_initState_2615_, v_handler_2616_, v_onDidChange_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2620_, lean_object* v_refreshMethod_2621_, lean_object* v_refreshIntervalMs_2622_, lean_object* v_stateType_2623_, lean_object* v_inst_2624_, lean_object* v_initState_2625_, lean_object* v_handler_2626_, lean_object* v_onDidChange_2627_, lean_object* v_a_2628_){
_start:
{
lean_object* v_res_2629_; 
v_res_2629_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(v_method_2620_, v_refreshMethod_2621_, v_refreshIntervalMs_2622_, v_stateType_2623_, v_inst_2624_, v_initState_2625_, v_handler_2626_, v_onDidChange_2627_);
return v_res_2629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_2630_, lean_object* v_completeness_2631_, lean_object* v_stateType_2632_, lean_object* v_inst_2633_, lean_object* v_initState_2634_, lean_object* v_handler_2635_, lean_object* v_onDidChange_2636_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2630_, v_completeness_2631_, v_inst_2633_, v_initState_2634_, v_handler_2635_, v_onDidChange_2636_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_method_2639_, lean_object* v_completeness_2640_, lean_object* v_stateType_2641_, lean_object* v_inst_2642_, lean_object* v_initState_2643_, lean_object* v_handler_2644_, lean_object* v_onDidChange_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(v_method_2639_, v_completeness_2640_, v_stateType_2641_, v_inst_2642_, v_initState_2643_, v_handler_2644_, v_onDidChange_2645_);
return v_res_2647_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2648_, lean_object* v_x_2649_, lean_object* v_x_2650_){
_start:
{
uint8_t v___x_2651_; 
v___x_2651_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2649_, v_x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2652_, lean_object* v_x_2653_, lean_object* v_x_2654_){
_start:
{
uint8_t v_res_2655_; lean_object* v_r_2656_; 
v_res_2655_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2652_, v_x_2653_, v_x_2654_);
lean_dec_ref(v_x_2654_);
lean_dec_ref(v_x_2653_);
v_r_2656_ = lean_box(v_res_2655_);
return v_r_2656_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b1_2657_, lean_object* v_00_u03b2_2658_, lean_object* v_mutex_2659_, lean_object* v_k_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2659_, v_k_2660_, v___y_2661_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2664_, lean_object* v_00_u03b2_2665_, lean_object* v_mutex_2666_, lean_object* v_k_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v_res_2670_; 
v_res_2670_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(v_00_u03b1_2664_, v_00_u03b2_2665_, v_mutex_2666_, v_k_2667_, v___y_2668_);
lean_dec_ref(v___y_2668_);
return v_res_2670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_method_2671_, lean_object* v_completeness_2672_, lean_object* v_stateType_2673_, lean_object* v_inst_2674_, lean_object* v_initState_2675_, lean_object* v_handler_2676_, lean_object* v_onDidChange_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2671_, v_completeness_2672_, v_inst_2674_, v_initState_2675_, v_handler_2676_, v_onDidChange_2677_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_method_2680_, lean_object* v_completeness_2681_, lean_object* v_stateType_2682_, lean_object* v_inst_2683_, lean_object* v_initState_2684_, lean_object* v_handler_2685_, lean_object* v_onDidChange_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_method_2680_, v_completeness_2681_, v_stateType_2682_, v_inst_2683_, v_initState_2684_, v_handler_2685_, v_onDidChange_2686_);
return v_res_2688_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2689_, lean_object* v_x_2690_, size_t v_x_2691_, lean_object* v_x_2692_){
_start:
{
uint8_t v___x_2693_; 
v___x_2693_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2690_, v_x_2691_, v_x_2692_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2694_, lean_object* v_x_2695_, lean_object* v_x_2696_, lean_object* v_x_2697_){
_start:
{
size_t v_x_3504__boxed_2698_; uint8_t v_res_2699_; lean_object* v_r_2700_; 
v_x_3504__boxed_2698_ = lean_unbox_usize(v_x_2696_);
lean_dec(v_x_2696_);
v_res_2699_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2694_, v_x_2695_, v_x_3504__boxed_2698_, v_x_2697_);
lean_dec_ref(v_x_2697_);
lean_dec_ref(v_x_2695_);
v_r_2700_ = lean_box(v_res_2699_);
return v_r_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_params_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v___x_2704_; 
v___x_2704_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2701_);
return v___x_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_params_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_res_2708_; 
v_res_2708_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_params_2705_, v_a_2706_);
lean_dec_ref(v_a_2706_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_, lean_object* v_x_2712_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v_x_2710_, v_x_2711_, v_x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2714_, lean_object* v_keys_2715_, lean_object* v_vals_2716_, lean_object* v_heq_2717_, lean_object* v_i_2718_, lean_object* v_k_2719_){
_start:
{
uint8_t v___x_2720_; 
v___x_2720_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2715_, v_i_2718_, v_k_2719_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2721_, lean_object* v_keys_2722_, lean_object* v_vals_2723_, lean_object* v_heq_2724_, lean_object* v_i_2725_, lean_object* v_k_2726_){
_start:
{
uint8_t v_res_2727_; lean_object* v_r_2728_; 
v_res_2727_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_2721_, v_keys_2722_, v_vals_2723_, v_heq_2724_, v_i_2725_, v_k_2726_);
lean_dec_ref(v_k_2726_);
lean_dec_ref(v_vals_2723_);
lean_dec_ref(v_keys_2722_);
v_r_2728_ = lean_box(v_res_2727_);
return v_r_2728_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_2729_, lean_object* v_x_2730_, size_t v_x_2731_, size_t v_x_2732_, lean_object* v_x_2733_, lean_object* v_x_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_2730_, v_x_2731_, v_x_2732_, v_x_2733_, v_x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_, lean_object* v_x_2741_){
_start:
{
size_t v_x_3530__boxed_2742_; size_t v_x_3531__boxed_2743_; lean_object* v_res_2744_; 
v_x_3530__boxed_2742_ = lean_unbox_usize(v_x_2738_);
lean_dec(v_x_2738_);
v_x_3531__boxed_2743_ = lean_unbox_usize(v_x_2739_);
lean_dec(v_x_2739_);
v_res_2744_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(v_00_u03b2_2736_, v_x_2737_, v_x_3530__boxed_2742_, v_x_3531__boxed_2743_, v_x_2740_, v_x_2741_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_2745_, lean_object* v_n_2746_, lean_object* v_k_2747_, lean_object* v_v_2748_){
_start:
{
lean_object* v___x_2749_; 
v___x_2749_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v_n_2746_, v_k_2747_, v_v_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(lean_object* v_00_u03b2_2750_, size_t v_depth_2751_, lean_object* v_keys_2752_, lean_object* v_vals_2753_, lean_object* v_heq_2754_, lean_object* v_i_2755_, lean_object* v_entries_2756_){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_2751_, v_keys_2752_, v_vals_2753_, v_i_2755_, v_entries_2756_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___boxed(lean_object* v_00_u03b2_2758_, lean_object* v_depth_2759_, lean_object* v_keys_2760_, lean_object* v_vals_2761_, lean_object* v_heq_2762_, lean_object* v_i_2763_, lean_object* v_entries_2764_){
_start:
{
size_t v_depth_boxed_2765_; lean_object* v_res_2766_; 
v_depth_boxed_2765_ = lean_unbox_usize(v_depth_2759_);
lean_dec(v_depth_2759_);
v_res_2766_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(v_00_u03b2_2758_, v_depth_boxed_2765_, v_keys_2760_, v_vals_2761_, v_heq_2762_, v_i_2763_, v_entries_2764_);
lean_dec_ref(v_vals_2761_);
lean_dec_ref(v_keys_2760_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_2767_, lean_object* v_x_2768_, lean_object* v_x_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_x_2768_, v_x_2769_, v_x_2770_, v_x_2771_);
return v___x_2772_;
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
