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
lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f(lean_object*);
lean_object* l_Lean_Elab_InlayHint_resolveDeferred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
lean_object* l_Lean_Server_Snapshots_Snapshot_infoTree(lean_object*);
lean_object* l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Info_updateContext_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toList___redArg(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Server_instInhabitedRequestError_default;
lean_object* l_instInhabitedEIO___aux__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* l_Lean_FileMap_utf8PosToLspPos(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unexpected context-free info tree node"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__2_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "_private.Lean.Elab.InfoTree.Util.0.Lean.Elab.InfoTree.visitM.go"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__1_value;
static const lean_string_object l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Elab.InfoTree.Util"};
static const lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Server_FileWorker_handleInlayHints___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Lean.Server.FileWorker.handleInlayHints"};
static const lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_handleInlayHints___closed__0_value;
static const lean_string_object l_Lean_Server_FileWorker_handleInlayHints___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 399, .m_capacity = 399, .m_length = 398, .m_data = "assertion violation: finishedSnaps >= oldFinishedSnaps\n  -- VS Code emits inlay hint requests *every time the user scrolls*. This is reasonably expensive,\n  -- so in addition to re-using old inlay hints from parts of the file that haven't been processed\n  -- yet, we also re-use old inlay hints from parts of the file that have been processed already\n  -- with the current state of the document.\n  "};
static const lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__1 = (const lean_object*)&l_Lean_Server_FileWorker_handleInlayHints___closed__1_value;
static lean_once_cell_t l_Lean_Server_FileWorker_handleInlayHints___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_handleInlayHints___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_ctor_set(v___x_223_, 2, v___y_215_);
lean_ctor_set(v___x_223_, 3, v___y_216_);
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
v___y_215_ = v___y_228_;
v___y_216_ = v___x_232_;
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
v___y_215_ = v___y_228_;
v___y_216_ = v___x_232_;
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
lean_object* v_val_534_; lean_object* v_module_535_; lean_object* v_range_536_; uint8_t v___x_537_; 
v_val_534_ = lean_ctor_get(v_location_x3f_533_, 0);
v_module_535_ = lean_ctor_get(v_val_534_, 0);
v_range_536_ = lean_ctor_get(v_val_534_, 1);
v___x_537_ = lean_name_eq(v_module_535_, v_hintMod_522_);
if (v___x_537_ == 0)
{
goto v___jp_527_;
}
else
{
uint8_t v___x_538_; 
v___x_538_ = l_Lean_Syntax_Range_overlaps(v_range_523_, v_range_536_, v___x_537_, v___x_531_);
if (v___x_538_ == 0)
{
goto v___jp_527_;
}
else
{
return v___x_538_;
}
}
}
}
else
{
uint8_t v___x_539_; 
v___x_539_ = 0;
return v___x_539_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5___boxed(lean_object* v_hintMod_540_, lean_object* v_range_541_, lean_object* v_as_542_, lean_object* v_i_543_, lean_object* v_stop_544_){
_start:
{
size_t v_i_boxed_545_; size_t v_stop_boxed_546_; uint8_t v_res_547_; lean_object* v_r_548_; 
v_i_boxed_545_ = lean_unbox_usize(v_i_543_);
lean_dec(v_i_543_);
v_stop_boxed_546_ = lean_unbox_usize(v_stop_544_);
lean_dec(v_stop_544_);
v_res_547_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_540_, v_range_541_, v_as_542_, v_i_boxed_545_, v_stop_boxed_546_);
lean_dec_ref(v_as_542_);
lean_dec_ref(v_range_541_);
lean_dec(v_hintMod_540_);
v_r_548_ = lean_box(v_res_547_);
return v_r_548_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(lean_object* v_range_549_, uint8_t v___x_550_, lean_object* v_as_551_, size_t v_i_552_, size_t v_stop_553_){
_start:
{
uint8_t v___x_554_; 
v___x_554_ = lean_usize_dec_eq(v_i_552_, v_stop_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v_range_556_; uint8_t v___x_557_; uint8_t v___x_558_; 
v___x_555_ = lean_array_uget_borrowed(v_as_551_, v_i_552_);
v_range_556_ = lean_ctor_get(v___x_555_, 0);
v___x_557_ = 1;
v___x_558_ = l_Lean_Syntax_Range_overlaps(v_range_549_, v_range_556_, v___x_557_, v___x_550_);
if (v___x_558_ == 0)
{
size_t v___x_559_; size_t v___x_560_; 
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_i_552_, v___x_559_);
v_i_552_ = v___x_560_;
goto _start;
}
else
{
return v___x_557_;
}
}
else
{
uint8_t v___x_562_; 
v___x_562_ = 0;
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4___boxed(lean_object* v_range_563_, lean_object* v___x_564_, lean_object* v_as_565_, lean_object* v_i_566_, lean_object* v_stop_567_){
_start:
{
uint8_t v___x_2536__boxed_568_; size_t v_i_boxed_569_; size_t v_stop_boxed_570_; uint8_t v_res_571_; lean_object* v_r_572_; 
v___x_2536__boxed_568_ = lean_unbox(v___x_564_);
v_i_boxed_569_ = lean_unbox_usize(v_i_566_);
lean_dec(v_i_566_);
v_stop_boxed_570_ = lean_unbox_usize(v_stop_567_);
lean_dec(v_stop_567_);
v_res_571_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_563_, v___x_2536__boxed_568_, v_as_565_, v_i_boxed_569_, v_stop_boxed_570_);
lean_dec_ref(v_as_565_);
lean_dec_ref(v_range_563_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f(lean_object* v_hintMod_573_, lean_object* v_ihi_574_, lean_object* v_range_575_, lean_object* v_newText_576_){
_start:
{
lean_object* v_position_577_; lean_object* v_label_578_; lean_object* v_kind_x3f_579_; lean_object* v_textEdits_580_; lean_object* v_tooltip_x3f_581_; uint8_t v_paddingLeft_582_; uint8_t v_paddingRight_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_667_; 
v_position_577_ = lean_ctor_get(v_ihi_574_, 0);
v_label_578_ = lean_ctor_get(v_ihi_574_, 1);
v_kind_x3f_579_ = lean_ctor_get(v_ihi_574_, 2);
v_textEdits_580_ = lean_ctor_get(v_ihi_574_, 3);
v_tooltip_x3f_581_ = lean_ctor_get(v_ihi_574_, 4);
v_paddingLeft_582_ = lean_ctor_get_uint8(v_ihi_574_, sizeof(void*)*5);
v_paddingRight_583_ = lean_ctor_get_uint8(v_ihi_574_, sizeof(void*)*5 + 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v_ihi_574_);
if (v_isSharedCheck_667_ == 0)
{
v___x_585_ = v_ihi_574_;
v_isShared_586_ = v_isSharedCheck_667_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_tooltip_x3f_581_);
lean_inc(v_textEdits_580_);
lean_inc(v_kind_x3f_579_);
lean_inc(v_label_578_);
lean_inc(v_position_577_);
lean_dec(v_ihi_574_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_667_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___y_588_; lean_object* v___y_589_; lean_object* v___y_590_; lean_object* v___y_599_; lean_object* v___y_600_; uint8_t v___y_613_; uint8_t v___y_648_; 
if (lean_obj_tag(v_label_578_) == 0)
{
uint8_t v___x_659_; 
v___x_659_ = 0;
v___y_648_ = v___x_659_;
goto v___jp_647_;
}
else
{
lean_object* v_p_660_; lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
v_p_660_ = lean_ctor_get(v_label_578_, 0);
v___x_661_ = lean_unsigned_to_nat(0u);
v___x_662_ = lean_array_get_size(v_p_660_);
v___x_663_ = lean_nat_dec_lt(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
v___y_648_ = v___x_663_;
goto v___jp_647_;
}
else
{
if (v___x_663_ == 0)
{
v___y_648_ = v___x_663_;
goto v___jp_647_;
}
else
{
size_t v___x_664_; size_t v___x_665_; uint8_t v___x_666_; 
v___x_664_ = ((size_t)0ULL);
v___x_665_ = lean_usize_of_nat(v___x_662_);
v___x_666_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__5(v_hintMod_573_, v_range_575_, v_p_660_, v___x_664_, v___x_665_);
v___y_648_ = v___x_666_;
goto v___jp_647_;
}
}
}
v___jp_587_:
{
size_t v_sz_591_; size_t v___x_592_; lean_object* v___x_593_; lean_object* v___x_595_; 
v_sz_591_ = lean_array_size(v_textEdits_580_);
v___x_592_ = ((size_t)0ULL);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_575_, v___y_588_, v_sz_591_, v___x_592_, v_textEdits_580_);
lean_dec(v___y_588_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 3, v___x_593_);
lean_ctor_set(v___x_585_, 1, v___y_590_);
lean_ctor_set(v___x_585_, 0, v___y_589_);
v___x_595_ = v___x_585_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v___y_589_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v___y_590_);
lean_ctor_set(v_reuseFailAlloc_597_, 2, v_kind_x3f_579_);
lean_ctor_set(v_reuseFailAlloc_597_, 3, v___x_593_);
lean_ctor_set(v_reuseFailAlloc_597_, 4, v_tooltip_x3f_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_597_, sizeof(void*)*5, v_paddingLeft_582_);
lean_ctor_set_uint8(v_reuseFailAlloc_597_, sizeof(void*)*5 + 1, v_paddingRight_583_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
return v___x_596_;
}
}
v___jp_598_:
{
if (lean_obj_tag(v_label_578_) == 0)
{
v___y_588_ = v___y_599_;
v___y_589_ = v___y_600_;
v___y_590_ = v_label_578_;
goto v___jp_587_;
}
else
{
lean_object* v_p_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_611_; 
v_p_601_ = lean_ctor_get(v_label_578_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v_label_578_);
if (v_isSharedCheck_611_ == 0)
{
v___x_603_ = v_label_578_;
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_p_601_);
lean_dec(v_label_578_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_611_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
size_t v_sz_605_; size_t v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v_sz_605_ = lean_array_size(v_p_601_);
v___x_606_ = ((size_t)0ULL);
lean_inc_ref(v_range_575_);
v___x_607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_573_, v_range_575_, v___y_599_, v_sz_605_, v___x_606_, v_p_601_);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_607_);
v___x_609_ = v___x_603_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v___x_607_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
v___y_588_ = v___y_599_;
v___y_589_ = v___y_600_;
v___y_590_ = v___x_609_;
goto v___jp_587_;
}
}
}
}
v___jp_612_:
{
if (v___y_613_ == 0)
{
lean_object* v_start_614_; lean_object* v_stop_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_byteOffset_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_start_614_ = lean_ctor_get(v_range_575_, 0);
v_stop_615_ = lean_ctor_get(v_range_575_, 1);
v___x_616_ = lean_string_utf8_byte_size(v_newText_576_);
v___x_617_ = lean_nat_to_int(v___x_616_);
v___x_618_ = l_Lean_Syntax_Range_bsize(v_range_575_);
v___x_619_ = lean_nat_to_int(v___x_618_);
v_byteOffset_620_ = lean_int_sub(v___x_617_, v___x_619_);
lean_dec(v___x_619_);
lean_dec(v___x_617_);
v___x_621_ = lean_unsigned_to_nat(1u);
v___x_622_ = lean_nat_add(v_stop_615_, v___x_621_);
v___x_623_ = lean_nat_dec_le(v___x_622_, v_position_577_);
lean_dec(v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_624_ = lean_nat_add(v_position_577_, v___x_621_);
v___x_625_ = lean_nat_dec_le(v___x_624_, v_start_614_);
lean_dec(v___x_624_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__1));
v___x_628_ = lean_unsigned_to_nat(87u);
v___x_629_ = lean_unsigned_to_nat(6u);
v___x_630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__2));
v___x_631_ = l_Nat_reprFast(v_position_577_);
v___x_632_ = lean_string_append(v___x_630_, v___x_631_);
lean_dec_ref(v___x_631_);
v___x_633_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__3));
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
lean_inc(v_start_614_);
v___x_635_ = l_Nat_reprFast(v_start_614_);
v___x_636_ = lean_string_append(v___x_634_, v___x_635_);
lean_dec_ref(v___x_635_);
v___x_637_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__4));
v___x_638_ = lean_string_append(v___x_636_, v___x_637_);
lean_inc(v_stop_615_);
v___x_639_ = l_Nat_reprFast(v_stop_615_);
v___x_640_ = lean_string_append(v___x_638_, v___x_639_);
lean_dec_ref(v___x_639_);
v___x_641_ = l_mkPanicMessageWithDecl(v___x_626_, v___x_627_, v___x_628_, v___x_629_, v___x_640_);
lean_dec_ref(v___x_640_);
v___x_642_ = l_panic___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__1(v___x_641_);
v___y_599_ = v_byteOffset_620_;
v___y_600_ = v___x_642_;
goto v___jp_598_;
}
else
{
v___y_599_ = v_byteOffset_620_;
v___y_600_ = v_position_577_;
goto v___jp_598_;
}
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_643_ = lean_nat_to_int(v_position_577_);
v___x_644_ = lean_int_add(v___x_643_, v_byteOffset_620_);
lean_dec(v___x_643_);
v___x_645_ = l_Int_toNat(v___x_644_);
lean_dec(v___x_644_);
v___y_599_ = v_byteOffset_620_;
v___y_600_ = v___x_645_;
goto v___jp_598_;
}
}
else
{
lean_object* v___x_646_; 
lean_del_object(v___x_585_);
lean_dec(v_tooltip_x3f_581_);
lean_dec_ref(v_textEdits_580_);
lean_dec(v_kind_x3f_579_);
lean_dec_ref(v_label_578_);
lean_dec(v_position_577_);
lean_dec_ref(v_range_575_);
v___x_646_ = lean_box(0);
return v___x_646_;
}
}
v___jp_647_:
{
uint8_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 1;
v___x_650_ = l_Lean_Syntax_Range_contains(v_range_575_, v_position_577_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_array_get_size(v_textEdits_580_);
v___x_653_ = lean_nat_dec_lt(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
v___y_613_ = v___y_648_;
goto v___jp_612_;
}
else
{
if (v___x_653_ == 0)
{
v___y_613_ = v___y_648_;
goto v___jp_612_;
}
else
{
size_t v___x_654_; size_t v___x_655_; uint8_t v___x_656_; 
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_652_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__4(v_range_575_, v___x_650_, v_textEdits_580_, v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
v___y_613_ = v___y_648_;
goto v___jp_612_;
}
else
{
lean_object* v___x_657_; 
lean_del_object(v___x_585_);
lean_dec(v_tooltip_x3f_581_);
lean_dec_ref(v_textEdits_580_);
lean_dec(v_kind_x3f_579_);
lean_dec_ref(v_label_578_);
lean_dec(v_position_577_);
lean_dec_ref(v_range_575_);
v___x_657_ = lean_box(0);
return v___x_657_;
}
}
}
}
else
{
lean_object* v___x_658_; 
lean_del_object(v___x_585_);
lean_dec(v_tooltip_x3f_581_);
lean_dec_ref(v_textEdits_580_);
lean_dec(v_kind_x3f_579_);
lean_dec_ref(v_label_578_);
lean_dec(v_position_577_);
lean_dec_ref(v_range_575_);
v___x_658_ = lean_box(0);
return v___x_658_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_applyEditToHint_x3f___boxed(lean_object* v_hintMod_668_, lean_object* v_ihi_669_, lean_object* v_range_670_, lean_object* v_newText_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(v_hintMod_668_, v_ihi_669_, v_range_670_, v_newText_671_);
lean_dec_ref(v_newText_671_);
lean_dec(v_hintMod_668_);
return v_res_672_;
}
}
static lean_object* _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0(void){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = l_Lean_Server_instInhabitedRequestError_default;
v___x_702_ = lean_alloc_closure((void*)(l_instInhabitedEIO___aux__1___boxed), 4, 3);
lean_closure_set(v___x_702_, 0, lean_box(0));
lean_closure_set(v___x_702_, 1, lean_box(0));
lean_closure_set(v___x_702_, 2, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(lean_object* v_msg_703_, lean_object* v___y_704_){
_start:
{
lean_object* v___x_706_; lean_object* v___f_707_; lean_object* v___x_14669__overap_708_; lean_object* v___x_709_; 
v___x_706_ = lean_obj_once(&l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0, &l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0_once, _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0);
v___f_707_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_707_, 0, v___x_706_);
v___x_14669__overap_708_ = lean_panic_fn_borrowed(v___f_707_, v_msg_703_);
lean_dec_ref(v___f_707_);
lean_inc_ref(v___y_704_);
v___x_709_ = lean_apply_2(v___x_14669__overap_708_, v___y_704_, lean_box(0));
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___boxed(lean_object* v_msg_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v_msg_710_, v___y_711_);
lean_dec_ref(v___y_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(lean_object* v___x_714_, uint8_t v_val_715_, lean_object* v_as_716_, size_t v_i_717_, size_t v_stop_718_, lean_object* v_b_719_){
_start:
{
lean_object* v___y_721_; uint8_t v___x_725_; 
v___x_725_ = lean_usize_dec_eq(v_i_717_, v_stop_718_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v_position_727_; uint8_t v___x_728_; 
v___x_726_ = lean_array_uget_borrowed(v_as_716_, v_i_717_);
v_position_727_ = lean_ctor_get(v___x_726_, 0);
v___x_728_ = l_Lean_Syntax_Range_contains(v___x_714_, v_position_727_, v_val_715_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_inc(v___x_726_);
v___x_729_ = lean_array_push(v_b_719_, v___x_726_);
v___y_721_ = v___x_729_;
goto v___jp_720_;
}
else
{
v___y_721_ = v_b_719_;
goto v___jp_720_;
}
}
else
{
return v_b_719_;
}
v___jp_720_:
{
size_t v___x_722_; size_t v___x_723_; 
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_717_, v___x_722_);
v_i_717_ = v___x_723_;
v_b_719_ = v___y_721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5___boxed(lean_object* v___x_730_, lean_object* v_val_731_, lean_object* v_as_732_, lean_object* v_i_733_, lean_object* v_stop_734_, lean_object* v_b_735_){
_start:
{
uint8_t v_val_17613__boxed_736_; size_t v_i_boxed_737_; size_t v_stop_boxed_738_; lean_object* v_res_739_; 
v_val_17613__boxed_736_ = lean_unbox(v_val_731_);
v_i_boxed_737_ = lean_unbox_usize(v_i_733_);
lean_dec(v_i_733_);
v_stop_boxed_738_ = lean_unbox_usize(v_stop_734_);
lean_dec(v_stop_734_);
v_res_739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_730_, v_val_17613__boxed_736_, v_as_732_, v_i_boxed_737_, v_stop_boxed_738_, v_b_735_);
lean_dec_ref(v_as_732_);
lean_dec_ref(v___x_730_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(lean_object* v___x_740_, lean_object* v_as_741_, size_t v_i_742_, size_t v_stop_743_, lean_object* v_b_744_){
_start:
{
lean_object* v___y_746_; uint8_t v___x_750_; 
v___x_750_ = lean_usize_dec_eq(v_i_742_, v_stop_743_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; lean_object* v_position_752_; uint8_t v___x_753_; uint8_t v___x_754_; 
v___x_751_ = lean_array_uget_borrowed(v_as_741_, v_i_742_);
v_position_752_ = lean_ctor_get(v___x_751_, 0);
v___x_753_ = 1;
v___x_754_ = l_Lean_Syntax_Range_contains(v___x_740_, v_position_752_, v___x_753_);
if (v___x_754_ == 0)
{
v___y_746_ = v_b_744_;
goto v___jp_745_;
}
else
{
lean_object* v___x_755_; 
lean_inc(v___x_751_);
v___x_755_ = lean_array_push(v_b_744_, v___x_751_);
v___y_746_ = v___x_755_;
goto v___jp_745_;
}
}
else
{
return v_b_744_;
}
v___jp_745_:
{
size_t v___x_747_; size_t v___x_748_; 
v___x_747_ = ((size_t)1ULL);
v___x_748_ = lean_usize_add(v_i_742_, v___x_747_);
v_i_742_ = v___x_748_;
v_b_744_ = v___y_746_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___boxed(lean_object* v___x_756_, lean_object* v_as_757_, lean_object* v_i_758_, lean_object* v_stop_759_, lean_object* v_b_760_){
_start:
{
size_t v_i_boxed_761_; size_t v_stop_boxed_762_; lean_object* v_res_763_; 
v_i_boxed_761_ = lean_unbox_usize(v_i_758_);
lean_dec(v_i_758_);
v_stop_boxed_762_ = lean_unbox_usize(v_stop_759_);
lean_dec(v_stop_759_);
v_res_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(v___x_756_, v_as_757_, v_i_boxed_761_, v_stop_boxed_762_, v_b_760_);
lean_dec_ref(v_as_757_);
lean_dec_ref(v___x_756_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___redArg(lean_object* v___x_764_, size_t v_sz_765_, size_t v_i_766_, lean_object* v_bs_767_){
_start:
{
uint8_t v___x_769_; 
v___x_769_ = lean_usize_dec_lt(v_i_766_, v_sz_765_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v___x_764_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v_bs_767_);
return v___x_770_;
}
else
{
lean_object* v_v_771_; lean_object* v___x_772_; lean_object* v_bs_x27_773_; lean_object* v___x_774_; 
v_v_771_ = lean_array_uget(v_bs_767_, v_i_766_);
v___x_772_ = lean_unsigned_to_nat(0u);
v_bs_x27_773_ = lean_array_uset(v_bs_767_, v_i_766_, v___x_772_);
lean_inc_ref(v___x_764_);
v___x_774_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v___x_764_, v_v_771_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v___x_776_ = ((size_t)1ULL);
v___x_777_ = lean_usize_add(v_i_766_, v___x_776_);
v___x_778_ = lean_array_uset(v_bs_x27_773_, v_i_766_, v_a_775_);
v_i_766_ = v___x_777_;
v_bs_767_ = v___x_778_;
goto _start;
}
else
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
lean_dec_ref(v_bs_x27_773_);
lean_dec_ref(v___x_764_);
v_a_780_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v___x_774_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_774_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___redArg___boxed(lean_object* v___x_789_, lean_object* v_sz_790_, lean_object* v_i_791_, lean_object* v_bs_792_, lean_object* v___y_793_){
_start:
{
size_t v_sz_boxed_794_; size_t v_i_boxed_795_; lean_object* v_res_796_; 
v_sz_boxed_794_ = lean_unbox_usize(v_sz_790_);
lean_dec(v_sz_790_);
v_i_boxed_795_ = lean_unbox_usize(v_i_791_);
lean_dec(v_i_791_);
v_res_796_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___redArg(v___x_789_, v_sz_boxed_794_, v_i_boxed_795_, v_bs_792_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___lam__0(lean_object* v_postNode_797_, lean_object* v_ci_798_, lean_object* v_i_799_, lean_object* v_cs_800_, lean_object* v_x_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
lean_object* v___x_805_; 
lean_inc_ref(v___y_803_);
v___x_805_ = lean_apply_6(v_postNode_797_, v_ci_798_, v_i_799_, v_cs_800_, v___y_802_, v___y_803_, lean_box(0));
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___lam__0___boxed(lean_object* v_postNode_806_, lean_object* v_ci_807_, lean_object* v_i_808_, lean_object* v_cs_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___lam__0(v_postNode_806_, v_ci_807_, v_i_808_, v_cs_809_, v_x_810_, v___y_811_, v___y_812_);
lean_dec_ref(v___y_812_);
lean_dec(v_x_810_);
return v_res_814_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_instMonadEIO___redArg();
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg(lean_object* v_msg_816_, lean_object* v___y_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___f_824_; lean_object* v___f_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_17040__overap_834_; lean_object* v___x_835_; 
v___x_820_ = lean_obj_once(&l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg___closed__0, &l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg___closed__0);
v___x_821_ = l_ReaderT_instMonad___redArg(v___x_820_);
lean_inc_ref_n(v___x_821_, 6);
v___f_822_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_822_, 0, v___x_821_);
v___f_823_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_823_, 0, v___x_821_);
v___f_824_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_824_, 0, v___x_821_);
v___f_825_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_825_, 0, v___x_821_);
v___x_826_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_826_, 0, lean_box(0));
lean_closure_set(v___x_826_, 1, lean_box(0));
lean_closure_set(v___x_826_, 2, v___x_821_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___f_822_);
v___x_828_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_828_, 0, lean_box(0));
lean_closure_set(v___x_828_, 1, lean_box(0));
lean_closure_set(v___x_828_, 2, v___x_821_);
v___x_829_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_829_, 0, v___x_827_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
lean_ctor_set(v___x_829_, 2, v___f_823_);
lean_ctor_set(v___x_829_, 3, v___f_824_);
lean_ctor_set(v___x_829_, 4, v___f_825_);
v___x_830_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_830_, 0, lean_box(0));
lean_closure_set(v___x_830_, 1, lean_box(0));
lean_closure_set(v___x_830_, 2, v___x_821_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_829_);
lean_ctor_set(v___x_831_, 1, v___x_830_);
v___x_832_ = lean_box(0);
v___x_833_ = l_instInhabitedOfMonad___redArg(v___x_831_, v___x_832_);
v___x_17040__overap_834_ = lean_panic_fn_borrowed(v___x_833_, v_msg_816_);
lean_dec(v___x_833_);
lean_inc_ref(v___y_818_);
v___x_835_ = lean_apply_3(v___x_17040__overap_834_, v___y_817_, v___y_818_, lean_box(0));
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_msg_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg(v_msg_836_, v___y_837_, v___y_838_);
lean_dec_ref(v___y_838_);
return v_res_840_;
}
}
static lean_object* _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_844_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__2));
v___x_845_ = lean_unsigned_to_nat(21u);
v___x_846_ = lean_unsigned_to_nat(65u);
v___x_847_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__1));
v___x_848_ = ((lean_object*)(l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__0));
v___x_849_ = l_mkPanicMessageWithDecl(v___x_848_, v___x_847_, v___x_846_, v___x_845_, v___x_844_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg(lean_object* v_preNode_850_, lean_object* v_postNode_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
switch(lean_obj_tag(v_x_853_))
{
case 0:
{
lean_object* v_i_857_; lean_object* v_t_858_; lean_object* v___x_859_; 
v_i_857_ = lean_ctor_get(v_x_853_, 0);
lean_inc_ref(v_i_857_);
v_t_858_ = lean_ctor_get(v_x_853_, 1);
lean_inc_ref(v_t_858_);
lean_dec_ref_known(v_x_853_, 2);
v___x_859_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_857_, v_x_852_);
v_x_852_ = v___x_859_;
v_x_853_ = v_t_858_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_852_) == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec_ref_known(v_x_853_, 2);
lean_dec_ref(v_postNode_851_);
lean_dec_ref(v_preNode_850_);
v___x_861_ = lean_obj_once(&l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__3, &l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__3_once, _init_l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___closed__3);
v___x_862_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg(v___x_861_, v___y_854_, v___y_855_);
return v___x_862_;
}
else
{
lean_object* v_i_863_; lean_object* v_children_864_; lean_object* v_val_865_; lean_object* v___x_866_; 
v_i_863_ = lean_ctor_get(v_x_853_, 0);
lean_inc_ref_n(v_i_863_, 2);
v_children_864_ = lean_ctor_get(v_x_853_, 1);
lean_inc_ref_n(v_children_864_, 2);
lean_dec_ref_known(v_x_853_, 2);
v_val_865_ = lean_ctor_get(v_x_852_, 0);
lean_inc_n(v_val_865_, 2);
lean_inc_ref(v_preNode_850_);
lean_inc_ref(v___y_855_);
v___x_866_ = lean_apply_6(v_preNode_850_, v_val_865_, v_i_863_, v_children_864_, v___y_854_, v___y_855_, lean_box(0));
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v_fst_868_; uint8_t v___x_869_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
v_fst_868_ = lean_ctor_get(v_a_867_, 0);
v___x_869_ = lean_unbox(v_fst_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_904_; 
lean_dec_ref(v_preNode_850_);
v_isSharedCheck_904_ = !lean_is_exclusive(v_x_852_);
if (v_isSharedCheck_904_ == 0)
{
lean_object* v_unused_905_; 
v_unused_905_ = lean_ctor_get(v_x_852_, 0);
lean_dec(v_unused_905_);
v___x_871_ = v_x_852_;
v_isShared_872_ = v_isSharedCheck_904_;
goto v_resetjp_870_;
}
else
{
lean_dec(v_x_852_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_904_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v_snd_873_; lean_object* v___x_874_; lean_object* v___x_875_; 
v_snd_873_ = lean_ctor_get(v_a_867_, 1);
lean_inc(v_snd_873_);
lean_dec(v_a_867_);
v___x_874_ = lean_box(0);
lean_inc_ref(v___y_855_);
v___x_875_ = lean_apply_7(v_postNode_851_, v_val_865_, v_i_863_, v_children_864_, v___x_874_, v_snd_873_, v___y_855_, lean_box(0));
if (lean_obj_tag(v___x_875_) == 0)
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_895_; 
v_a_876_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_895_ == 0)
{
v___x_878_ = v___x_875_;
v_isShared_879_ = v_isSharedCheck_895_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_875_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_895_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v_fst_880_; lean_object* v_snd_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_894_; 
v_fst_880_ = lean_ctor_get(v_a_876_, 0);
v_snd_881_ = lean_ctor_get(v_a_876_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_a_876_);
if (v_isSharedCheck_894_ == 0)
{
v___x_883_ = v_a_876_;
v_isShared_884_ = v_isSharedCheck_894_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_snd_881_);
lean_inc(v_fst_880_);
lean_dec(v_a_876_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_894_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 0, v_fst_880_);
v___x_886_ = v___x_871_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v_fst_880_);
v___x_886_ = v_reuseFailAlloc_893_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_886_);
v___x_888_ = v___x_883_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_snd_881_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_879_ == 0)
{
lean_ctor_set(v___x_878_, 0, v___x_888_);
v___x_890_ = v___x_878_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_del_object(v___x_871_);
v_a_896_ = lean_ctor_get(v___x_875_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_875_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_875_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_875_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
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
else
{
lean_object* v_snd_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_snd_906_ = lean_ctor_get(v_a_867_, 1);
lean_inc(v_snd_906_);
lean_dec(v_a_867_);
v___x_907_ = l_Lean_Elab_Info_updateContext_x3f(v_x_852_, v_i_863_);
v___x_908_ = l_Lean_PersistentArray_toList___redArg(v_children_864_);
v___x_909_ = lean_box(0);
lean_inc_ref(v_postNode_851_);
v___x_910_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3___redArg(v_preNode_850_, v_postNode_851_, v___x_907_, v___x_908_, v___x_909_, v_snd_906_, v___y_855_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v_fst_912_; lean_object* v_snd_913_; lean_object* v___x_914_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v_fst_912_ = lean_ctor_get(v_a_911_, 0);
lean_inc(v_fst_912_);
v_snd_913_ = lean_ctor_get(v_a_911_, 1);
lean_inc(v_snd_913_);
lean_dec(v_a_911_);
lean_inc_ref(v___y_855_);
v___x_914_ = lean_apply_7(v_postNode_851_, v_val_865_, v_i_863_, v_children_864_, v_fst_912_, v_snd_913_, v___y_855_, lean_box(0));
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_932_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_932_ == 0)
{
v___x_917_ = v___x_914_;
v_isShared_918_ = v_isSharedCheck_932_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_914_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_932_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v_fst_919_; lean_object* v_snd_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_931_; 
v_fst_919_ = lean_ctor_get(v_a_915_, 0);
v_snd_920_ = lean_ctor_get(v_a_915_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_a_915_);
if (v_isSharedCheck_931_ == 0)
{
v___x_922_ = v_a_915_;
v_isShared_923_ = v_isSharedCheck_931_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_snd_920_);
lean_inc(v_fst_919_);
lean_dec(v_a_915_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_931_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_924_, 0, v_fst_919_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_930_, 1, v_snd_920_);
v___x_926_ = v_reuseFailAlloc_930_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_928_; 
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 0, v___x_926_);
v___x_928_ = v___x_917_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
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
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
v_a_933_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_914_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_914_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
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
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_val_865_);
lean_dec_ref(v_children_864_);
lean_dec_ref(v_i_863_);
lean_dec_ref(v_postNode_851_);
v_a_941_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_910_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_910_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_val_865_);
lean_dec_ref(v_children_864_);
lean_dec_ref(v_i_863_);
lean_dec_ref_known(v_x_852_, 1);
lean_dec_ref(v_postNode_851_);
lean_dec_ref(v_preNode_850_);
v_a_949_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_866_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_866_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
}
}
default: 
{
lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_965_; 
lean_dec(v_x_852_);
lean_dec_ref(v_postNode_851_);
lean_dec_ref(v_preNode_850_);
v_isSharedCheck_965_ = !lean_is_exclusive(v_x_853_);
if (v_isSharedCheck_965_ == 0)
{
lean_object* v_unused_966_; 
v_unused_966_ = lean_ctor_get(v_x_853_, 0);
lean_dec(v_unused_966_);
v___x_958_ = v_x_853_;
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
else
{
lean_dec(v_x_853_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_965_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
v___x_960_ = lean_box(0);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___y_854_);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 0);
lean_ctor_set(v___x_958_, 0, v___x_961_);
v___x_963_ = v___x_958_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3___redArg(lean_object* v_preNode_967_, lean_object* v_postNode_968_, lean_object* v___x_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
if (lean_obj_tag(v_x_970_) == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec(v___x_969_);
lean_dec_ref(v_postNode_968_);
lean_dec_ref(v_preNode_967_);
v___x_975_ = l_List_reverse___redArg(v_x_971_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___y_972_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
else
{
lean_object* v_head_978_; lean_object* v_tail_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_999_; 
v_head_978_ = lean_ctor_get(v_x_970_, 0);
v_tail_979_ = lean_ctor_get(v_x_970_, 1);
v_isSharedCheck_999_ = !lean_is_exclusive(v_x_970_);
if (v_isSharedCheck_999_ == 0)
{
v___x_981_ = v_x_970_;
v_isShared_982_ = v_isSharedCheck_999_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_tail_979_);
lean_inc(v_head_978_);
lean_dec(v_x_970_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_999_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_983_; 
lean_inc(v___x_969_);
lean_inc_ref(v_postNode_968_);
lean_inc_ref(v_preNode_967_);
v___x_983_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg(v_preNode_967_, v_postNode_968_, v___x_969_, v_head_978_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_983_) == 0)
{
lean_object* v_a_984_; lean_object* v_fst_985_; lean_object* v_snd_986_; lean_object* v___x_988_; 
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec_ref_known(v___x_983_, 1);
v_fst_985_ = lean_ctor_get(v_a_984_, 0);
lean_inc(v_fst_985_);
v_snd_986_ = lean_ctor_get(v_a_984_, 1);
lean_inc(v_snd_986_);
lean_dec(v_a_984_);
if (v_isShared_982_ == 0)
{
lean_ctor_set(v___x_981_, 1, v_x_971_);
lean_ctor_set(v___x_981_, 0, v_fst_985_);
v___x_988_ = v___x_981_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_fst_985_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_x_971_);
v___x_988_ = v_reuseFailAlloc_990_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
v_x_970_ = v_tail_979_;
v_x_971_ = v___x_988_;
v___y_972_ = v_snd_986_;
goto _start;
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_del_object(v___x_981_);
lean_dec(v_tail_979_);
lean_dec(v_x_971_);
lean_dec(v___x_969_);
lean_dec_ref(v_postNode_968_);
lean_dec_ref(v_preNode_967_);
v_a_991_ = lean_ctor_get(v___x_983_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_983_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_983_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_983_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3___redArg___boxed(lean_object* v_preNode_1000_, lean_object* v_postNode_1001_, lean_object* v___x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3___redArg(v_preNode_1000_, v_postNode_1001_, v___x_1002_, v_x_1003_, v_x_1004_, v___y_1005_, v___y_1006_);
lean_dec_ref(v___y_1006_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg___boxed(lean_object* v_preNode_1009_, lean_object* v_postNode_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg(v_preNode_1009_, v_postNode_1010_, v_x_1011_, v_x_1012_, v___y_1013_, v___y_1014_);
lean_dec_ref(v___y_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(lean_object* v_preNode_1017_, lean_object* v_postNode_1018_, lean_object* v_ctx_x3f_1019_, lean_object* v_t_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_){
_start:
{
lean_object* v___f_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___f_1024_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1024_, 0, v_postNode_1018_);
v___x_1025_ = lean_box(0);
v___x_1026_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg(v_preNode_1017_, v___f_1024_, v_ctx_x3f_1019_, v_t_1020_, v___y_1021_, v___y_1022_);
if (lean_obj_tag(v___x_1026_) == 0)
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1043_; 
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1029_ = v___x_1026_;
v_isShared_1030_ = v_isSharedCheck_1043_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1043_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v_snd_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1041_; 
v_snd_1031_ = lean_ctor_get(v_a_1027_, 1);
v_isSharedCheck_1041_ = !lean_is_exclusive(v_a_1027_);
if (v_isSharedCheck_1041_ == 0)
{
lean_object* v_unused_1042_; 
v_unused_1042_ = lean_ctor_get(v_a_1027_, 0);
lean_dec(v_unused_1042_);
v___x_1033_ = v_a_1027_;
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_snd_1031_);
lean_dec(v_a_1027_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1041_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1025_);
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1025_);
lean_ctor_set(v_reuseFailAlloc_1040_, 1, v_snd_1031_);
v___x_1036_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1030_ == 0)
{
lean_ctor_set(v___x_1029_, 0, v___x_1036_);
v___x_1038_ = v___x_1029_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_a_1044_ = lean_ctor_get(v___x_1026_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1026_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1026_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1026_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___boxed(lean_object* v_preNode_1052_, lean_object* v_postNode_1053_, lean_object* v_ctx_x3f_1054_, lean_object* v_t_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(v_preNode_1052_, v_postNode_1053_, v_ctx_x3f_1054_, v_t_1055_, v___y_1056_, v___y_1057_);
lean_dec_ref(v___y_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__1(uint8_t v___x_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_x_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1067_ = lean_box(v___x_1060_);
v___x_1068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1068_, 0, v___x_1067_);
lean_ctor_set(v___x_1068_, 1, v___y_1064_);
v___x_1069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__1___boxed(lean_object* v___x_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
uint8_t v___x_18154__boxed_1077_; lean_object* v_res_1078_; 
v___x_18154__boxed_1077_ = lean_unbox(v___x_1070_);
v_res_1078_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__1(v___x_18154__boxed_1077_, v_x_1071_, v_x_1072_, v_x_1073_, v___y_1074_, v___y_1075_);
lean_dec_ref(v___y_1075_);
lean_dec_ref(v_x_1073_);
lean_dec_ref(v_x_1072_);
lean_dec_ref(v_x_1071_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__0(lean_object* v_ci_1079_, lean_object* v_i_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
if (lean_obj_tag(v_i_1080_) == 10)
{
lean_object* v_i_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1120_; 
v_i_1085_ = lean_ctor_get(v_i_1080_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_i_1080_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1087_ = v_i_1080_;
v_isShared_1088_ = v_isSharedCheck_1120_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_i_1085_);
lean_dec(v_i_1080_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1120_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_Elab_InlayHint_ofCustomInfo_x3f(v_i_1085_);
lean_dec_ref(v_i_1085_);
if (lean_obj_tag(v___x_1089_) == 1)
{
lean_object* v_val_1090_; lean_object* v_lctx_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_del_object(v___x_1087_);
v_val_1090_ = lean_ctor_get(v___x_1089_, 0);
lean_inc(v_val_1090_);
lean_dec_ref_known(v___x_1089_, 1);
v_lctx_1091_ = lean_ctor_get(v_val_1090_, 1);
lean_inc_ref(v_lctx_1091_);
v___x_1092_ = lean_alloc_closure((void*)(l_Lean_Elab_InlayHint_resolveDeferred___boxed), 6, 1);
lean_closure_set(v___x_1092_, 0, v_val_1090_);
v___x_1093_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_1079_, v_lctx_1091_, v___x_1092_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1105_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1096_ = v___x_1093_;
v_isShared_1097_ = v_isSharedCheck_1105_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1093_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1105_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v_toInlayHintInfo_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1103_; 
v_toInlayHintInfo_1098_ = lean_ctor_get(v_a_1094_, 0);
lean_inc_ref(v_toInlayHintInfo_1098_);
lean_dec(v_a_1094_);
v___x_1099_ = lean_box(0);
v___x_1100_ = lean_array_push(v___y_1082_, v_toInlayHintInfo_1098_);
v___x_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1099_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 0, v___x_1101_);
v___x_1103_ = v___x_1096_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1101_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1114_; 
lean_dec_ref(v___y_1082_);
v_a_1106_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1108_ = v___x_1093_;
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1093_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1110_ = l_Lean_Server_RequestError_ofIoError(v_a_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_dec(v___x_1089_);
lean_dec_ref(v_ci_1079_);
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v___y_1082_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1116_);
v___x_1118_ = v___x_1087_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v_i_1080_);
lean_dec_ref(v_ci_1079_);
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v___y_1082_);
v___x_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1123_, 0, v___x_1122_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__0___boxed(lean_object* v_ci_1124_, lean_object* v_i_1125_, lean_object* v_x_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_){
_start:
{
lean_object* v_res_1130_; 
v_res_1130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__0(v_ci_1124_, v_i_1125_, v_x_1126_, v___y_1127_, v___y_1128_);
lean_dec_ref(v___y_1128_);
lean_dec_ref(v_x_1126_);
return v_res_1130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg(lean_object* v_a_1132_, lean_object* v_b_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_){
_start:
{
lean_object* v_array_1137_; lean_object* v_start_1138_; lean_object* v_stop_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1162_; 
v_array_1137_ = lean_ctor_get(v_a_1132_, 0);
v_start_1138_ = lean_ctor_get(v_a_1132_, 1);
v_stop_1139_ = lean_ctor_get(v_a_1132_, 2);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_a_1132_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1141_ = v_a_1132_;
v_isShared_1142_ = v_isSharedCheck_1162_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_stop_1139_);
lean_inc(v_start_1138_);
lean_inc(v_array_1137_);
lean_dec(v_a_1132_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1162_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_nat_dec_lt(v_start_1138_, v_stop_1139_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_del_object(v___x_1141_);
lean_dec(v_stop_1139_);
lean_dec(v_start_1138_);
lean_dec_ref(v_array_1137_);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v_b_1133_);
lean_ctor_set(v___x_1144_, 1, v___y_1134_);
v___x_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
return v___x_1145_;
}
else
{
lean_object* v___f_1146_; lean_object* v___x_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___f_1146_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___closed__0));
v___x_1147_ = lean_box(v___x_1143_);
v___f_1148_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1148_, 0, v___x_1147_);
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_unsigned_to_nat(1u);
v___x_1151_ = lean_nat_add(v_start_1138_, v___x_1150_);
lean_inc_ref(v_array_1137_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 1, v___x_1151_);
v___x_1153_ = v___x_1141_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_array_1137_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v_stop_1139_);
v___x_1153_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1154_ = lean_array_fget(v_array_1137_, v_start_1138_);
lean_dec(v_start_1138_);
lean_dec_ref(v_array_1137_);
v___x_1155_ = lean_box(0);
v___x_1156_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v___x_1154_);
v___x_1157_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(v___f_1148_, v___f_1146_, v___x_1155_, v___x_1156_, v___y_1134_, v___y_1135_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; lean_object* v_snd_1159_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v_snd_1159_ = lean_ctor_get(v_a_1158_, 1);
lean_inc(v_snd_1159_);
lean_dec(v_a_1158_);
v_a_1132_ = v___x_1153_;
v_b_1133_ = v___x_1149_;
v___y_1134_ = v_snd_1159_;
goto _start;
}
else
{
lean_dec_ref(v___x_1153_);
return v___x_1157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg___boxed(lean_object* v_a_1163_, lean_object* v_b_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg(v_a_1163_, v_b_1164_, v___y_1165_, v___y_1166_);
lean_dec_ref(v___y_1166_);
return v_res_1168_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2(void){
_start:
{
lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1171_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__1));
v___x_1172_ = lean_unsigned_to_nat(2u);
v___x_1173_ = lean_unsigned_to_nat(162u);
v___x_1174_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__0));
v___x_1175_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_1176_ = l_mkPanicMessageWithDecl(v___x_1175_, v___x_1174_, v___x_1173_, v___x_1172_, v___x_1171_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints(lean_object* v_p_1177_, lean_object* v_s_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_doc_1181_; lean_object* v_toEditableDocumentCore_1182_; lean_object* v_meta_1183_; lean_object* v_cancelTk_1184_; lean_object* v_cmdSnaps_1185_; lean_object* v_text_1186_; lean_object* v_oldInlayHints_1187_; lean_object* v_oldFinishedSnaps_1188_; lean_object* v_lastEditTimestamp_x3f_1189_; uint8_t v_isFirstRequestAfterEdit_1190_; uint8_t v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; 
v_doc_1181_ = lean_ctor_get(v_a_1179_, 1);
v_toEditableDocumentCore_1182_ = lean_ctor_get(v_doc_1181_, 0);
v_meta_1183_ = lean_ctor_get(v_toEditableDocumentCore_1182_, 0);
v_cancelTk_1184_ = lean_ctor_get(v_a_1179_, 4);
v_cmdSnaps_1185_ = lean_ctor_get(v_toEditableDocumentCore_1182_, 2);
v_text_1186_ = lean_ctor_get(v_meta_1183_, 3);
v_oldInlayHints_1187_ = lean_ctor_get(v_s_1178_, 0);
v_oldFinishedSnaps_1188_ = lean_ctor_get(v_s_1178_, 1);
v_lastEditTimestamp_x3f_1189_ = lean_ctor_get(v_s_1178_, 2);
v_isFirstRequestAfterEdit_1190_ = lean_ctor_get_uint8(v_s_1178_, sizeof(void*)*3);
if (v_isFirstRequestAfterEdit_1190_ == 0)
{
lean_object* v_range_1218_; lean_object* v___x_1219_; uint8_t v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v_lower_1226_; lean_object* v_upper_1227_; uint8_t v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; lean_object* v___y_1253_; uint8_t v___y_1256_; uint8_t v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; uint8_t v___y_1271_; lean_object* v___y_1272_; uint8_t v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___y_1285_; 
v_range_1218_ = lean_ctor_get(v_p_1177_, 2);
lean_inc_ref(v_range_1218_);
lean_dec_ref(v_p_1177_);
v___x_1219_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_1186_, v_range_1218_);
v___x_1282_ = lean_unsigned_to_nat(3000u);
v___x_1283_ = lean_io_mono_ms_now();
if (lean_obj_tag(v_lastEditTimestamp_x3f_1189_) == 0)
{
lean_object* v___x_1334_; 
lean_dec(v___x_1283_);
v___x_1334_ = lean_unsigned_to_nat(0u);
v___y_1285_ = v___x_1334_;
goto v___jp_1284_;
}
else
{
lean_object* v_val_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; 
v_val_1335_ = lean_ctor_get(v_lastEditTimestamp_x3f_1189_, 0);
v___x_1336_ = lean_nat_sub(v___x_1283_, v_val_1335_);
lean_dec(v___x_1283_);
v___x_1337_ = lean_nat_sub(v___x_1282_, v___x_1336_);
lean_dec(v___x_1336_);
v___y_1285_ = v___x_1337_;
goto v___jp_1284_;
}
v___jp_1220_:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1228_ = l_Array_toSubarray___redArg(v___y_1225_, v_lower_1226_, v_upper_1227_);
v___x_1229_ = lean_box(0);
v___x_1230_ = lean_mk_empty_array_with_capacity(v___y_1224_);
lean_inc_ref(v___x_1230_);
v___x_1231_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg(v___x_1228_, v___x_1229_, v___x_1230_, v_a_1179_);
if (lean_obj_tag(v___x_1231_) == 0)
{
lean_object* v_a_1232_; lean_object* v_snd_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v_a_1232_ = lean_ctor_get(v___x_1231_, 0);
lean_inc(v_a_1232_);
lean_dec_ref_known(v___x_1231_, 1);
v_snd_1233_ = lean_ctor_get(v_a_1232_, 1);
lean_inc(v_snd_1233_);
lean_dec(v_a_1232_);
v___x_1234_ = l_Array_append___redArg(v_snd_1233_, v___y_1222_);
lean_dec_ref(v___y_1222_);
v___x_1235_ = lean_array_get_size(v___x_1234_);
v___x_1236_ = lean_nat_dec_lt(v___y_1224_, v___x_1235_);
lean_dec(v___y_1224_);
if (v___x_1236_ == 0)
{
lean_dec_ref(v___x_1219_);
v___y_1192_ = v___y_1221_;
v___y_1193_ = v___x_1234_;
v___y_1194_ = v___y_1223_;
v___y_1195_ = v___x_1230_;
goto v___jp_1191_;
}
else
{
size_t v___x_1237_; size_t v___x_1238_; lean_object* v___x_1239_; 
v___x_1237_ = ((size_t)0ULL);
v___x_1238_ = lean_usize_of_nat(v___x_1235_);
v___x_1239_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(v___x_1219_, v___x_1234_, v___x_1237_, v___x_1238_, v___x_1230_);
lean_dec_ref(v___x_1219_);
v___y_1192_ = v___y_1221_;
v___y_1193_ = v___x_1234_;
v___y_1194_ = v___y_1223_;
v___y_1195_ = v___x_1239_;
goto v___jp_1191_;
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v___x_1230_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec_ref(v___x_1219_);
lean_dec(v_lastEditTimestamp_x3f_1189_);
v_a_1240_ = lean_ctor_get(v___x_1231_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1231_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1231_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1231_);
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
v___jp_1248_:
{
uint8_t v___x_1254_; 
v___x_1254_ = lean_nat_dec_le(v_oldFinishedSnaps_1188_, v___y_1252_);
if (v___x_1254_ == 0)
{
lean_inc(v___y_1250_);
v___y_1221_ = v___y_1249_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v___y_1250_;
v___y_1224_ = v___y_1252_;
v___y_1225_ = v___y_1251_;
v_lower_1226_ = v_oldFinishedSnaps_1188_;
v_upper_1227_ = v___y_1250_;
goto v___jp_1220_;
}
else
{
lean_dec(v_oldFinishedSnaps_1188_);
lean_inc(v___y_1252_);
lean_inc(v___y_1250_);
v___y_1221_ = v___y_1249_;
v___y_1222_ = v___y_1253_;
v___y_1223_ = v___y_1250_;
v___y_1224_ = v___y_1252_;
v___y_1225_ = v___y_1251_;
v_lower_1226_ = v___y_1252_;
v_upper_1227_ = v___y_1250_;
goto v___jp_1220_;
}
}
v___jp_1255_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = lean_array_get_size(v_oldInlayHints_1187_);
v___x_1264_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init___closed__0));
v___x_1265_ = lean_nat_dec_lt(v___x_1262_, v___x_1263_);
if (v___x_1265_ == 0)
{
lean_dec(v___y_1261_);
lean_dec(v___y_1259_);
lean_dec_ref(v_oldInlayHints_1187_);
v___y_1249_ = v___y_1256_;
v___y_1250_ = v___y_1258_;
v___y_1251_ = v___y_1260_;
v___y_1252_ = v___x_1262_;
v___y_1253_ = v___x_1264_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1266_; size_t v___x_1267_; size_t v___x_1268_; lean_object* v___x_1269_; 
v___x_1266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1266_, 0, v___y_1259_);
lean_ctor_set(v___x_1266_, 1, v___y_1261_);
v___x_1267_ = ((size_t)0ULL);
v___x_1268_ = lean_usize_of_nat(v___x_1263_);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1266_, v___y_1257_, v_oldInlayHints_1187_, v___x_1267_, v___x_1268_, v___x_1264_);
lean_dec_ref(v_oldInlayHints_1187_);
lean_dec_ref_known(v___x_1266_, 2);
v___y_1249_ = v___y_1256_;
v___y_1250_ = v___y_1258_;
v___y_1251_ = v___y_1260_;
v___y_1252_ = v___x_1262_;
v___y_1253_ = v___x_1269_;
goto v___jp_1248_;
}
}
v___jp_1270_:
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_nat_sub(v___y_1274_, v___y_1272_);
v___x_1278_ = lean_nat_dec_lt(v___x_1277_, v___y_1274_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_dec(v___x_1277_);
v___x_1279_ = lean_unsigned_to_nat(0u);
v___y_1256_ = v___y_1271_;
v___y_1257_ = v___y_1273_;
v___y_1258_ = v___y_1274_;
v___y_1259_ = v___y_1276_;
v___y_1260_ = v___y_1275_;
v___y_1261_ = v___x_1279_;
goto v___jp_1255_;
}
else
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_array_fget_borrowed(v___y_1275_, v___x_1277_);
lean_dec(v___x_1277_);
v___x_1281_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1280_);
v___y_1256_ = v___y_1271_;
v___y_1257_ = v___y_1273_;
v___y_1258_ = v___y_1274_;
v___y_1259_ = v___y_1276_;
v___y_1260_ = v___y_1275_;
v___y_1261_ = v___x_1281_;
goto v___jp_1255_;
}
}
v___jp_1284_:
{
uint32_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v_snd_1289_; lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1332_; 
v___x_1286_ = lean_uint32_of_nat(v___y_1285_);
lean_dec(v___y_1285_);
v___x_1287_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_1184_);
lean_inc(v_cmdSnaps_1185_);
v___x_1288_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_cmdSnaps_1185_, v___x_1286_, v___x_1287_);
v_snd_1289_ = lean_ctor_get(v___x_1288_, 1);
lean_inc(v_snd_1289_);
v_fst_1290_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_fst_1290_);
lean_dec_ref(v___x_1288_);
v_snd_1291_ = lean_ctor_get(v_snd_1289_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v_snd_1289_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v_snd_1289_, 0);
lean_dec(v_unused_1333_);
v___x_1293_ = v_snd_1289_;
v_isShared_1294_ = v_isSharedCheck_1332_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_snd_1291_);
lean_dec(v_snd_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1332_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_cancelTk_1184_);
if (v___x_1295_ == 0)
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
lean_inc(v_lastEditTimestamp_x3f_1189_);
lean_inc(v_oldFinishedSnaps_1188_);
lean_inc_ref(v_oldInlayHints_1187_);
lean_del_object(v___x_1293_);
lean_dec_ref(v_s_1178_);
v___x_1296_ = lean_array_mk(v_fst_1290_);
v___x_1297_ = lean_array_get_size(v___x_1296_);
v___x_1298_ = lean_nat_dec_le(v_oldFinishedSnaps_1188_, v___x_1297_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
lean_dec_ref(v___x_1296_);
lean_dec(v_snd_1291_);
lean_dec_ref(v___x_1219_);
lean_dec(v_lastEditTimestamp_x3f_1189_);
lean_dec(v_oldFinishedSnaps_1188_);
lean_dec_ref(v_oldInlayHints_1187_);
v___x_1299_ = lean_obj_once(&l_Lean_Server_FileWorker_handleInlayHints___closed__2, &l_Lean_Server_FileWorker_handleInlayHints___closed__2_once, _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2);
v___x_1300_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v___x_1299_, v_a_1179_);
return v___x_1300_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v___x_1301_ = lean_unsigned_to_nat(1u);
v___x_1302_ = lean_nat_sub(v_oldFinishedSnaps_1188_, v___x_1301_);
v___x_1303_ = lean_nat_dec_lt(v___x_1302_, v___x_1297_);
if (v___x_1303_ == 0)
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
lean_dec(v___x_1302_);
v___x_1304_ = lean_unsigned_to_nat(0u);
v___x_1305_ = lean_unbox(v_snd_1291_);
lean_dec(v_snd_1291_);
v___y_1271_ = v___x_1305_;
v___y_1272_ = v___x_1301_;
v___y_1273_ = v___x_1295_;
v___y_1274_ = v___x_1297_;
v___y_1275_ = v___x_1296_;
v___y_1276_ = v___x_1304_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1306_ = lean_array_fget_borrowed(v___x_1296_, v___x_1302_);
lean_dec(v___x_1302_);
v___x_1307_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1306_);
v___x_1308_ = lean_unbox(v_snd_1291_);
lean_dec(v_snd_1291_);
v___y_1271_ = v___x_1308_;
v___y_1272_ = v___x_1301_;
v___y_1273_ = v___x_1295_;
v___y_1274_ = v___x_1297_;
v___y_1275_ = v___x_1296_;
v___y_1276_ = v___x_1307_;
goto v___jp_1270_;
}
}
}
else
{
size_t v_sz_1309_; size_t v___x_1310_; lean_object* v___x_1311_; 
lean_dec(v_snd_1291_);
lean_dec(v_fst_1290_);
lean_dec_ref(v___x_1219_);
v_sz_1309_ = lean_array_size(v_oldInlayHints_1187_);
v___x_1310_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1187_);
lean_inc_ref(v_text_1186_);
v___x_1311_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___redArg(v_text_1186_, v_sz_1309_, v___x_1310_, v_oldInlayHints_1187_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1323_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1323_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1316_, 0, v_a_1312_);
lean_ctor_set_uint8(v___x_1316_, sizeof(void*)*1, v_isFirstRequestAfterEdit_1190_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v_s_1178_);
lean_ctor_set(v___x_1293_, 0, v___x_1316_);
v___x_1318_ = v___x_1293_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_s_1178_);
v___x_1318_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1320_; 
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1318_);
v___x_1320_ = v___x_1314_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_del_object(v___x_1293_);
lean_dec_ref(v_s_1178_);
v_a_1324_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1311_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1311_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1366_; 
lean_inc(v_lastEditTimestamp_x3f_1189_);
lean_inc(v_oldFinishedSnaps_1188_);
lean_inc_ref(v_oldInlayHints_1187_);
lean_dec_ref(v_p_1177_);
v_isSharedCheck_1366_ = !lean_is_exclusive(v_s_1178_);
if (v_isSharedCheck_1366_ == 0)
{
lean_object* v_unused_1367_; lean_object* v_unused_1368_; lean_object* v_unused_1369_; 
v_unused_1367_ = lean_ctor_get(v_s_1178_, 2);
lean_dec(v_unused_1367_);
v_unused_1368_ = lean_ctor_get(v_s_1178_, 1);
lean_dec(v_unused_1368_);
v_unused_1369_ = lean_ctor_get(v_s_1178_, 0);
lean_dec(v_unused_1369_);
v___x_1339_ = v_s_1178_;
v_isShared_1340_ = v_isSharedCheck_1366_;
goto v_resetjp_1338_;
}
else
{
lean_dec(v_s_1178_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1366_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
size_t v_sz_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v_sz_1341_ = lean_array_size(v_oldInlayHints_1187_);
v___x_1342_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1187_);
lean_inc_ref(v_text_1186_);
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___redArg(v_text_1186_, v_sz_1341_, v___x_1342_, v_oldInlayHints_1187_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1357_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1357_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1357_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
uint8_t v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1348_ = 0;
v___x_1349_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1349_, 0, v_a_1344_);
lean_ctor_set_uint8(v___x_1349_, sizeof(void*)*1, v___x_1348_);
if (v_isShared_1340_ == 0)
{
v___x_1351_ = v___x_1339_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_oldInlayHints_1187_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v_oldFinishedSnaps_1188_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_lastEditTimestamp_x3f_1189_);
v___x_1351_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
lean_ctor_set_uint8(v___x_1351_, sizeof(void*)*3, v___x_1348_);
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1349_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 0, v___x_1352_);
v___x_1354_ = v___x_1346_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_del_object(v___x_1339_);
lean_dec(v_lastEditTimestamp_x3f_1189_);
lean_dec(v_oldFinishedSnaps_1188_);
lean_dec_ref(v_oldInlayHints_1187_);
v_a_1358_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1343_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1343_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
v___jp_1191_:
{
size_t v_sz_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
v_sz_1196_ = lean_array_size(v___y_1195_);
v___x_1197_ = ((size_t)0ULL);
lean_inc_ref(v_text_1186_);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___redArg(v_text_1186_, v_sz_1196_, v___x_1197_, v___y_1195_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1209_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1201_ = v___x_1198_;
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1209_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1203_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1203_, 0, v_a_1199_);
lean_ctor_set_uint8(v___x_1203_, sizeof(void*)*1, v___y_1192_);
v___x_1204_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1204_, 0, v___y_1193_);
lean_ctor_set(v___x_1204_, 1, v___y_1194_);
lean_ctor_set(v___x_1204_, 2, v_lastEditTimestamp_x3f_1189_);
lean_ctor_set_uint8(v___x_1204_, sizeof(void*)*3, v_isFirstRequestAfterEdit_1190_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1203_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1205_);
v___x_1207_ = v___x_1201_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v_lastEditTimestamp_x3f_1189_);
v_a_1210_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1198_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1198_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints___boxed(lean_object* v_p_1370_, lean_object* v_s_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Server_FileWorker_handleInlayHints(v_p_1370_, v_s_1371_, v_a_1372_);
lean_dec_ref(v_a_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(lean_object* v_inst_1375_, lean_object* v_R_1376_, lean_object* v_a_1377_, lean_object* v_b_1378_, lean_object* v_c_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___redArg(v_a_1377_, v_b_1378_, v___y_1380_, v___y_1381_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___boxed(lean_object* v_inst_1384_, lean_object* v_R_1385_, lean_object* v_a_1386_, lean_object* v_b_1387_, lean_object* v_c_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v_inst_1384_, v_R_1385_, v_a_1386_, v_b_1387_, v_c_1388_, v___y_1389_, v___y_1390_);
lean_dec_ref(v___y_1390_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(lean_object* v___x_1393_, size_t v_sz_1394_, size_t v_i_1395_, lean_object* v_bs_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___redArg(v___x_1393_, v_sz_1394_, v_i_1395_, v_bs_1396_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___boxed(lean_object* v___x_1400_, lean_object* v_sz_1401_, lean_object* v_i_1402_, lean_object* v_bs_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_){
_start:
{
size_t v_sz_boxed_1406_; size_t v_i_boxed_1407_; lean_object* v_res_1408_; 
v_sz_boxed_1406_ = lean_unbox_usize(v_sz_1401_);
lean_dec(v_sz_1401_);
v_i_boxed_1407_ = lean_unbox_usize(v_i_1402_);
lean_dec(v_i_1402_);
v_res_1408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v___x_1400_, v_sz_boxed_1406_, v_i_boxed_1407_, v_bs_1403_, v___y_1404_);
lean_dec_ref(v___y_1404_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2(lean_object* v_00_u03b1_1409_, lean_object* v_msg_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___redArg(v_msg_1410_, v___y_1411_, v___y_1412_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_panic___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__2(v_00_u03b1_1415_, v_msg_1416_, v___y_1417_, v___y_1418_);
lean_dec_ref(v___y_1418_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1(lean_object* v_00_u03b1_1421_, lean_object* v_preNode_1422_, lean_object* v_postNode_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
lean_object* v___x_1429_; 
v___x_1429_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___redArg(v_preNode_1422_, v_postNode_1423_, v_x_1424_, v_x_1425_, v___y_1426_, v___y_1427_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1___boxed(lean_object* v_00_u03b1_1430_, lean_object* v_preNode_1431_, lean_object* v_postNode_1432_, lean_object* v_x_1433_, lean_object* v_x_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l___private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1(v_00_u03b1_1430_, v_preNode_1431_, v_postNode_1432_, v_x_1433_, v_x_1434_, v___y_1435_, v___y_1436_);
lean_dec_ref(v___y_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3(lean_object* v_00_u03b1_1439_, lean_object* v_preNode_1440_, lean_object* v_postNode_1441_, lean_object* v___x_1442_, lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3___redArg(v_preNode_1440_, v_postNode_1441_, v___x_1442_, v_x_1443_, v_x_1444_, v___y_1445_, v___y_1446_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3___boxed(lean_object* v_00_u03b1_1449_, lean_object* v_preNode_1450_, lean_object* v_postNode_1451_, lean_object* v___x_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_List_mapM_loop___at___00__private_Lean_Elab_InfoTree_Util_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__1_spec__1_spec__3(v_00_u03b1_1449_, v_preNode_1450_, v_postNode_1451_, v___x_1452_, v_x_1453_, v_x_1454_, v___y_1455_, v___y_1456_);
lean_dec_ref(v___y_1456_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(lean_object* v___x_1461_, lean_object* v___x_1462_, lean_object* v_as_1463_, size_t v_sz_1464_, size_t v_i_1465_, lean_object* v_b_1466_){
_start:
{
uint8_t v___x_1468_; 
v___x_1468_ = lean_usize_dec_lt(v_i_1465_, v_sz_1464_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1469_, 0, v_b_1466_);
return v___x_1469_;
}
else
{
lean_object* v_snd_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1513_; 
v_snd_1470_ = lean_ctor_get(v_b_1466_, 1);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_b_1466_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v_b_1466_, 0);
lean_dec(v_unused_1514_);
v___x_1472_ = v_b_1466_;
v_isShared_1473_ = v_isSharedCheck_1513_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_snd_1470_);
lean_dec(v_b_1466_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1513_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v_fst_1474_; lean_object* v_snd_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1512_; 
v_fst_1474_ = lean_ctor_get(v_snd_1470_, 0);
v_snd_1475_ = lean_ctor_get(v_snd_1470_, 1);
v_isSharedCheck_1512_ = !lean_is_exclusive(v_snd_1470_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1477_ = v_snd_1470_;
v_isShared_1478_ = v_isSharedCheck_1512_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_snd_1475_);
lean_inc(v_fst_1474_);
lean_dec(v_snd_1470_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1512_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v_a_1479_; 
v_a_1479_ = lean_array_uget_borrowed(v_as_1463_, v_i_1465_);
if (lean_obj_tag(v_a_1479_) == 0)
{
lean_object* v_range_1480_; lean_object* v_text_1481_; lean_object* v_mod_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_range_1480_ = lean_ctor_get(v_a_1479_, 0);
v_text_1481_ = lean_ctor_get(v_a_1479_, 1);
v_mod_1482_ = lean_ctor_get(v___x_1462_, 1);
v___x_1483_ = lean_box(0);
lean_inc_ref(v_range_1480_);
v___x_1484_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1461_, v_range_1480_);
lean_inc(v_fst_1474_);
v___x_1485_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(v_mod_1482_, v_fst_1474_, v___x_1484_, v_text_1481_);
if (lean_obj_tag(v___x_1485_) == 1)
{
lean_object* v_val_1486_; lean_object* v___x_1488_; 
lean_dec(v_fst_1474_);
v_val_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v___x_1485_, 1);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v_val_1486_);
v___x_1488_ = v___x_1477_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_val_1486_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v_snd_1475_);
v___x_1488_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1488_);
lean_ctor_set(v___x_1472_, 0, v___x_1483_);
v___x_1490_ = v___x_1472_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
size_t v___x_1491_; size_t v___x_1492_; 
v___x_1491_ = ((size_t)1ULL);
v___x_1492_ = lean_usize_add(v_i_1465_, v___x_1491_);
v_i_1465_ = v___x_1492_;
v_b_1466_ = v___x_1490_;
goto _start;
}
}
}
else
{
lean_object* v___x_1496_; lean_object* v___x_1498_; 
lean_dec(v___x_1485_);
lean_dec(v_snd_1475_);
v___x_1496_ = lean_box(v___x_1468_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___x_1496_);
v___x_1498_ = v___x_1477_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_fst_1474_);
lean_ctor_set(v_reuseFailAlloc_1503_, 1, v___x_1496_);
v___x_1498_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
lean_object* v___x_1500_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1498_);
lean_ctor_set(v___x_1472_, 0, v___x_1483_);
v___x_1500_ = v___x_1472_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1502_, 1, v___x_1498_);
v___x_1500_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
lean_object* v___x_1501_; 
v___x_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1501_, 0, v___x_1500_);
return v___x_1501_;
}
}
}
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1506_; 
v___x_1504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0));
if (v_isShared_1478_ == 0)
{
v___x_1506_ = v___x_1477_;
goto v_reusejp_1505_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_fst_1474_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v_snd_1475_);
v___x_1506_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1505_;
}
v_reusejp_1505_:
{
lean_object* v___x_1508_; 
if (v_isShared_1473_ == 0)
{
lean_ctor_set(v___x_1472_, 1, v___x_1506_);
lean_ctor_set(v___x_1472_, 0, v___x_1504_);
v___x_1508_ = v___x_1472_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1504_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1506_);
v___x_1508_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
return v___x_1509_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___boxed(lean_object* v___x_1515_, lean_object* v___x_1516_, lean_object* v_as_1517_, lean_object* v_sz_1518_, lean_object* v_i_1519_, lean_object* v_b_1520_, lean_object* v___y_1521_){
_start:
{
size_t v_sz_boxed_1522_; size_t v_i_boxed_1523_; lean_object* v_res_1524_; 
v_sz_boxed_1522_ = lean_unbox_usize(v_sz_1518_);
lean_dec(v_sz_1518_);
v_i_boxed_1523_ = lean_unbox_usize(v_i_1519_);
lean_dec(v_i_1519_);
v_res_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1515_, v___x_1516_, v_as_1517_, v_sz_boxed_1522_, v_i_boxed_1523_, v_b_1520_);
lean_dec_ref(v_as_1517_);
lean_dec_ref(v___x_1516_);
lean_dec_ref(v___x_1515_);
return v_res_1524_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(lean_object* v_p_1525_, lean_object* v___x_1526_, lean_object* v___x_1527_, lean_object* v_as_1528_, size_t v_sz_1529_, size_t v_i_1530_, lean_object* v_b_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_a_1535_; uint8_t v___x_1539_; 
v___x_1539_ = lean_usize_dec_lt(v_i_1530_, v_sz_1529_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1540_, 0, v_b_1531_);
return v___x_1540_;
}
else
{
lean_object* v_snd_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1605_; 
v_snd_1541_ = lean_ctor_get(v_b_1531_, 1);
v_isSharedCheck_1605_ = !lean_is_exclusive(v_b_1531_);
if (v_isSharedCheck_1605_ == 0)
{
lean_object* v_unused_1606_; 
v_unused_1606_ = lean_ctor_get(v_b_1531_, 0);
lean_dec(v_unused_1606_);
v___x_1543_ = v_b_1531_;
v_isShared_1544_ = v_isSharedCheck_1605_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_snd_1541_);
lean_dec(v_b_1531_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1605_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v_contentChanges_1545_; lean_object* v___x_1546_; lean_object* v_a_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v_contentChanges_1545_ = lean_ctor_get(v_p_1525_, 1);
v___x_1546_ = lean_box(0);
v_a_1547_ = lean_array_uget_borrowed(v_as_1528_, v_i_1530_);
v___x_1548_ = 0;
v___x_1549_ = lean_box(v___x_1548_);
lean_inc(v_a_1547_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 1, v___x_1549_);
lean_ctor_set(v___x_1543_, 0, v_a_1547_);
v___x_1551_ = v___x_1543_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_a_1547_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
lean_object* v___x_1552_; size_t v_sz_1553_; size_t v___x_1554_; lean_object* v___x_1555_; 
v___x_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1546_);
lean_ctor_set(v___x_1552_, 1, v___x_1551_);
v_sz_1553_ = lean_array_size(v_contentChanges_1545_);
v___x_1554_ = ((size_t)0ULL);
v___x_1555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1526_, v___x_1527_, v_contentChanges_1545_, v_sz_1553_, v___x_1554_, v___x_1552_);
if (lean_obj_tag(v___x_1555_) == 0)
{
lean_object* v_a_1556_; lean_object* v___x_1558_; uint8_t v_isShared_1559_; uint8_t v_isSharedCheck_1595_; 
v_a_1556_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1558_ = v___x_1555_;
v_isShared_1559_ = v_isSharedCheck_1595_;
goto v_resetjp_1557_;
}
else
{
lean_inc(v_a_1556_);
lean_dec(v___x_1555_);
v___x_1558_ = lean_box(0);
v_isShared_1559_ = v_isSharedCheck_1595_;
goto v_resetjp_1557_;
}
v_resetjp_1557_:
{
lean_object* v_fst_1560_; 
v_fst_1560_ = lean_ctor_get(v_a_1556_, 0);
if (lean_obj_tag(v_fst_1560_) == 0)
{
lean_object* v_snd_1561_; lean_object* v_snd_1562_; uint8_t v___x_1563_; 
lean_del_object(v___x_1558_);
v_snd_1561_ = lean_ctor_get(v_a_1556_, 1);
lean_inc(v_snd_1561_);
lean_dec(v_a_1556_);
v_snd_1562_ = lean_ctor_get(v_snd_1561_, 1);
v___x_1563_ = lean_unbox(v_snd_1562_);
if (v___x_1563_ == 0)
{
lean_object* v_fst_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1572_; 
v_fst_1564_ = lean_ctor_get(v_snd_1561_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v_snd_1561_);
if (v_isSharedCheck_1572_ == 0)
{
lean_object* v_unused_1573_; 
v_unused_1573_ = lean_ctor_get(v_snd_1561_, 1);
lean_dec(v_unused_1573_);
v___x_1566_ = v_snd_1561_;
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_fst_1564_);
lean_dec(v_snd_1561_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1572_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_array_push(v_snd_1541_, v_fst_1564_);
if (v_isShared_1567_ == 0)
{
lean_ctor_set(v___x_1566_, 1, v___x_1568_);
lean_ctor_set(v___x_1566_, 0, v___x_1546_);
v___x_1570_ = v___x_1566_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
v_a_1535_ = v___x_1570_;
goto v___jp_1534_;
}
}
}
else
{
lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_isSharedCheck_1580_ = !lean_is_exclusive(v_snd_1561_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; 
v_unused_1581_ = lean_ctor_get(v_snd_1561_, 1);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_snd_1561_, 0);
lean_dec(v_unused_1582_);
v___x_1575_ = v_snd_1561_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_dec(v_snd_1561_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v_snd_1541_);
lean_ctor_set(v___x_1575_, 0, v___x_1546_);
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_snd_1541_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
v_a_1535_ = v___x_1578_;
goto v___jp_1534_;
}
}
}
}
else
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1592_; 
lean_inc_ref(v_fst_1560_);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_a_1556_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; lean_object* v_unused_1594_; 
v_unused_1593_ = lean_ctor_get(v_a_1556_, 1);
lean_dec(v_unused_1593_);
v_unused_1594_ = lean_ctor_get(v_a_1556_, 0);
lean_dec(v_unused_1594_);
v___x_1584_ = v_a_1556_;
v_isShared_1585_ = v_isSharedCheck_1592_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v_a_1556_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1592_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 1, v_snd_1541_);
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_fst_1560_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_snd_1541_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
lean_object* v___x_1589_; 
if (v_isShared_1559_ == 0)
{
lean_ctor_set(v___x_1558_, 0, v___x_1587_);
v___x_1589_ = v___x_1558_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v___x_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
}
}
else
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
lean_dec(v_snd_1541_);
v_a_1596_ = lean_ctor_get(v___x_1555_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1555_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v___x_1555_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v___x_1555_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
}
}
}
v___jp_1534_:
{
size_t v___x_1536_; size_t v___x_1537_; 
v___x_1536_ = ((size_t)1ULL);
v___x_1537_ = lean_usize_add(v_i_1530_, v___x_1536_);
v_i_1530_ = v___x_1537_;
v_b_1531_ = v_a_1535_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1___boxed(lean_object* v_p_1607_, lean_object* v___x_1608_, lean_object* v___x_1609_, lean_object* v_as_1610_, lean_object* v_sz_1611_, lean_object* v_i_1612_, lean_object* v_b_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
size_t v_sz_boxed_1616_; size_t v_i_boxed_1617_; lean_object* v_res_1618_; 
v_sz_boxed_1616_ = lean_unbox_usize(v_sz_1611_);
lean_dec(v_sz_1611_);
v_i_boxed_1617_ = lean_unbox_usize(v_i_1612_);
lean_dec(v_i_1612_);
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1607_, v___x_1608_, v___x_1609_, v_as_1610_, v_sz_boxed_1616_, v_i_boxed_1617_, v_b_1613_, v___y_1614_);
lean_dec_ref(v___y_1614_);
lean_dec_ref(v_as_1610_);
lean_dec_ref(v___x_1609_);
lean_dec_ref(v___x_1608_);
lean_dec_ref(v_p_1607_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(lean_object* v_p_1622_, lean_object* v_oldInlayHints_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v_doc_1626_; lean_object* v_toEditableDocumentCore_1627_; lean_object* v_meta_1628_; lean_object* v_text_1629_; lean_object* v___x_1630_; size_t v_sz_1631_; size_t v___x_1632_; lean_object* v___x_1633_; 
v_doc_1626_ = lean_ctor_get(v_a_1624_, 1);
v_toEditableDocumentCore_1627_ = lean_ctor_get(v_doc_1626_, 0);
v_meta_1628_ = lean_ctor_get(v_toEditableDocumentCore_1627_, 0);
v_text_1629_ = lean_ctor_get(v_meta_1628_, 3);
v___x_1630_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0));
v_sz_1631_ = lean_array_size(v_oldInlayHints_1623_);
v___x_1632_ = ((size_t)0ULL);
v___x_1633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1622_, v_text_1629_, v_meta_1628_, v_oldInlayHints_1623_, v_sz_1631_, v___x_1632_, v___x_1630_, v_a_1624_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1647_; 
v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1636_ = v___x_1633_;
v_isShared_1637_ = v_isSharedCheck_1647_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1633_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1647_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v_fst_1638_; 
v_fst_1638_ = lean_ctor_get(v_a_1634_, 0);
if (lean_obj_tag(v_fst_1638_) == 0)
{
lean_object* v_snd_1639_; lean_object* v___x_1641_; 
v_snd_1639_ = lean_ctor_get(v_a_1634_, 1);
lean_inc(v_snd_1639_);
lean_dec(v_a_1634_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_snd_1639_);
v___x_1641_ = v___x_1636_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_snd_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
return v___x_1641_;
}
}
else
{
lean_object* v_val_1643_; lean_object* v___x_1645_; 
lean_inc_ref(v_fst_1638_);
lean_dec(v_a_1634_);
v_val_1643_ = lean_ctor_get(v_fst_1638_, 0);
lean_inc(v_val_1643_);
lean_dec_ref_known(v_fst_1638_, 1);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 0, v_val_1643_);
v___x_1645_ = v___x_1636_;
goto v_reusejp_1644_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_val_1643_);
v___x_1645_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1644_;
}
v_reusejp_1644_:
{
return v___x_1645_;
}
}
}
}
else
{
lean_object* v_a_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1655_; 
v_a_1648_ = lean_ctor_get(v___x_1633_, 0);
v_isSharedCheck_1655_ = !lean_is_exclusive(v___x_1633_);
if (v_isSharedCheck_1655_ == 0)
{
v___x_1650_ = v___x_1633_;
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_a_1648_);
lean_dec(v___x_1633_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1655_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1654_; 
v_reuseFailAlloc_1654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1654_, 0, v_a_1648_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___boxed(lean_object* v_p_1656_, lean_object* v_oldInlayHints_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1656_, v_oldInlayHints_1657_, v_a_1658_);
lean_dec_ref(v_a_1658_);
lean_dec_ref(v_oldInlayHints_1657_);
lean_dec_ref(v_p_1656_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(lean_object* v___x_1661_, lean_object* v___x_1662_, lean_object* v_as_1663_, size_t v_sz_1664_, size_t v_i_1665_, lean_object* v_b_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1661_, v___x_1662_, v_as_1663_, v_sz_1664_, v_i_1665_, v_b_1666_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___boxed(lean_object* v___x_1670_, lean_object* v___x_1671_, lean_object* v_as_1672_, lean_object* v_sz_1673_, lean_object* v_i_1674_, lean_object* v_b_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
size_t v_sz_boxed_1678_; size_t v_i_boxed_1679_; lean_object* v_res_1680_; 
v_sz_boxed_1678_ = lean_unbox_usize(v_sz_1673_);
lean_dec(v_sz_1673_);
v_i_boxed_1679_ = lean_unbox_usize(v_i_1674_);
lean_dec(v_i_1674_);
v_res_1680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(v___x_1670_, v___x_1671_, v_as_1672_, v_sz_boxed_1678_, v_i_boxed_1679_, v_b_1675_, v___y_1676_);
lean_dec_ref(v___y_1676_);
lean_dec_ref(v_as_1672_);
lean_dec_ref(v___x_1671_);
lean_dec_ref(v___x_1670_);
return v_res_1680_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(lean_object* v_a_1681_, lean_object* v_as_1682_, size_t v_i_1683_, size_t v_stop_1684_){
_start:
{
uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_eq(v_i_1683_, v_stop_1684_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; uint8_t v___x_1687_; 
v___x_1686_ = lean_array_uget_borrowed(v_as_1682_, v_i_1683_);
v___x_1687_ = l_Lean_Elab_instBEqInlayHintTextEdit_beq(v_a_1681_, v___x_1686_);
if (v___x_1687_ == 0)
{
size_t v___x_1688_; size_t v___x_1689_; 
v___x_1688_ = ((size_t)1ULL);
v___x_1689_ = lean_usize_add(v_i_1683_, v___x_1688_);
v_i_1683_ = v___x_1689_;
goto _start;
}
else
{
return v___x_1687_;
}
}
else
{
uint8_t v___x_1691_; 
v___x_1691_ = 0;
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0___boxed(lean_object* v_a_1692_, lean_object* v_as_1693_, lean_object* v_i_1694_, lean_object* v_stop_1695_){
_start:
{
size_t v_i_boxed_1696_; size_t v_stop_boxed_1697_; uint8_t v_res_1698_; lean_object* v_r_1699_; 
v_i_boxed_1696_ = lean_unbox_usize(v_i_1694_);
lean_dec(v_i_1694_);
v_stop_boxed_1697_ = lean_unbox_usize(v_stop_1695_);
lean_dec(v_stop_1695_);
v_res_1698_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1692_, v_as_1693_, v_i_boxed_1696_, v_stop_boxed_1697_);
lean_dec_ref(v_as_1693_);
lean_dec_ref(v_a_1692_);
v_r_1699_ = lean_box(v_res_1698_);
return v_r_1699_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(lean_object* v_as_1700_, lean_object* v_a_1701_){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = lean_array_get_size(v_as_1700_);
v___x_1704_ = lean_nat_dec_lt(v___x_1702_, v___x_1703_);
if (v___x_1704_ == 0)
{
return v___x_1704_;
}
else
{
size_t v___x_1705_; size_t v___x_1706_; uint8_t v___x_1707_; 
v___x_1705_ = ((size_t)0ULL);
v___x_1706_ = lean_usize_of_nat(v___x_1703_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1701_, v_as_1700_, v___x_1705_, v___x_1706_);
return v___x_1707_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0___boxed(lean_object* v_as_1708_, lean_object* v_a_1709_){
_start:
{
uint8_t v_res_1710_; lean_object* v_r_1711_; 
v_res_1710_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_as_1708_, v_a_1709_);
lean_dec_ref(v_a_1709_);
lean_dec_ref(v_as_1708_);
v_r_1711_ = lean_box(v_res_1710_);
return v_r_1711_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(lean_object* v___x_1712_, lean_object* v_as_1713_, size_t v_i_1714_, size_t v_stop_1715_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_usize_dec_eq(v_i_1714_, v_stop_1715_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v_textEdits_1718_; uint8_t v___x_1719_; 
v___x_1717_ = lean_array_uget_borrowed(v_as_1713_, v_i_1714_);
v_textEdits_1718_ = lean_ctor_get(v___x_1717_, 3);
v___x_1719_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_textEdits_1718_, v___x_1712_);
if (v___x_1719_ == 0)
{
size_t v___x_1720_; size_t v___x_1721_; 
v___x_1720_ = ((size_t)1ULL);
v___x_1721_ = lean_usize_add(v_i_1714_, v___x_1720_);
v_i_1714_ = v___x_1721_;
goto _start;
}
else
{
return v___x_1719_;
}
}
else
{
uint8_t v___x_1723_; 
v___x_1723_ = 0;
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1___boxed(lean_object* v___x_1724_, lean_object* v_as_1725_, lean_object* v_i_1726_, lean_object* v_stop_1727_){
_start:
{
size_t v_i_boxed_1728_; size_t v_stop_boxed_1729_; uint8_t v_res_1730_; lean_object* v_r_1731_; 
v_i_boxed_1728_ = lean_unbox_usize(v_i_1726_);
lean_dec(v_i_1726_);
v_stop_boxed_1729_ = lean_unbox_usize(v_stop_1727_);
lean_dec(v_stop_1727_);
v_res_1730_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1724_, v_as_1725_, v_i_boxed_1728_, v_stop_boxed_1729_);
lean_dec_ref(v_as_1725_);
lean_dec_ref(v___x_1724_);
v_r_1731_ = lean_box(v_res_1730_);
return v_r_1731_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(lean_object* v_oldInlayHints_1732_, lean_object* v___x_1733_, lean_object* v___x_1734_, lean_object* v_as_1735_, size_t v_i_1736_, size_t v_stop_1737_){
_start:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_usize_dec_eq(v_i_1736_, v_stop_1737_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; uint8_t v___x_1744_; uint8_t v___x_1745_; lean_object* v___x_1747_; 
v___x_1743_ = lean_unsigned_to_nat(0u);
v___x_1744_ = lean_nat_dec_lt(v___x_1743_, v___x_1733_);
v___x_1745_ = 1;
v___x_1747_ = lean_array_uget(v_as_1735_, v_i_1736_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_range_1748_; lean_object* v_text_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1762_; 
v_range_1748_ = lean_ctor_get(v___x_1747_, 0);
v_text_1749_ = lean_ctor_get(v___x_1747_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1747_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1751_ = v___x_1747_;
v_isShared_1752_ = v_isSharedCheck_1762_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_text_1749_);
lean_inc(v_range_1748_);
lean_dec(v___x_1747_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1762_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1753_ = lean_array_get_size(v_oldInlayHints_1732_);
v___x_1754_ = lean_nat_dec_lt(v___x_1743_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_del_object(v___x_1751_);
lean_dec_ref(v_text_1749_);
lean_dec_ref(v_range_1748_);
goto v___jp_1746_;
}
else
{
if (v___x_1754_ == 0)
{
lean_del_object(v___x_1751_);
lean_dec_ref(v_text_1749_);
lean_dec_ref(v_range_1748_);
return v___x_1745_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1757_; 
v___x_1755_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1734_, v_range_1748_);
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1755_);
v___x_1757_ = v___x_1751_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1755_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_text_1749_);
v___x_1757_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
size_t v___x_1758_; size_t v___x_1759_; uint8_t v___x_1760_; 
v___x_1758_ = ((size_t)0ULL);
v___x_1759_ = lean_usize_of_nat(v___x_1753_);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1757_, v_oldInlayHints_1732_, v___x_1758_, v___x_1759_);
lean_dec_ref(v___x_1757_);
if (v___x_1760_ == 0)
{
return v___x_1745_;
}
else
{
goto v___jp_1738_;
}
}
}
}
}
}
else
{
lean_dec(v___x_1747_);
goto v___jp_1746_;
}
v___jp_1746_:
{
if (v___x_1744_ == 0)
{
goto v___jp_1738_;
}
else
{
return v___x_1745_;
}
}
}
else
{
uint8_t v___x_1763_; 
v___x_1763_ = 0;
return v___x_1763_;
}
v___jp_1738_:
{
size_t v___x_1739_; size_t v___x_1740_; 
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_i_1736_, v___x_1739_);
v_i_1736_ = v___x_1740_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2___boxed(lean_object* v_oldInlayHints_1764_, lean_object* v___x_1765_, lean_object* v___x_1766_, lean_object* v_as_1767_, lean_object* v_i_1768_, lean_object* v_stop_1769_){
_start:
{
size_t v_i_boxed_1770_; size_t v_stop_boxed_1771_; uint8_t v_res_1772_; lean_object* v_r_1773_; 
v_i_boxed_1770_ = lean_unbox_usize(v_i_1768_);
lean_dec(v_i_1768_);
v_stop_boxed_1771_ = lean_unbox_usize(v_stop_1769_);
lean_dec(v_stop_1769_);
v_res_1772_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1764_, v___x_1765_, v___x_1766_, v_as_1767_, v_i_boxed_1770_, v_stop_boxed_1771_);
lean_dec_ref(v_as_1767_);
lean_dec_ref(v___x_1766_);
lean_dec(v___x_1765_);
lean_dec_ref(v_oldInlayHints_1764_);
v_r_1773_ = lean_box(v_res_1772_);
return v_r_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(lean_object* v_p_1774_, lean_object* v_oldInlayHints_1775_, lean_object* v_a_1776_){
_start:
{
uint8_t v___y_1779_; lean_object* v_contentChanges_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; uint8_t v___x_1788_; 
v_contentChanges_1785_ = lean_ctor_get(v_p_1774_, 1);
v___x_1786_ = lean_unsigned_to_nat(0u);
v___x_1787_ = lean_array_get_size(v_contentChanges_1785_);
v___x_1788_ = lean_nat_dec_lt(v___x_1786_, v___x_1787_);
if (v___x_1788_ == 0)
{
uint8_t v___x_1789_; 
v___x_1789_ = 1;
v___y_1779_ = v___x_1789_;
goto v___jp_1778_;
}
else
{
if (v___x_1788_ == 0)
{
v___y_1779_ = v___x_1788_;
goto v___jp_1778_;
}
else
{
lean_object* v_doc_1790_; lean_object* v_toEditableDocumentCore_1791_; lean_object* v_meta_1792_; lean_object* v_text_1793_; size_t v___x_1794_; size_t v___x_1795_; uint8_t v___x_1796_; 
v_doc_1790_ = lean_ctor_get(v_a_1776_, 1);
v_toEditableDocumentCore_1791_ = lean_ctor_get(v_doc_1790_, 0);
v_meta_1792_ = lean_ctor_get(v_toEditableDocumentCore_1791_, 0);
v_text_1793_ = lean_ctor_get(v_meta_1792_, 3);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = lean_usize_of_nat(v___x_1787_);
v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1775_, v___x_1787_, v_text_1793_, v_contentChanges_1785_, v___x_1794_, v___x_1795_);
if (v___x_1796_ == 0)
{
v___y_1779_ = v___x_1788_;
goto v___jp_1778_;
}
else
{
uint8_t v___x_1797_; 
v___x_1797_ = 0;
v___y_1779_ = v___x_1797_;
goto v___jp_1778_;
}
}
}
v___jp_1778_:
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_io_mono_ms_now();
if (v___y_1779_ == 0)
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
v___x_1782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
else
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
lean_dec(v___x_1780_);
v___x_1783_ = lean_box(0);
v___x_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1784_, 0, v___x_1783_);
return v___x_1784_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___boxed(lean_object* v_p_1798_, lean_object* v_oldInlayHints_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1798_, v_oldInlayHints_1799_, v_a_1800_);
lean_dec_ref(v_a_1800_);
lean_dec_ref(v_oldInlayHints_1799_);
lean_dec_ref(v_p_1798_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange(lean_object* v_p_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_oldInlayHints_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1837_; 
v_oldInlayHints_1807_ = lean_ctor_get(v_a_1804_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_a_1804_);
if (v_isSharedCheck_1837_ == 0)
{
lean_object* v_unused_1838_; lean_object* v_unused_1839_; 
v_unused_1838_ = lean_ctor_get(v_a_1804_, 2);
lean_dec(v_unused_1838_);
v_unused_1839_ = lean_ctor_get(v_a_1804_, 1);
lean_dec(v_unused_1839_);
v___x_1809_ = v_a_1804_;
v_isShared_1810_ = v_isSharedCheck_1837_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_oldInlayHints_1807_);
lean_dec(v_a_1804_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1837_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; 
v___x_1811_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1803_, v_oldInlayHints_1807_, v_a_1805_);
if (lean_obj_tag(v___x_1811_) == 0)
{
lean_object* v_a_1812_; lean_object* v___x_1813_; lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1828_; 
v_a_1812_ = lean_ctor_get(v___x_1811_, 0);
lean_inc(v_a_1812_);
lean_dec_ref_known(v___x_1811_, 1);
v___x_1813_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1803_, v_oldInlayHints_1807_, v_a_1805_);
lean_dec_ref(v_oldInlayHints_1807_);
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1828_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1828_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1828_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1828_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1821_; 
v___x_1818_ = lean_unsigned_to_nat(0u);
v___x_1819_ = 1;
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 2, v_a_1814_);
lean_ctor_set(v___x_1809_, 1, v___x_1818_);
lean_ctor_set(v___x_1809_, 0, v_a_1812_);
v___x_1821_ = v___x_1809_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_a_1812_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v___x_1818_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_a_1814_);
v___x_1821_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*3, v___x_1819_);
v___x_1822_ = lean_box(0);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1821_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1823_);
v___x_1825_ = v___x_1816_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
else
{
lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1836_; 
lean_del_object(v___x_1809_);
lean_dec_ref(v_oldInlayHints_1807_);
v_a_1829_ = lean_ctor_get(v___x_1811_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1811_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1831_ = v___x_1811_;
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1811_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1836_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1834_; 
if (v_isShared_1832_ == 0)
{
v___x_1834_ = v___x_1831_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_a_1829_);
v___x_1834_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
return v___x_1834_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed(lean_object* v_p_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_Server_FileWorker_handleInlayHintsDidChange(v_p_1840_, v_a_1841_, v_a_1842_);
lean_dec_ref(v_a_1842_);
lean_dec_ref(v_p_1840_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(lean_object* v___x_1845_, lean_object* v_x_1846_){
_start:
{
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed(lean_object* v___x_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(v___x_1847_, v_x_1848_);
lean_dec_ref(v_x_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1850_, lean_object* v_x_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_){
_start:
{
lean_object* v_ks_1854_; lean_object* v_vs_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1879_; 
v_ks_1854_ = lean_ctor_get(v_x_1850_, 0);
v_vs_1855_ = lean_ctor_get(v_x_1850_, 1);
v_isSharedCheck_1879_ = !lean_is_exclusive(v_x_1850_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1857_ = v_x_1850_;
v_isShared_1858_ = v_isSharedCheck_1879_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_vs_1855_);
lean_inc(v_ks_1854_);
lean_dec(v_x_1850_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1879_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; uint8_t v___x_1860_; 
v___x_1859_ = lean_array_get_size(v_ks_1854_);
v___x_1860_ = lean_nat_dec_lt(v_x_1851_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1864_; 
lean_dec(v_x_1851_);
v___x_1861_ = lean_array_push(v_ks_1854_, v_x_1852_);
v___x_1862_ = lean_array_push(v_vs_1855_, v_x_1853_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v___x_1862_);
lean_ctor_set(v___x_1857_, 0, v___x_1861_);
v___x_1864_ = v___x_1857_;
goto v_reusejp_1863_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1862_);
v___x_1864_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1863_;
}
v_reusejp_1863_:
{
return v___x_1864_;
}
}
else
{
lean_object* v_k_x27_1866_; uint8_t v___x_1867_; 
v_k_x27_1866_ = lean_array_fget_borrowed(v_ks_1854_, v_x_1851_);
v___x_1867_ = lean_string_dec_eq(v_x_1852_, v_k_x27_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1869_; 
if (v_isShared_1858_ == 0)
{
v___x_1869_ = v___x_1857_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_ks_1854_);
lean_ctor_set(v_reuseFailAlloc_1873_, 1, v_vs_1855_);
v___x_1869_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = lean_unsigned_to_nat(1u);
v___x_1871_ = lean_nat_add(v_x_1851_, v___x_1870_);
lean_dec(v_x_1851_);
v_x_1850_ = v___x_1869_;
v_x_1851_ = v___x_1871_;
goto _start;
}
}
else
{
lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1877_; 
v___x_1874_ = lean_array_fset(v_ks_1854_, v_x_1851_, v_x_1852_);
v___x_1875_ = lean_array_fset(v_vs_1855_, v_x_1851_, v_x_1853_);
lean_dec(v_x_1851_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v___x_1875_);
lean_ctor_set(v___x_1857_, 0, v___x_1874_);
v___x_1877_ = v___x_1857_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v___x_1874_);
lean_ctor_set(v_reuseFailAlloc_1878_, 1, v___x_1875_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(lean_object* v_n_1880_, lean_object* v_k_1881_, lean_object* v_v_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_n_1880_, v___x_1883_, v_k_1881_, v_v_1882_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(lean_object* v_x_1886_, size_t v_x_1887_, size_t v_x_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_){
_start:
{
if (lean_obj_tag(v_x_1886_) == 0)
{
lean_object* v_es_1891_; size_t v___x_1892_; size_t v___x_1893_; lean_object* v_j_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v_es_1891_ = lean_ctor_get(v_x_1886_, 0);
v___x_1892_ = ((size_t)31ULL);
v___x_1893_ = lean_usize_land(v_x_1887_, v___x_1892_);
v_j_1894_ = lean_usize_to_nat(v___x_1893_);
v___x_1895_ = lean_array_get_size(v_es_1891_);
v___x_1896_ = lean_nat_dec_lt(v_j_1894_, v___x_1895_);
if (v___x_1896_ == 0)
{
lean_dec(v_j_1894_);
lean_dec(v_x_1890_);
lean_dec_ref(v_x_1889_);
return v_x_1886_;
}
else
{
lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1935_; 
lean_inc_ref(v_es_1891_);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_x_1886_);
if (v_isSharedCheck_1935_ == 0)
{
lean_object* v_unused_1936_; 
v_unused_1936_ = lean_ctor_get(v_x_1886_, 0);
lean_dec(v_unused_1936_);
v___x_1898_ = v_x_1886_;
v_isShared_1899_ = v_isSharedCheck_1935_;
goto v_resetjp_1897_;
}
else
{
lean_dec(v_x_1886_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1935_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v_v_1900_; lean_object* v___x_1901_; lean_object* v_xs_x27_1902_; lean_object* v___y_1904_; 
v_v_1900_ = lean_array_fget(v_es_1891_, v_j_1894_);
v___x_1901_ = lean_box(0);
v_xs_x27_1902_ = lean_array_fset(v_es_1891_, v_j_1894_, v___x_1901_);
switch(lean_obj_tag(v_v_1900_))
{
case 0:
{
lean_object* v_key_1909_; lean_object* v_val_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1920_; 
v_key_1909_ = lean_ctor_get(v_v_1900_, 0);
v_val_1910_ = lean_ctor_get(v_v_1900_, 1);
v_isSharedCheck_1920_ = !lean_is_exclusive(v_v_1900_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1912_ = v_v_1900_;
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_val_1910_);
lean_inc(v_key_1909_);
lean_dec(v_v_1900_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1920_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
uint8_t v___x_1914_; 
v___x_1914_ = lean_string_dec_eq(v_x_1889_, v_key_1909_);
if (v___x_1914_ == 0)
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
lean_del_object(v___x_1912_);
v___x_1915_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1909_, v_val_1910_, v_x_1889_, v_x_1890_);
v___x_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
v___y_1904_ = v___x_1916_;
goto v___jp_1903_;
}
else
{
lean_object* v___x_1918_; 
lean_dec(v_val_1910_);
lean_dec(v_key_1909_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v_x_1890_);
lean_ctor_set(v___x_1912_, 0, v_x_1889_);
v___x_1918_ = v___x_1912_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_x_1889_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_x_1890_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
v___y_1904_ = v___x_1918_;
goto v___jp_1903_;
}
}
}
}
case 1:
{
lean_object* v_node_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1933_; 
v_node_1921_ = lean_ctor_get(v_v_1900_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_v_1900_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1923_ = v_v_1900_;
v_isShared_1924_ = v_isSharedCheck_1933_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_node_1921_);
lean_dec(v_v_1900_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1933_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1925_ = ((size_t)5ULL);
v___x_1926_ = lean_usize_shift_right(v_x_1887_, v___x_1925_);
v___x_1927_ = ((size_t)1ULL);
v___x_1928_ = lean_usize_add(v_x_1888_, v___x_1927_);
v___x_1929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_node_1921_, v___x_1926_, v___x_1928_, v_x_1889_, v_x_1890_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 0, v___x_1929_);
v___x_1931_ = v___x_1923_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
v___y_1904_ = v___x_1931_;
goto v___jp_1903_;
}
}
}
default: 
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v_x_1889_);
lean_ctor_set(v___x_1934_, 1, v_x_1890_);
v___y_1904_ = v___x_1934_;
goto v___jp_1903_;
}
}
v___jp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = lean_array_fset(v_xs_x27_1902_, v_j_1894_, v___y_1904_);
lean_dec(v_j_1894_);
if (v_isShared_1899_ == 0)
{
lean_ctor_set(v___x_1898_, 0, v___x_1905_);
v___x_1907_ = v___x_1898_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
else
{
lean_object* v_ks_1937_; lean_object* v_vs_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1956_; 
v_ks_1937_ = lean_ctor_get(v_x_1886_, 0);
v_vs_1938_ = lean_ctor_get(v_x_1886_, 1);
v_isSharedCheck_1956_ = !lean_is_exclusive(v_x_1886_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1940_ = v_x_1886_;
v_isShared_1941_ = v_isSharedCheck_1956_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_vs_1938_);
lean_inc(v_ks_1937_);
lean_dec(v_x_1886_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1956_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_ks_1937_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v_vs_1938_);
v___x_1943_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
lean_object* v_newNode_1944_; size_t v___x_1945_; uint8_t v___x_1946_; 
v_newNode_1944_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v___x_1943_, v_x_1889_, v_x_1890_);
v___x_1945_ = ((size_t)7ULL);
v___x_1946_ = lean_usize_dec_le(v___x_1945_, v_x_1888_);
if (v___x_1946_ == 0)
{
lean_object* v___x_1947_; lean_object* v___x_1948_; uint8_t v___x_1949_; 
v___x_1947_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1944_);
v___x_1948_ = lean_unsigned_to_nat(4u);
v___x_1949_ = lean_nat_dec_lt(v___x_1947_, v___x_1948_);
lean_dec(v___x_1947_);
if (v___x_1949_ == 0)
{
lean_object* v_ks_1950_; lean_object* v_vs_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_ks_1950_ = lean_ctor_get(v_newNode_1944_, 0);
lean_inc_ref(v_ks_1950_);
v_vs_1951_ = lean_ctor_get(v_newNode_1944_, 1);
lean_inc_ref(v_vs_1951_);
lean_dec_ref(v_newNode_1944_);
v___x_1952_ = lean_unsigned_to_nat(0u);
v___x_1953_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0);
v___x_1954_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_x_1888_, v_ks_1950_, v_vs_1951_, v___x_1952_, v___x_1953_);
lean_dec_ref(v_vs_1951_);
lean_dec_ref(v_ks_1950_);
return v___x_1954_;
}
else
{
return v_newNode_1944_;
}
}
else
{
return v_newNode_1944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(size_t v_depth_1957_, lean_object* v_keys_1958_, lean_object* v_vals_1959_, lean_object* v_i_1960_, lean_object* v_entries_1961_){
_start:
{
lean_object* v___x_1962_; uint8_t v___x_1963_; 
v___x_1962_ = lean_array_get_size(v_keys_1958_);
v___x_1963_ = lean_nat_dec_lt(v_i_1960_, v___x_1962_);
if (v___x_1963_ == 0)
{
lean_dec(v_i_1960_);
return v_entries_1961_;
}
else
{
lean_object* v_k_1964_; lean_object* v_v_1965_; uint64_t v___x_1966_; size_t v_h_1967_; size_t v___x_1968_; lean_object* v___x_1969_; size_t v___x_1970_; size_t v___x_1971_; size_t v___x_1972_; size_t v_h_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_k_1964_ = lean_array_fget_borrowed(v_keys_1958_, v_i_1960_);
v_v_1965_ = lean_array_fget_borrowed(v_vals_1959_, v_i_1960_);
v___x_1966_ = lean_string_hash(v_k_1964_);
v_h_1967_ = lean_uint64_to_usize(v___x_1966_);
v___x_1968_ = ((size_t)5ULL);
v___x_1969_ = lean_unsigned_to_nat(1u);
v___x_1970_ = ((size_t)1ULL);
v___x_1971_ = lean_usize_sub(v_depth_1957_, v___x_1970_);
v___x_1972_ = lean_usize_mul(v___x_1968_, v___x_1971_);
v_h_1973_ = lean_usize_shift_right(v_h_1967_, v___x_1972_);
v___x_1974_ = lean_nat_add(v_i_1960_, v___x_1969_);
lean_dec(v_i_1960_);
lean_inc(v_v_1965_);
lean_inc(v_k_1964_);
v___x_1975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_entries_1961_, v_h_1973_, v_depth_1957_, v_k_1964_, v_v_1965_);
v_i_1960_ = v___x_1974_;
v_entries_1961_ = v___x_1975_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_depth_1977_, lean_object* v_keys_1978_, lean_object* v_vals_1979_, lean_object* v_i_1980_, lean_object* v_entries_1981_){
_start:
{
size_t v_depth_boxed_1982_; lean_object* v_res_1983_; 
v_depth_boxed_1982_ = lean_unbox_usize(v_depth_1977_);
lean_dec(v_depth_1977_);
v_res_1983_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_boxed_1982_, v_keys_1978_, v_vals_1979_, v_i_1980_, v_entries_1981_);
lean_dec_ref(v_vals_1979_);
lean_dec_ref(v_keys_1978_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_x_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_){
_start:
{
size_t v_x_2491__boxed_1989_; size_t v_x_2492__boxed_1990_; lean_object* v_res_1991_; 
v_x_2491__boxed_1989_ = lean_unbox_usize(v_x_1985_);
lean_dec(v_x_1985_);
v_x_2492__boxed_1990_ = lean_unbox_usize(v_x_1986_);
lean_dec(v_x_1986_);
v_res_1991_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_1984_, v_x_2491__boxed_1989_, v_x_2492__boxed_1990_, v_x_1987_, v_x_1988_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
uint64_t v___x_1995_; size_t v___x_1996_; size_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = lean_string_hash(v_x_1993_);
v___x_1996_ = lean_uint64_to_usize(v___x_1995_);
v___x_1997_ = ((size_t)1ULL);
v___x_1998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_1992_, v___x_1996_, v___x_1997_, v_x_1993_, v_x_1994_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(lean_object* v_mutex_1999_, lean_object* v_a_x3f_2000_){
_start:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_io_basemutex_unlock(v_mutex_1999_);
v___x_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0___boxed(lean_object* v_mutex_2004_, lean_object* v_a_x3f_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2004_, v_a_x3f_2005_);
lean_dec(v_a_x3f_2005_);
lean_dec(v_mutex_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_mutex_2008_, lean_object* v_k_2009_, lean_object* v___y_2010_){
_start:
{
lean_object* v_ref_2012_; lean_object* v_mutex_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v_ref_2012_ = lean_ctor_get(v_mutex_2008_, 0);
lean_inc(v_ref_2012_);
v_mutex_2013_ = lean_ctor_get(v_mutex_2008_, 1);
lean_inc(v_mutex_2013_);
lean_dec_ref(v_mutex_2008_);
v___x_2014_ = lean_io_basemutex_lock(v_mutex_2013_);
lean_inc_ref(v___y_2010_);
v___x_2015_ = lean_apply_3(v_k_2009_, v_ref_2012_, v___y_2010_, lean_box(0));
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2032_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2032_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2018_ = v___x_2015_;
v_isShared_2019_ = v_isSharedCheck_2032_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2015_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2032_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
lean_inc(v_a_2016_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set_tag(v___x_2018_, 1);
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2029_; 
v___x_2022_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2013_, v___x_2021_);
lean_dec_ref(v___x_2021_);
lean_dec(v_mutex_2013_);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2029_ == 0)
{
lean_object* v_unused_2030_; 
v_unused_2030_ = lean_ctor_get(v___x_2022_, 0);
lean_dec(v_unused_2030_);
v___x_2024_ = v___x_2022_;
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v___x_2022_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2029_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v_a_2016_);
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_a_2016_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
else
{
lean_object* v_a_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_a_2033_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2034_ = lean_box(0);
v___x_2035_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2013_, v___x_2034_);
lean_dec(v_mutex_2013_);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2042_ == 0)
{
lean_object* v_unused_2043_; 
v_unused_2043_ = lean_ctor_get(v___x_2035_, 0);
lean_dec(v_unused_2043_);
v___x_2037_ = v___x_2035_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_dec(v___x_2035_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set_tag(v___x_2037_, 1);
lean_ctor_set(v___x_2037_, 0, v_a_2033_);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2033_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_mutex_2044_, lean_object* v_k_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2044_, v_k_2045_, v___y_2046_);
lean_dec_ref(v___y_2046_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(lean_object* v_val_2049_, lean_object* v___f_2050_, lean_object* v_param_2051_, lean_object* v___x_2052_, lean_object* v_x_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = lean_st_ref_get(v_val_2049_);
lean_inc_ref(v___y_2054_);
v___x_2057_ = lean_apply_4(v___f_2050_, v_param_2051_, v___x_2056_, v___y_2054_, lean_box(0));
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2067_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2060_ = v___x_2057_;
v_isShared_2061_ = v_isSharedCheck_2067_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2057_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2067_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v_snd_2062_; lean_object* v___x_2063_; lean_object* v___x_2065_; 
v_snd_2062_ = lean_ctor_get(v_a_2058_, 1);
lean_inc(v_snd_2062_);
lean_dec(v_a_2058_);
v___x_2063_ = lean_st_ref_swap(v_val_2049_, v_snd_2062_);
lean_dec(v___x_2063_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 0, v___x_2052_);
v___x_2065_ = v___x_2060_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2052_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
v_a_2068_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2057_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2057_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed(lean_object* v_val_2076_, lean_object* v___f_2077_, lean_object* v_param_2078_, lean_object* v___x_2079_, lean_object* v_x_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(v_val_2076_, v___f_2077_, v_param_2078_, v___x_2079_, v_x_2080_, v___y_2081_);
lean_dec_ref(v___y_2081_);
lean_dec(v_val_2076_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(lean_object* v___f_2084_, lean_object* v___f_2085_, lean_object* v___x_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = lean_st_ref_get(v___y_2087_);
v___x_2091_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_2090_, v___f_2084_, v___y_2088_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2101_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2101_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2101_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2101_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2099_; 
v___x_2096_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2085_, v_a_2092_);
v___x_2097_ = lean_st_ref_swap(v___y_2087_, v___x_2096_);
lean_dec(v___x_2097_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2086_);
v___x_2099_ = v___x_2094_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2086_);
v___x_2099_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
return v___x_2099_;
}
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
lean_dec_ref(v___f_2085_);
v_a_2102_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2091_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2091_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed(lean_object* v___f_2110_, lean_object* v___f_2111_, lean_object* v___x_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(v___f_2110_, v___f_2111_, v___x_2112_, v___y_2113_, v___y_2114_);
lean_dec_ref(v___y_2114_);
lean_dec(v___y_2113_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(lean_object* v_val_2117_, lean_object* v___f_2118_, lean_object* v___x_2119_, lean_object* v___f_2120_, lean_object* v_val_2121_, lean_object* v_param_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___f_2125_; lean_object* v___f_2126_; lean_object* v___x_2127_; 
v___f_2125_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed), 7, 4);
lean_closure_set(v___f_2125_, 0, v_val_2117_);
lean_closure_set(v___f_2125_, 1, v___f_2118_);
lean_closure_set(v___f_2125_, 2, v_param_2122_);
lean_closure_set(v___f_2125_, 3, v___x_2119_);
v___f_2126_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed), 6, 3);
lean_closure_set(v___f_2126_, 0, v___f_2125_);
lean_closure_set(v___f_2126_, 1, v___f_2120_);
lean_closure_set(v___f_2126_, 2, v___x_2119_);
v___x_2127_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_2121_, v___f_2126_, v___y_2123_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed(lean_object* v_val_2128_, lean_object* v___f_2129_, lean_object* v___x_2130_, lean_object* v___f_2131_, lean_object* v_val_2132_, lean_object* v_param_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(v_val_2128_, v___f_2129_, v___x_2130_, v___f_2131_, v_val_2132_, v_param_2133_, v___y_2134_);
lean_dec_ref(v___y_2134_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(lean_object* v___x_2137_, lean_object* v_x_2138_){
_start:
{
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed(lean_object* v___x_2139_, lean_object* v_x_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4(v___x_2139_, v_x_2140_);
lean_dec_ref(v_x_2140_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(lean_object* v_params_2144_){
_start:
{
lean_object* v___x_2145_; 
lean_inc(v_params_2144_);
v___x_2145_ = l_Lean_Lsp_instFromJsonInlayHintParams_fromJson(v_params_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2161_; 
v_a_2146_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2161_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2161_ == 0)
{
v___x_2148_ = v___x_2145_;
v_isShared_2149_ = v_isSharedCheck_2161_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___x_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2161_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
uint8_t v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2159_; 
v___x_2150_ = 3;
v___x_2151_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2152_ = l_Lean_Json_compress(v_params_2144_);
v___x_2153_ = lean_string_append(v___x_2151_, v___x_2152_);
lean_dec_ref(v___x_2152_);
v___x_2154_ = ((lean_object*)(l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4___closed__1));
v___x_2155_ = lean_string_append(v___x_2153_, v___x_2154_);
v___x_2156_ = lean_string_append(v___x_2155_, v_a_2146_);
lean_dec(v_a_2146_);
v___x_2157_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2157_, 0, v___x_2156_);
lean_ctor_set_uint8(v___x_2157_, sizeof(void*)*1, v___x_2150_);
if (v_isShared_2149_ == 0)
{
lean_ctor_set(v___x_2148_, 0, v___x_2157_);
v___x_2159_ = v___x_2148_;
goto v_reusejp_2158_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2157_);
v___x_2159_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2158_;
}
v_reusejp_2158_:
{
return v___x_2159_;
}
}
}
else
{
lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2169_; 
lean_dec(v_params_2144_);
v_a_2162_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2164_ = v___x_2145_;
v_isShared_2165_ = v_isSharedCheck_2169_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2145_);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0(lean_object* v_j_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_j_2170_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
v_a_2172_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2171_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
else
{
lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2188_; 
v_a_2180_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2182_ = v___x_2171_;
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2171_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2188_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v_textDocument_2184_; lean_object* v___x_2186_; 
v_textDocument_2184_ = lean_ctor_get(v_a_2180_, 1);
lean_inc_ref(v_textDocument_2184_);
lean_dec(v_a_2180_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v_textDocument_2184_);
v___x_2186_ = v___x_2182_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_textDocument_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(lean_object* v_method_2189_, lean_object* v_inst_2190_, lean_object* v_onDidChange_2191_, lean_object* v_param_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2189_, v___y_2193_, lean_box(0), v_inst_2190_, v___y_2194_);
if (lean_obj_tag(v___x_2196_) == 0)
{
lean_object* v_a_2197_; lean_object* v___x_2198_; 
v_a_2197_ = lean_ctor_get(v___x_2196_, 0);
lean_inc(v_a_2197_);
lean_dec_ref_known(v___x_2196_, 1);
lean_inc_ref(v___y_2194_);
v___x_2198_ = lean_apply_4(v_onDidChange_2191_, v_param_2192_, v_a_2197_, v___y_2194_, lean_box(0));
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2217_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2217_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2217_ == 0)
{
v___x_2201_ = v___x_2198_;
v_isShared_2202_ = v_isSharedCheck_2217_;
goto v_resetjp_2200_;
}
else
{
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2217_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v_snd_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2215_; 
v_snd_2203_ = lean_ctor_get(v_a_2199_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_a_2199_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; 
v_unused_2216_ = lean_ctor_get(v_a_2199_, 0);
lean_dec(v_unused_2216_);
v___x_2205_ = v_a_2199_;
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_snd_2203_);
lean_dec(v_a_2199_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2215_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2208_; 
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v_inst_2190_);
v___x_2208_ = v___x_2205_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_inst_2190_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_snd_2203_);
v___x_2208_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2209_ = lean_box(0);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2208_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2210_);
v___x_2212_ = v___x_2201_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2210_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_dec(v_inst_2190_);
v_a_2218_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2198_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2198_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
lean_dec_ref(v_param_2192_);
lean_dec_ref(v_onDidChange_2191_);
lean_dec(v_inst_2190_);
v_a_2226_ = lean_ctor_get(v___x_2196_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2196_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2196_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2196_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed(lean_object* v_method_2234_, lean_object* v_inst_2235_, lean_object* v_onDidChange_2236_, lean_object* v_param_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2(v_method_2234_, v_inst_2235_, v_onDidChange_2236_, v_param_2237_, v___y_2238_, v___y_2239_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v_method_2234_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(size_t v_sz_2242_, size_t v_i_2243_, lean_object* v_bs_2244_){
_start:
{
uint8_t v___x_2245_; 
v___x_2245_ = lean_usize_dec_lt(v_i_2243_, v_sz_2242_);
if (v___x_2245_ == 0)
{
return v_bs_2244_;
}
else
{
lean_object* v_v_2246_; lean_object* v___x_2247_; lean_object* v_bs_x27_2248_; lean_object* v___x_2249_; size_t v___x_2250_; size_t v___x_2251_; lean_object* v___x_2252_; 
v_v_2246_ = lean_array_uget(v_bs_2244_, v_i_2243_);
v___x_2247_ = lean_unsigned_to_nat(0u);
v_bs_x27_2248_ = lean_array_uset(v_bs_2244_, v_i_2243_, v___x_2247_);
v___x_2249_ = l_Lean_Lsp_instToJsonInlayHint_toJson(v_v_2246_);
v___x_2250_ = ((size_t)1ULL);
v___x_2251_ = lean_usize_add(v_i_2243_, v___x_2250_);
v___x_2252_ = lean_array_uset(v_bs_x27_2248_, v_i_2243_, v___x_2249_);
v_i_2243_ = v___x_2251_;
v_bs_2244_ = v___x_2252_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8___boxed(lean_object* v_sz_2254_, lean_object* v_i_2255_, lean_object* v_bs_2256_){
_start:
{
size_t v_sz_boxed_2257_; size_t v_i_boxed_2258_; lean_object* v_res_2259_; 
v_sz_boxed_2257_ = lean_unbox_usize(v_sz_2254_);
lean_dec(v_sz_2254_);
v_i_boxed_2258_ = lean_unbox_usize(v_i_2255_);
lean_dec(v_i_2255_);
v_res_2259_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_boxed_2257_, v_i_boxed_2258_, v_bs_2256_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(lean_object* v_a_2260_){
_start:
{
size_t v_sz_2261_; size_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v_sz_2261_ = lean_array_size(v_a_2260_);
v___x_2262_ = ((size_t)0ULL);
v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6_spec__8(v_sz_2261_, v___x_2262_, v_a_2260_);
v___x_2264_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_params_2265_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Lean_Server_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__4(v_params_2265_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2267_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set_tag(v___x_2270_, 1);
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
v_a_2276_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2267_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2267_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
lean_ctor_set_tag(v___x_2278_, 0);
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
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
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_params_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2284_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(lean_object* v_method_2287_, lean_object* v_inst_2288_, lean_object* v_handler_2289_, lean_object* v_param_2290_, lean_object* v_state_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v___x_2294_; 
v___x_2294_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_param_2290_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; lean_object* v___x_2296_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
v___x_2296_ = l___private_Lean_Server_Requests_0__Lean_Server_getState_x21(v_method_2287_, v_state_2291_, lean_box(0), v_inst_2288_, v___y_2292_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2298_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
lean_inc(v_a_2297_);
lean_dec_ref_known(v___x_2296_, 1);
lean_inc_ref(v___y_2292_);
v___x_2298_ = lean_apply_4(v_handler_2289_, v_a_2295_, v_a_2297_, v___y_2292_, lean_box(0));
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2322_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2322_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2322_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_fst_2303_; lean_object* v_snd_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2321_; 
v_fst_2303_ = lean_ctor_get(v_a_2299_, 0);
v_snd_2304_ = lean_ctor_get(v_a_2299_, 1);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_a_2299_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2306_ = v_a_2299_;
v_isShared_2307_ = v_isSharedCheck_2321_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_snd_2304_);
lean_inc(v_fst_2303_);
lean_dec(v_a_2299_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2321_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_response_2308_; uint8_t v_isComplete_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2315_; 
v_response_2308_ = lean_ctor_get(v_fst_2303_, 0);
lean_inc(v_response_2308_);
v_isComplete_2309_ = lean_ctor_get_uint8(v_fst_2303_, sizeof(void*)*1);
lean_dec(v_fst_2303_);
v___x_2310_ = l_Lean_Array_toJson___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__6(v_response_2308_);
lean_inc(v___x_2310_);
v___x_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2310_);
v___x_2312_ = l_Lean_Json_compress(v___x_2310_);
v___x_2313_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
lean_ctor_set_uint8(v___x_2313_, sizeof(void*)*2, v_isComplete_2309_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v_inst_2288_);
v___x_2315_ = v___x_2306_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_inst_2288_);
lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_snd_2304_);
v___x_2315_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
lean_object* v___x_2316_; lean_object* v___x_2318_; 
v___x_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2313_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2316_);
v___x_2318_ = v___x_2301_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
else
{
lean_object* v_a_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2330_; 
lean_dec(v_inst_2288_);
v_a_2323_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2325_ = v___x_2298_;
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_a_2323_);
lean_dec(v___x_2298_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2330_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2328_; 
if (v_isShared_2326_ == 0)
{
v___x_2328_ = v___x_2325_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v_a_2323_);
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
lean_dec(v_a_2295_);
lean_dec_ref(v_handler_2289_);
lean_dec(v_inst_2288_);
v_a_2331_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2296_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2296_);
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
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec_ref(v_handler_2289_);
lean_dec(v_inst_2288_);
v_a_2339_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2294_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2294_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed(lean_object* v_method_2347_, lean_object* v_inst_2348_, lean_object* v_handler_2349_, lean_object* v_param_2350_, lean_object* v_state_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1(v_method_2347_, v_inst_2348_, v_handler_2349_, v_param_2350_, v_state_2351_, v___y_2352_);
lean_dec_ref(v___y_2352_);
lean_dec(v_state_2351_);
lean_dec_ref(v_method_2347_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(lean_object* v___f_2355_, lean_object* v___f_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2360_ = lean_st_ref_get(v___y_2357_);
v___x_2361_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_2360_, v___f_2355_, v___y_2358_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2371_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2371_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2371_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2369_; 
lean_inc(v_a_2362_);
v___x_2366_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2356_, v_a_2362_);
v___x_2367_ = lean_st_ref_swap(v___y_2357_, v___x_2366_);
lean_dec(v___x_2367_);
if (v_isShared_2365_ == 0)
{
v___x_2369_ = v___x_2364_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2362_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
else
{
lean_dec_ref(v___f_2356_);
return v___x_2361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed(lean_object* v___f_2372_, lean_object* v___f_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6(v___f_2372_, v___f_2373_, v___y_2374_, v___y_2375_);
lean_dec_ref(v___y_2375_);
lean_dec(v___y_2374_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(lean_object* v_val_2378_, lean_object* v___f_2379_, lean_object* v_param_2380_, lean_object* v_x_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = lean_st_ref_get(v_val_2378_);
lean_inc_ref(v___y_2382_);
v___x_2385_ = lean_apply_4(v___f_2379_, v_param_2380_, v___x_2384_, v___y_2382_, lean_box(0));
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v_a_2386_; lean_object* v___x_2388_; uint8_t v_isShared_2389_; uint8_t v_isSharedCheck_2396_; 
v_a_2386_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2388_ = v___x_2385_;
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
else
{
lean_inc(v_a_2386_);
lean_dec(v___x_2385_);
v___x_2388_ = lean_box(0);
v_isShared_2389_ = v_isSharedCheck_2396_;
goto v_resetjp_2387_;
}
v_resetjp_2387_:
{
lean_object* v_fst_2390_; lean_object* v_snd_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
v_fst_2390_ = lean_ctor_get(v_a_2386_, 0);
lean_inc(v_fst_2390_);
v_snd_2391_ = lean_ctor_get(v_a_2386_, 1);
lean_inc(v_snd_2391_);
lean_dec(v_a_2386_);
v___x_2392_ = lean_st_ref_swap(v_val_2378_, v_snd_2391_);
lean_dec(v___x_2392_);
if (v_isShared_2389_ == 0)
{
lean_ctor_set(v___x_2388_, 0, v_fst_2390_);
v___x_2394_ = v___x_2388_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_fst_2390_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2404_; 
v_a_2397_ = lean_ctor_get(v___x_2385_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2385_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2399_ = v___x_2385_;
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2385_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2404_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v___x_2402_; 
if (v_isShared_2400_ == 0)
{
v___x_2402_ = v___x_2399_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_a_2397_);
v___x_2402_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
return v___x_2402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed(lean_object* v_val_2405_, lean_object* v___f_2406_, lean_object* v_param_2407_, lean_object* v_x_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5(v_val_2405_, v___f_2406_, v_param_2407_, v_x_2408_, v___y_2409_);
lean_dec_ref(v___y_2409_);
lean_dec(v_val_2405_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(lean_object* v_val_2412_, lean_object* v___f_2413_, lean_object* v___f_2414_, lean_object* v_val_2415_, lean_object* v_param_2416_, lean_object* v___y_2417_){
_start:
{
lean_object* v___f_2419_; lean_object* v___f_2420_; lean_object* v___x_2421_; 
v___f_2419_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__5___boxed), 6, 3);
lean_closure_set(v___f_2419_, 0, v_val_2412_);
lean_closure_set(v___f_2419_, 1, v___f_2413_);
lean_closure_set(v___f_2419_, 2, v_param_2416_);
v___f_2420_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__6___boxed), 5, 2);
lean_closure_set(v___f_2420_, 0, v___f_2419_);
lean_closure_set(v___f_2420_, 1, v___f_2414_);
v___x_2421_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_2415_, v___f_2420_, v___y_2417_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed(lean_object* v_val_2422_, lean_object* v___f_2423_, lean_object* v___f_2424_, lean_object* v_val_2425_, lean_object* v_param_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7(v_val_2422_, v___f_2423_, v___f_2424_, v_val_2425_, v_param_2426_, v___y_2427_);
lean_dec_ref(v___y_2427_);
return v_res_2429_;
}
}
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_box(0);
v___x_2438_ = lean_task_pure(v___x_2437_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_method_2439_, lean_object* v_completeness_2440_, lean_object* v_inst_2441_, lean_object* v_initState_2442_, lean_object* v_handler_2443_, lean_object* v_onDidChange_2444_){
_start:
{
lean_object* v___f_2446_; lean_object* v___f_2447_; lean_object* v___f_2448_; uint8_t v___x_2449_; 
v___f_2446_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0));
lean_inc_n(v_inst_2441_, 2);
lean_inc_ref_n(v_method_2439_, 2);
v___f_2447_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_2447_, 0, v_method_2439_);
lean_closure_set(v___f_2447_, 1, v_inst_2441_);
lean_closure_set(v___f_2447_, 2, v_handler_2443_);
v___f_2448_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_2448_, 0, v_method_2439_);
lean_closure_set(v___f_2448_, 1, v_inst_2441_);
lean_closure_set(v___f_2448_, 2, v_onDidChange_2444_);
v___x_2449_ = l_Lean_initializing();
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
lean_dec_ref(v___f_2448_);
lean_dec_ref(v___f_2447_);
lean_dec(v_initState_2442_);
lean_dec(v_inst_2441_);
lean_dec(v_completeness_2440_);
v___x_2450_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2451_ = lean_string_append(v___x_2450_, v_method_2439_);
lean_dec_ref(v_method_2439_);
v___x_2452_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2));
v___x_2453_ = lean_string_append(v___x_2451_, v___x_2452_);
v___x_2454_ = lean_mk_io_user_error(v___x_2453_);
v___x_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2455_, 0, v___x_2454_);
return v___x_2455_;
}
else
{
lean_object* v___x_2456_; lean_object* v___f_2457_; lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___f_2463_; lean_object* v___f_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2456_ = lean_box(0);
v___f_2457_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3));
v___f_2458_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4));
v___x_2459_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5);
v___x_2460_ = l_Std_Mutex_new___redArg(v___x_2459_);
v___x_2461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2461_, 0, v_inst_2441_);
lean_ctor_set(v___x_2461_, 1, v_initState_2442_);
lean_inc_ref(v___x_2461_);
v___x_2462_ = lean_st_mk_ref(v___x_2461_);
lean_inc_ref_n(v___x_2460_, 2);
lean_inc_ref(v___f_2447_);
lean_inc_n(v___x_2462_, 2);
v___f_2463_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2463_, 0, v___x_2462_);
lean_closure_set(v___f_2463_, 1, v___f_2447_);
lean_closure_set(v___f_2463_, 2, v___f_2457_);
lean_closure_set(v___f_2463_, 3, v___x_2460_);
lean_inc_ref(v___f_2448_);
v___f_2464_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed), 8, 5);
lean_closure_set(v___f_2464_, 0, v___x_2462_);
lean_closure_set(v___f_2464_, 1, v___f_2448_);
lean_closure_set(v___f_2464_, 2, v___x_2456_);
lean_closure_set(v___f_2464_, 3, v___f_2458_);
lean_closure_set(v___f_2464_, 4, v___x_2460_);
v___x_2465_ = l_Lean_Server_statefulRequestHandlers;
v___x_2466_ = lean_st_ref_take(v___x_2465_);
v___x_2467_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2467_, 0, v___f_2446_);
lean_ctor_set(v___x_2467_, 1, v___f_2447_);
lean_ctor_set(v___x_2467_, 2, v___f_2463_);
lean_ctor_set(v___x_2467_, 3, v___f_2448_);
lean_ctor_set(v___x_2467_, 4, v___f_2464_);
lean_ctor_set(v___x_2467_, 5, v___x_2460_);
lean_ctor_set(v___x_2467_, 6, v___x_2461_);
lean_ctor_set(v___x_2467_, 7, v___x_2462_);
lean_ctor_set(v___x_2467_, 8, v_completeness_2440_);
v___x_2468_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v___x_2466_, v_method_2439_, v___x_2467_);
v___x_2469_ = lean_st_ref_put(v___x_2465_, v___x_2468_);
v___x_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2470_, 0, v___x_2469_);
return v___x_2470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_method_2471_, lean_object* v_completeness_2472_, lean_object* v_inst_2473_, lean_object* v_initState_2474_, lean_object* v_handler_2475_, lean_object* v_onDidChange_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2471_, v_completeness_2472_, v_inst_2473_, v_initState_2474_, v_handler_2475_, v_onDidChange_2476_);
return v_res_2478_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_2479_, lean_object* v_i_2480_, lean_object* v_k_2481_){
_start:
{
lean_object* v___x_2482_; uint8_t v___x_2483_; 
v___x_2482_ = lean_array_get_size(v_keys_2479_);
v___x_2483_ = lean_nat_dec_lt(v_i_2480_, v___x_2482_);
if (v___x_2483_ == 0)
{
lean_dec(v_i_2480_);
return v___x_2483_;
}
else
{
lean_object* v_k_x27_2484_; uint8_t v___x_2485_; 
v_k_x27_2484_ = lean_array_fget_borrowed(v_keys_2479_, v_i_2480_);
v___x_2485_ = lean_string_dec_eq(v_k_2481_, v_k_x27_2484_);
if (v___x_2485_ == 0)
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = lean_unsigned_to_nat(1u);
v___x_2487_ = lean_nat_add(v_i_2480_, v___x_2486_);
lean_dec(v_i_2480_);
v_i_2480_ = v___x_2487_;
goto _start;
}
else
{
lean_dec(v_i_2480_);
return v___x_2483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_2489_, lean_object* v_i_2490_, lean_object* v_k_2491_){
_start:
{
uint8_t v_res_2492_; lean_object* v_r_2493_; 
v_res_2492_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2489_, v_i_2490_, v_k_2491_);
lean_dec_ref(v_k_2491_);
lean_dec_ref(v_keys_2489_);
v_r_2493_ = lean_box(v_res_2492_);
return v_r_2493_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2494_, size_t v_x_2495_, lean_object* v_x_2496_){
_start:
{
if (lean_obj_tag(v_x_2494_) == 0)
{
lean_object* v_es_2497_; lean_object* v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; lean_object* v_j_2501_; lean_object* v___x_2502_; 
v_es_2497_ = lean_ctor_get(v_x_2494_, 0);
v___x_2498_ = lean_box(2);
v___x_2499_ = ((size_t)31ULL);
v___x_2500_ = lean_usize_land(v_x_2495_, v___x_2499_);
v_j_2501_ = lean_usize_to_nat(v___x_2500_);
v___x_2502_ = lean_array_get_borrowed(v___x_2498_, v_es_2497_, v_j_2501_);
lean_dec(v_j_2501_);
switch(lean_obj_tag(v___x_2502_))
{
case 0:
{
lean_object* v_key_2503_; uint8_t v___x_2504_; 
v_key_2503_ = lean_ctor_get(v___x_2502_, 0);
v___x_2504_ = lean_string_dec_eq(v_x_2496_, v_key_2503_);
return v___x_2504_;
}
case 1:
{
lean_object* v_node_2505_; size_t v___x_2506_; size_t v___x_2507_; 
v_node_2505_ = lean_ctor_get(v___x_2502_, 0);
v___x_2506_ = ((size_t)5ULL);
v___x_2507_ = lean_usize_shift_right(v_x_2495_, v___x_2506_);
v_x_2494_ = v_node_2505_;
v_x_2495_ = v___x_2507_;
goto _start;
}
default: 
{
uint8_t v___x_2509_; 
v___x_2509_ = 0;
return v___x_2509_;
}
}
}
else
{
lean_object* v_ks_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; 
v_ks_2510_ = lean_ctor_get(v_x_2494_, 0);
v___x_2511_ = lean_unsigned_to_nat(0u);
v___x_2512_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_2510_, v___x_2511_, v_x_2496_);
return v___x_2512_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_2513_, lean_object* v_x_2514_, lean_object* v_x_2515_){
_start:
{
size_t v_x_3447__boxed_2516_; uint8_t v_res_2517_; lean_object* v_r_2518_; 
v_x_3447__boxed_2516_ = lean_unbox_usize(v_x_2514_);
lean_dec(v_x_2514_);
v_res_2517_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2513_, v_x_3447__boxed_2516_, v_x_2515_);
lean_dec_ref(v_x_2515_);
lean_dec_ref(v_x_2513_);
v_r_2518_ = lean_box(v_res_2517_);
return v_r_2518_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_2519_, lean_object* v_x_2520_){
_start:
{
uint64_t v___x_2521_; size_t v___x_2522_; uint8_t v___x_2523_; 
v___x_2521_ = lean_string_hash(v_x_2520_);
v___x_2522_ = lean_uint64_to_usize(v___x_2521_);
v___x_2523_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2519_, v___x_2522_, v_x_2520_);
return v___x_2523_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2524_, lean_object* v_x_2525_){
_start:
{
uint8_t v_res_2526_; lean_object* v_r_2527_; 
v_res_2526_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2524_, v_x_2525_);
lean_dec_ref(v_x_2525_);
lean_dec_ref(v_x_2524_);
v_r_2527_ = lean_box(v_res_2526_);
return v_r_2527_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_method_2529_, lean_object* v_completeness_2530_, lean_object* v_inst_2531_, lean_object* v_initState_2532_, lean_object* v_handler_2533_, lean_object* v_onDidChange_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; 
v___x_2536_ = l_Lean_Server_requestHandlers;
v___x_2537_ = lean_st_ref_get(v___x_2536_);
v___x_2538_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_2537_, v_method_2529_);
lean_dec(v___x_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; 
v___x_2539_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2529_, v_completeness_2530_, v_inst_2531_, v_initState_2532_, v_handler_2533_, v_onDidChange_2534_);
return v___x_2539_;
}
else
{
lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_dec_ref(v_onDidChange_2534_);
lean_dec_ref(v_handler_2533_);
lean_dec(v_initState_2532_);
lean_dec(v_inst_2531_);
lean_dec(v_completeness_2530_);
v___x_2540_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
v___x_2541_ = lean_string_append(v___x_2540_, v_method_2529_);
lean_dec_ref(v_method_2529_);
v___x_2542_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_2543_ = lean_string_append(v___x_2541_, v___x_2542_);
v___x_2544_ = lean_mk_io_user_error(v___x_2543_);
v___x_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
return v___x_2545_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_method_2546_, lean_object* v_completeness_2547_, lean_object* v_inst_2548_, lean_object* v_initState_2549_, lean_object* v_handler_2550_, lean_object* v_onDidChange_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2546_, v_completeness_2547_, v_inst_2548_, v_initState_2549_, v_handler_2550_, v_onDidChange_2551_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(lean_object* v_method_2554_, lean_object* v_refreshMethod_2555_, lean_object* v_refreshIntervalMs_2556_, lean_object* v_inst_2557_, lean_object* v_initState_2558_, lean_object* v_handler_2559_, lean_object* v_onDidChange_2560_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2562_, 0, v_refreshMethod_2555_);
lean_ctor_set(v___x_2562_, 1, v_refreshIntervalMs_2556_);
v___x_2563_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2554_, v___x_2562_, v_inst_2557_, v_initState_2558_, v_handler_2559_, v_onDidChange_2560_);
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_method_2564_, lean_object* v_refreshMethod_2565_, lean_object* v_refreshIntervalMs_2566_, lean_object* v_inst_2567_, lean_object* v_initState_2568_, lean_object* v_handler_2569_, lean_object* v_onDidChange_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2564_, v_refreshMethod_2565_, v_refreshIntervalMs_2566_, v_inst_2567_, v_initState_2568_, v_handler_2569_, v_onDidChange_2570_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2578_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_));
v___x_2579_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2580_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2581_ = lean_unsigned_to_nat(500u);
v___x_2582_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init));
v___x_2583_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2584_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2585_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v___x_2579_, v___x_2580_, v___x_2581_, v___x_2578_, v___x_2582_, v___x_2583_, v___x_2584_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2____boxed(lean_object* v_a_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(lean_object* v_method_2588_, lean_object* v_refreshMethod_2589_, lean_object* v_refreshIntervalMs_2590_, lean_object* v_stateType_2591_, lean_object* v_inst_2592_, lean_object* v_initState_2593_, lean_object* v_handler_2594_, lean_object* v_onDidChange_2595_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2588_, v_refreshMethod_2589_, v_refreshIntervalMs_2590_, v_inst_2592_, v_initState_2593_, v_handler_2594_, v_onDidChange_2595_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2598_, lean_object* v_refreshMethod_2599_, lean_object* v_refreshIntervalMs_2600_, lean_object* v_stateType_2601_, lean_object* v_inst_2602_, lean_object* v_initState_2603_, lean_object* v_handler_2604_, lean_object* v_onDidChange_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v_res_2607_; 
v_res_2607_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(v_method_2598_, v_refreshMethod_2599_, v_refreshIntervalMs_2600_, v_stateType_2601_, v_inst_2602_, v_initState_2603_, v_handler_2604_, v_onDidChange_2605_);
return v_res_2607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_2608_, lean_object* v_completeness_2609_, lean_object* v_stateType_2610_, lean_object* v_inst_2611_, lean_object* v_initState_2612_, lean_object* v_handler_2613_, lean_object* v_onDidChange_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2608_, v_completeness_2609_, v_inst_2611_, v_initState_2612_, v_handler_2613_, v_onDidChange_2614_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_method_2617_, lean_object* v_completeness_2618_, lean_object* v_stateType_2619_, lean_object* v_inst_2620_, lean_object* v_initState_2621_, lean_object* v_handler_2622_, lean_object* v_onDidChange_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(v_method_2617_, v_completeness_2618_, v_stateType_2619_, v_inst_2620_, v_initState_2621_, v_handler_2622_, v_onDidChange_2623_);
return v_res_2625_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2626_, lean_object* v_x_2627_, lean_object* v_x_2628_){
_start:
{
uint8_t v___x_2629_; 
v___x_2629_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2627_, v_x_2628_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_){
_start:
{
uint8_t v_res_2633_; lean_object* v_r_2634_; 
v_res_2633_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2630_, v_x_2631_, v_x_2632_);
lean_dec_ref(v_x_2632_);
lean_dec_ref(v_x_2631_);
v_r_2634_ = lean_box(v_res_2633_);
return v_r_2634_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b1_2635_, lean_object* v_00_u03b2_2636_, lean_object* v_mutex_2637_, lean_object* v_k_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v___x_2641_; 
v___x_2641_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2637_, v_k_2638_, v___y_2639_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2642_, lean_object* v_00_u03b2_2643_, lean_object* v_mutex_2644_, lean_object* v_k_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(v_00_u03b1_2642_, v_00_u03b2_2643_, v_mutex_2644_, v_k_2645_, v___y_2646_);
lean_dec_ref(v___y_2646_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_method_2649_, lean_object* v_completeness_2650_, lean_object* v_stateType_2651_, lean_object* v_inst_2652_, lean_object* v_initState_2653_, lean_object* v_handler_2654_, lean_object* v_onDidChange_2655_){
_start:
{
lean_object* v___x_2657_; 
v___x_2657_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2649_, v_completeness_2650_, v_inst_2652_, v_initState_2653_, v_handler_2654_, v_onDidChange_2655_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_method_2658_, lean_object* v_completeness_2659_, lean_object* v_stateType_2660_, lean_object* v_inst_2661_, lean_object* v_initState_2662_, lean_object* v_handler_2663_, lean_object* v_onDidChange_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_method_2658_, v_completeness_2659_, v_stateType_2660_, v_inst_2661_, v_initState_2662_, v_handler_2663_, v_onDidChange_2664_);
return v_res_2666_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2667_, lean_object* v_x_2668_, size_t v_x_2669_, lean_object* v_x_2670_){
_start:
{
uint8_t v___x_2671_; 
v___x_2671_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2668_, v_x_2669_, v_x_2670_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2672_, lean_object* v_x_2673_, lean_object* v_x_2674_, lean_object* v_x_2675_){
_start:
{
size_t v_x_3611__boxed_2676_; uint8_t v_res_2677_; lean_object* v_r_2678_; 
v_x_3611__boxed_2676_ = lean_unbox_usize(v_x_2674_);
lean_dec(v_x_2674_);
v_res_2677_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2672_, v_x_2673_, v_x_3611__boxed_2676_, v_x_2675_);
lean_dec_ref(v_x_2675_);
lean_dec_ref(v_x_2673_);
v_r_2678_ = lean_box(v_res_2677_);
return v_r_2678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_params_2679_, lean_object* v_a_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2679_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_params_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_params_2683_, v_a_2684_);
lean_dec_ref(v_a_2684_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_2687_, lean_object* v_x_2688_, lean_object* v_x_2689_, lean_object* v_x_2690_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v_x_2688_, v_x_2689_, v_x_2690_);
return v___x_2691_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2692_, lean_object* v_keys_2693_, lean_object* v_vals_2694_, lean_object* v_heq_2695_, lean_object* v_i_2696_, lean_object* v_k_2697_){
_start:
{
uint8_t v___x_2698_; 
v___x_2698_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2693_, v_i_2696_, v_k_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2699_, lean_object* v_keys_2700_, lean_object* v_vals_2701_, lean_object* v_heq_2702_, lean_object* v_i_2703_, lean_object* v_k_2704_){
_start:
{
uint8_t v_res_2705_; lean_object* v_r_2706_; 
v_res_2705_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_2699_, v_keys_2700_, v_vals_2701_, v_heq_2702_, v_i_2703_, v_k_2704_);
lean_dec_ref(v_k_2704_);
lean_dec_ref(v_vals_2701_);
lean_dec_ref(v_keys_2700_);
v_r_2706_ = lean_box(v_res_2705_);
return v_r_2706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_2707_, lean_object* v_x_2708_, size_t v_x_2709_, size_t v_x_2710_, lean_object* v_x_2711_, lean_object* v_x_2712_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_2708_, v_x_2709_, v_x_2710_, v_x_2711_, v_x_2712_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2714_, lean_object* v_x_2715_, lean_object* v_x_2716_, lean_object* v_x_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_){
_start:
{
size_t v_x_3637__boxed_2720_; size_t v_x_3638__boxed_2721_; lean_object* v_res_2722_; 
v_x_3637__boxed_2720_ = lean_unbox_usize(v_x_2716_);
lean_dec(v_x_2716_);
v_x_3638__boxed_2721_ = lean_unbox_usize(v_x_2717_);
lean_dec(v_x_2717_);
v_res_2722_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(v_00_u03b2_2714_, v_x_2715_, v_x_3637__boxed_2720_, v_x_3638__boxed_2721_, v_x_2718_, v_x_2719_);
return v_res_2722_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_2723_, lean_object* v_n_2724_, lean_object* v_k_2725_, lean_object* v_v_2726_){
_start:
{
lean_object* v___x_2727_; 
v___x_2727_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v_n_2724_, v_k_2725_, v_v_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(lean_object* v_00_u03b2_2728_, size_t v_depth_2729_, lean_object* v_keys_2730_, lean_object* v_vals_2731_, lean_object* v_heq_2732_, lean_object* v_i_2733_, lean_object* v_entries_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_2729_, v_keys_2730_, v_vals_2731_, v_i_2733_, v_entries_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___boxed(lean_object* v_00_u03b2_2736_, lean_object* v_depth_2737_, lean_object* v_keys_2738_, lean_object* v_vals_2739_, lean_object* v_heq_2740_, lean_object* v_i_2741_, lean_object* v_entries_2742_){
_start:
{
size_t v_depth_boxed_2743_; lean_object* v_res_2744_; 
v_depth_boxed_2743_ = lean_unbox_usize(v_depth_2737_);
lean_dec(v_depth_2737_);
v_res_2744_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(v_00_u03b2_2736_, v_depth_boxed_2743_, v_keys_2738_, v_vals_2739_, v_heq_2740_, v_i_2741_, v_entries_2742_);
lean_dec_ref(v_vals_2739_);
lean_dec_ref(v_keys_2738_);
return v_res_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_2745_, lean_object* v_x_2746_, lean_object* v_x_2747_, lean_object* v_x_2748_, lean_object* v_x_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_x_2746_, v_x_2747_, v_x_2748_, v_x_2749_);
return v___x_2750_;
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
