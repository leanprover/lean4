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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Elab_InlayHint_ofCustomInfo_x3f(lean_object*);
lean_object* l_Lean_Elab_InlayHint_resolveDeferred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestError_ofIoError(lean_object*);
uint8_t l_Lean_Elab_instBEqInlayHintTextEdit_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Server_requestHandlers;
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing();
lean_object* lean_task_pure(lean_object*);
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
extern lean_object* l_Lean_Server_statefulRequestHandlers;
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Server_RequestM_mapTaskCostly___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* lean_mk_io_user_error(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2_value;
static const lean_closure_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__4___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "Failed to register stateful LSP request handler for '"};
static const lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4 = (const lean_object*)&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4_value;
static const lean_string_object l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "': only possible during initialization"};
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(lean_object* v_hintMod_311_, lean_object* v_range_312_, lean_object* v_byteOffset_313_, size_t v_sz_314_, size_t v_i_315_, lean_object* v_bs_316_){
_start:
{
uint8_t v___x_317_; 
v___x_317_ = lean_usize_dec_lt(v_i_315_, v_sz_314_);
if (v___x_317_ == 0)
{
lean_dec_ref(v_range_312_);
return v_bs_316_;
}
else
{
lean_object* v_v_318_; lean_object* v_value_319_; lean_object* v_tooltip_x3f_320_; lean_object* v_location_x3f_321_; lean_object* v___x_323_; uint8_t v_isShared_324_; uint8_t v_isSharedCheck_364_; 
v_v_318_ = lean_array_uget(v_bs_316_, v_i_315_);
v_value_319_ = lean_ctor_get(v_v_318_, 0);
v_tooltip_x3f_320_ = lean_ctor_get(v_v_318_, 1);
v_location_x3f_321_ = lean_ctor_get(v_v_318_, 2);
v_isSharedCheck_364_ = !lean_is_exclusive(v_v_318_);
if (v_isSharedCheck_364_ == 0)
{
v___x_323_ = v_v_318_;
v_isShared_324_ = v_isSharedCheck_364_;
goto v_resetjp_322_;
}
else
{
lean_inc(v_location_x3f_321_);
lean_inc(v_tooltip_x3f_320_);
lean_inc(v_value_319_);
lean_dec(v_v_318_);
v___x_323_ = lean_box(0);
v_isShared_324_ = v_isSharedCheck_364_;
goto v_resetjp_322_;
}
v_resetjp_322_:
{
lean_object* v___x_325_; lean_object* v_bs_x27_326_; lean_object* v___y_328_; lean_object* v___y_334_; 
v___x_325_ = lean_unsigned_to_nat(0u);
v_bs_x27_326_ = lean_array_uset(v_bs_316_, v_i_315_, v___x_325_);
if (lean_obj_tag(v_location_x3f_321_) == 0)
{
lean_object* v___x_339_; 
lean_del_object(v___x_323_);
v___x_339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_339_, 0, v_value_319_);
lean_ctor_set(v___x_339_, 1, v_tooltip_x3f_320_);
lean_ctor_set(v___x_339_, 2, v_location_x3f_321_);
v___y_328_ = v___x_339_;
goto v___jp_327_;
}
else
{
lean_object* v_val_340_; lean_object* v_module_341_; lean_object* v_range_342_; uint8_t v___x_343_; 
v_val_340_ = lean_ctor_get(v_location_x3f_321_, 0);
lean_inc(v_val_340_);
lean_dec_ref_known(v_location_x3f_321_, 1);
v_module_341_ = lean_ctor_get(v_val_340_, 0);
v_range_342_ = lean_ctor_get(v_val_340_, 1);
lean_inc_ref(v_range_342_);
v___x_343_ = lean_name_eq(v_module_341_, v_hintMod_311_);
if (v___x_343_ == 0)
{
lean_dec_ref(v_range_342_);
v___y_334_ = v_val_340_;
goto v___jp_333_;
}
else
{
lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_361_; 
lean_inc(v_module_341_);
v_isSharedCheck_361_ = !lean_is_exclusive(v_val_340_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; lean_object* v_unused_363_; 
v_unused_362_ = lean_ctor_get(v_val_340_, 1);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_val_340_, 0);
lean_dec(v_unused_363_);
v___x_345_ = v_val_340_;
v_isShared_346_ = v_isSharedCheck_361_;
goto v_resetjp_344_;
}
else
{
lean_dec(v_val_340_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_361_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v_start_347_; lean_object* v_stop_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_360_; 
v_start_347_ = lean_ctor_get(v_range_342_, 0);
v_stop_348_ = lean_ctor_get(v_range_342_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v_range_342_);
if (v_isSharedCheck_360_ == 0)
{
v___x_350_ = v_range_342_;
v_isShared_351_ = v_isSharedCheck_360_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_stop_348_);
lean_inc(v_start_347_);
lean_dec(v_range_342_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_360_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_355_; 
lean_inc_ref_n(v_range_312_, 2);
v___x_352_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_312_, v_byteOffset_313_, v_start_347_);
v___x_353_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_312_, v_byteOffset_313_, v_stop_348_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 1, v___x_353_);
lean_ctor_set(v___x_350_, 0, v___x_352_);
v___x_355_ = v___x_350_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_352_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_353_);
v___x_355_ = v_reuseFailAlloc_359_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
lean_object* v___x_357_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 1, v___x_355_);
v___x_357_ = v___x_345_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_module_341_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v___x_355_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
v___y_334_ = v___x_357_;
goto v___jp_333_;
}
}
}
}
}
}
v___jp_327_:
{
size_t v___x_329_; size_t v___x_330_; lean_object* v___x_331_; 
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_315_, v___x_329_);
v___x_331_ = lean_array_uset(v_bs_x27_326_, v_i_315_, v___y_328_);
v_i_315_ = v___x_330_;
v_bs_316_ = v___x_331_;
goto _start;
}
v___jp_333_:
{
lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_335_, 0, v___y_334_);
if (v_isShared_324_ == 0)
{
lean_ctor_set(v___x_323_, 2, v___x_335_);
v___x_337_ = v___x_323_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_value_319_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v_tooltip_x3f_320_);
lean_ctor_set(v_reuseFailAlloc_338_, 2, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
v___y_328_ = v___x_337_;
goto v___jp_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4___boxed(lean_object* v_hintMod_365_, lean_object* v_range_366_, lean_object* v_byteOffset_367_, lean_object* v_sz_368_, lean_object* v_i_369_, lean_object* v_bs_370_){
_start:
{
size_t v_sz_boxed_371_; size_t v_i_boxed_372_; lean_object* v_res_373_; 
v_sz_boxed_371_ = lean_unbox_usize(v_sz_368_);
lean_dec(v_sz_368_);
v_i_boxed_372_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_365_, v_range_366_, v_byteOffset_367_, v_sz_boxed_371_, v_i_boxed_372_, v_bs_370_);
lean_dec(v_byteOffset_367_);
lean_dec(v_hintMod_365_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(lean_object* v_hintMod_374_, lean_object* v_range_375_, lean_object* v_byteOffset_376_, size_t v_sz_377_, size_t v_i_378_, lean_object* v_bs_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = lean_usize_dec_lt(v_i_378_, v_sz_377_);
if (v___x_380_ == 0)
{
lean_dec_ref(v_range_375_);
return v_bs_379_;
}
else
{
lean_object* v_v_381_; lean_object* v_value_382_; lean_object* v_tooltip_x3f_383_; lean_object* v_location_x3f_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_427_; 
v_v_381_ = lean_array_uget(v_bs_379_, v_i_378_);
v_value_382_ = lean_ctor_get(v_v_381_, 0);
v_tooltip_x3f_383_ = lean_ctor_get(v_v_381_, 1);
v_location_x3f_384_ = lean_ctor_get(v_v_381_, 2);
v_isSharedCheck_427_ = !lean_is_exclusive(v_v_381_);
if (v_isSharedCheck_427_ == 0)
{
v___x_386_ = v_v_381_;
v_isShared_387_ = v_isSharedCheck_427_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_location_x3f_384_);
lean_inc(v_tooltip_x3f_383_);
lean_inc(v_value_382_);
lean_dec(v_v_381_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_427_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v_bs_x27_389_; lean_object* v___y_391_; lean_object* v___y_397_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v_bs_x27_389_ = lean_array_uset(v_bs_379_, v_i_378_, v___x_388_);
if (lean_obj_tag(v_location_x3f_384_) == 0)
{
lean_object* v___x_402_; 
lean_del_object(v___x_386_);
v___x_402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_402_, 0, v_value_382_);
lean_ctor_set(v___x_402_, 1, v_tooltip_x3f_383_);
lean_ctor_set(v___x_402_, 2, v_location_x3f_384_);
v___y_391_ = v___x_402_;
goto v___jp_390_;
}
else
{
lean_object* v_val_403_; lean_object* v_module_404_; lean_object* v_range_405_; uint8_t v___x_406_; 
v_val_403_ = lean_ctor_get(v_location_x3f_384_, 0);
lean_inc(v_val_403_);
lean_dec_ref_known(v_location_x3f_384_, 1);
v_module_404_ = lean_ctor_get(v_val_403_, 0);
v_range_405_ = lean_ctor_get(v_val_403_, 1);
lean_inc_ref(v_range_405_);
v___x_406_ = lean_name_eq(v_module_404_, v_hintMod_374_);
if (v___x_406_ == 0)
{
lean_dec_ref(v_range_405_);
v___y_397_ = v_val_403_;
goto v___jp_396_;
}
else
{
lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_424_; 
lean_inc(v_module_404_);
v_isSharedCheck_424_ = !lean_is_exclusive(v_val_403_);
if (v_isSharedCheck_424_ == 0)
{
lean_object* v_unused_425_; lean_object* v_unused_426_; 
v_unused_425_ = lean_ctor_get(v_val_403_, 1);
lean_dec(v_unused_425_);
v_unused_426_ = lean_ctor_get(v_val_403_, 0);
lean_dec(v_unused_426_);
v___x_408_ = v_val_403_;
v_isShared_409_ = v_isSharedCheck_424_;
goto v_resetjp_407_;
}
else
{
lean_dec(v_val_403_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_424_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v_start_410_; lean_object* v_stop_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_423_; 
v_start_410_ = lean_ctor_get(v_range_405_, 0);
v_stop_411_ = lean_ctor_get(v_range_405_, 1);
v_isSharedCheck_423_ = !lean_is_exclusive(v_range_405_);
if (v_isSharedCheck_423_ == 0)
{
v___x_413_ = v_range_405_;
v_isShared_414_ = v_isSharedCheck_423_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_stop_411_);
lean_inc(v_start_410_);
lean_dec(v_range_405_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_423_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
lean_inc_ref_n(v_range_375_, 2);
v___x_415_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_375_, v_byteOffset_376_, v_start_410_);
v___x_416_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_375_, v_byteOffset_376_, v_stop_411_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_416_);
lean_ctor_set(v___x_413_, 0, v___x_415_);
v___x_418_ = v___x_413_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v___x_416_);
v___x_418_ = v_reuseFailAlloc_422_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_420_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 1, v___x_418_);
v___x_420_ = v___x_408_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_module_404_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v___x_418_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
v___y_397_ = v___x_420_;
goto v___jp_396_;
}
}
}
}
}
}
v___jp_390_:
{
size_t v___x_392_; size_t v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = ((size_t)1ULL);
v___x_393_ = lean_usize_add(v_i_378_, v___x_392_);
v___x_394_ = lean_array_uset(v_bs_x27_389_, v_i_378_, v___y_391_);
v___x_395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3_spec__4(v_hintMod_374_, v_range_375_, v_byteOffset_376_, v_sz_377_, v___x_393_, v___x_394_);
return v___x_395_;
}
v___jp_396_:
{
lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___y_397_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 2, v___x_398_);
v___x_400_ = v___x_386_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_value_382_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_tooltip_x3f_383_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v___x_398_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
v___y_391_ = v___x_400_;
goto v___jp_390_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3___boxed(lean_object* v_hintMod_428_, lean_object* v_range_429_, lean_object* v_byteOffset_430_, lean_object* v_sz_431_, lean_object* v_i_432_, lean_object* v_bs_433_){
_start:
{
size_t v_sz_boxed_434_; size_t v_i_boxed_435_; lean_object* v_res_436_; 
v_sz_boxed_434_ = lean_unbox_usize(v_sz_431_);
lean_dec(v_sz_431_);
v_i_boxed_435_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_res_436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__3(v_hintMod_428_, v_range_429_, v_byteOffset_430_, v_sz_boxed_434_, v_i_boxed_435_, v_bs_433_);
lean_dec(v_byteOffset_430_);
lean_dec(v_hintMod_428_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(lean_object* v_range_437_, lean_object* v_byteOffset_438_, size_t v_sz_439_, size_t v_i_440_, lean_object* v_bs_441_){
_start:
{
uint8_t v___x_442_; 
v___x_442_ = lean_usize_dec_lt(v_i_440_, v_sz_439_);
if (v___x_442_ == 0)
{
lean_dec_ref(v_range_437_);
return v_bs_441_;
}
else
{
lean_object* v_v_443_; lean_object* v_range_444_; lean_object* v_newText_445_; lean_object* v___x_447_; uint8_t v_isShared_448_; uint8_t v_isSharedCheck_469_; 
v_v_443_ = lean_array_uget(v_bs_441_, v_i_440_);
v_range_444_ = lean_ctor_get(v_v_443_, 0);
v_newText_445_ = lean_ctor_get(v_v_443_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_v_443_);
if (v_isSharedCheck_469_ == 0)
{
v___x_447_ = v_v_443_;
v_isShared_448_ = v_isSharedCheck_469_;
goto v_resetjp_446_;
}
else
{
lean_inc(v_newText_445_);
lean_inc(v_range_444_);
lean_dec(v_v_443_);
v___x_447_ = lean_box(0);
v_isShared_448_ = v_isSharedCheck_469_;
goto v_resetjp_446_;
}
v_resetjp_446_:
{
lean_object* v_start_449_; lean_object* v_stop_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_468_; 
v_start_449_ = lean_ctor_get(v_range_444_, 0);
v_stop_450_ = lean_ctor_get(v_range_444_, 1);
v_isSharedCheck_468_ = !lean_is_exclusive(v_range_444_);
if (v_isSharedCheck_468_ == 0)
{
v___x_452_ = v_range_444_;
v_isShared_453_ = v_isSharedCheck_468_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_stop_450_);
lean_inc(v_start_449_);
lean_dec(v_range_444_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_468_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; lean_object* v_bs_x27_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
v___x_454_ = lean_unsigned_to_nat(0u);
v_bs_x27_455_ = lean_array_uset(v_bs_441_, v_i_440_, v___x_454_);
lean_inc_ref_n(v_range_437_, 2);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_437_, v_byteOffset_438_, v_start_449_);
v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_437_, v_byteOffset_438_, v_stop_450_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_457_);
lean_ctor_set(v___x_452_, 0, v___x_456_);
v___x_459_ = v___x_452_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_467_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_467_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
lean_object* v___x_461_; 
if (v_isShared_448_ == 0)
{
lean_ctor_set(v___x_447_, 0, v___x_459_);
v___x_461_ = v___x_447_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_466_; 
v_reuseFailAlloc_466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_466_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_466_, 1, v_newText_445_);
v___x_461_ = v_reuseFailAlloc_466_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
size_t v___x_462_; size_t v___x_463_; lean_object* v___x_464_; 
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_add(v_i_440_, v___x_462_);
v___x_464_ = lean_array_uset(v_bs_x27_455_, v_i_440_, v___x_461_);
v_i_440_ = v___x_463_;
v_bs_441_ = v___x_464_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2___boxed(lean_object* v_range_470_, lean_object* v_byteOffset_471_, lean_object* v_sz_472_, lean_object* v_i_473_, lean_object* v_bs_474_){
_start:
{
size_t v_sz_boxed_475_; size_t v_i_boxed_476_; lean_object* v_res_477_; 
v_sz_boxed_475_ = lean_unbox_usize(v_sz_472_);
lean_dec(v_sz_472_);
v_i_boxed_476_ = lean_unbox_usize(v_i_473_);
lean_dec(v_i_473_);
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_470_, v_byteOffset_471_, v_sz_boxed_475_, v_i_boxed_476_, v_bs_474_);
lean_dec(v_byteOffset_471_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(lean_object* v_range_478_, lean_object* v_byteOffset_479_, size_t v_sz_480_, size_t v_i_481_, lean_object* v_bs_482_){
_start:
{
uint8_t v___x_483_; 
v___x_483_ = lean_usize_dec_lt(v_i_481_, v_sz_480_);
if (v___x_483_ == 0)
{
lean_dec_ref(v_range_478_);
return v_bs_482_;
}
else
{
lean_object* v_v_484_; lean_object* v_range_485_; lean_object* v_newText_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_510_; 
v_v_484_ = lean_array_uget(v_bs_482_, v_i_481_);
v_range_485_ = lean_ctor_get(v_v_484_, 0);
v_newText_486_ = lean_ctor_get(v_v_484_, 1);
v_isSharedCheck_510_ = !lean_is_exclusive(v_v_484_);
if (v_isSharedCheck_510_ == 0)
{
v___x_488_ = v_v_484_;
v_isShared_489_ = v_isSharedCheck_510_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_newText_486_);
lean_inc(v_range_485_);
lean_dec(v_v_484_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_510_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v_start_490_; lean_object* v_stop_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_509_; 
v_start_490_ = lean_ctor_get(v_range_485_, 0);
v_stop_491_ = lean_ctor_get(v_range_485_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_range_485_);
if (v_isSharedCheck_509_ == 0)
{
v___x_493_ = v_range_485_;
v_isShared_494_ = v_isSharedCheck_509_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_stop_491_);
lean_inc(v_start_490_);
lean_dec(v_range_485_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_509_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v_bs_x27_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_495_ = lean_unsigned_to_nat(0u);
v_bs_x27_496_ = lean_array_uset(v_bs_482_, v_i_481_, v___x_495_);
lean_inc_ref_n(v_range_478_, 2);
v___x_497_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_478_, v_byteOffset_479_, v_start_490_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0(v_range_478_, v_byteOffset_479_, v_stop_491_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v___x_498_);
lean_ctor_set(v___x_493_, 0, v___x_497_);
v___x_500_ = v___x_493_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_497_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_498_);
v___x_500_ = v_reuseFailAlloc_508_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_502_; 
if (v_isShared_489_ == 0)
{
lean_ctor_set(v___x_488_, 0, v___x_500_);
v___x_502_ = v___x_488_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_500_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_newText_486_);
v___x_502_ = v_reuseFailAlloc_507_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_add(v_i_481_, v___x_503_);
v___x_505_ = lean_array_uset(v_bs_x27_496_, v_i_481_, v___x_502_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2_spec__2(v_range_478_, v_byteOffset_479_, v_sz_480_, v___x_504_, v___x_505_);
return v___x_506_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___boxed(lean_object* v_range_511_, lean_object* v_byteOffset_512_, lean_object* v_sz_513_, lean_object* v_i_514_, lean_object* v_bs_515_){
_start:
{
size_t v_sz_boxed_516_; size_t v_i_boxed_517_; lean_object* v_res_518_; 
v_sz_boxed_516_ = lean_unbox_usize(v_sz_513_);
lean_dec(v_sz_513_);
v_i_boxed_517_ = lean_unbox_usize(v_i_514_);
lean_dec(v_i_514_);
v_res_518_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_511_, v_byteOffset_512_, v_sz_boxed_516_, v_i_boxed_517_, v_bs_515_);
lean_dec(v_byteOffset_512_);
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
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2(v_range_574_, v___y_588_, v_sz_590_, v___x_591_, v_textEdits_579_);
lean_dec(v___y_588_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 3, v___x_592_);
lean_ctor_set(v___x_584_, 1, v___y_589_);
lean_ctor_set(v___x_584_, 0, v___y_587_);
v___x_594_ = v___x_584_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v___y_587_);
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
v___y_587_ = v___y_599_;
v___y_588_ = v___y_598_;
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
v___y_587_ = v___y_599_;
v___y_588_ = v___y_598_;
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
lean_object* v___x_702_; lean_object* v___f_703_; lean_object* v___x_17441__overap_704_; lean_object* v___x_705_; 
v___x_702_ = lean_obj_once(&l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0, &l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0_once, _init_l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0___closed__0);
v___f_703_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_703_, 0, v___x_702_);
v___x_17441__overap_704_ = lean_panic_fn_borrowed(v___f_703_, v_msg_699_);
lean_dec_ref(v___f_703_);
lean_inc_ref(v___y_700_);
v___x_705_ = lean_apply_2(v___x_17441__overap_704_, v___y_700_, lean_box(0));
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(uint8_t v___x_710_, lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v___y_714_, lean_object* v___y_715_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_box(v___x_710_);
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
lean_ctor_set(v___x_718_, 1, v___y_714_);
v___x_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed(lean_object* v___x_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
uint8_t v___x_20394__boxed_727_; lean_object* v_res_728_; 
v___x_20394__boxed_727_ = lean_unbox(v___x_720_);
v_res_728_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1(v___x_20394__boxed_727_, v_x_721_, v_x_722_, v_x_723_, v___y_724_, v___y_725_);
lean_dec_ref(v___y_725_);
lean_dec_ref(v_x_723_);
lean_dec_ref(v_x_722_);
lean_dec_ref(v_x_721_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(lean_object* v_ci_729_, lean_object* v_i_730_, lean_object* v_x_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
if (lean_obj_tag(v_i_730_) == 10)
{
lean_object* v_i_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_770_; 
v_i_735_ = lean_ctor_get(v_i_730_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v_i_730_);
if (v_isSharedCheck_770_ == 0)
{
v___x_737_ = v_i_730_;
v_isShared_738_ = v_isSharedCheck_770_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_i_735_);
lean_dec(v_i_730_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_770_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Elab_InlayHint_ofCustomInfo_x3f(v_i_735_);
lean_dec_ref(v_i_735_);
if (lean_obj_tag(v___x_739_) == 1)
{
lean_object* v_val_740_; lean_object* v_lctx_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
lean_del_object(v___x_737_);
v_val_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v___x_739_, 1);
v_lctx_741_ = lean_ctor_get(v_val_740_, 1);
lean_inc_ref(v_lctx_741_);
v___x_742_ = lean_alloc_closure((void*)(l_Lean_Elab_InlayHint_resolveDeferred___boxed), 6, 1);
lean_closure_set(v___x_742_, 0, v_val_740_);
v___x_743_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ci_729_, v_lctx_741_, v___x_742_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_755_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_755_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_755_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_toInlayHintInfo_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_753_; 
v_toInlayHintInfo_748_ = lean_ctor_get(v_a_744_, 0);
lean_inc_ref(v_toInlayHintInfo_748_);
lean_dec(v_a_744_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_array_push(v___y_732_, v_toInlayHintInfo_748_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_749_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_751_);
v___x_753_ = v___x_746_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
lean_dec_ref(v___y_732_);
v_a_756_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_764_ == 0)
{
v___x_758_ = v___x_743_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_743_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = l_Lean_Server_RequestError_ofIoError(v_a_756_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 0, v___x_760_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_768_; 
lean_dec(v___x_739_);
lean_dec_ref(v_ci_729_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v___y_732_);
if (v_isShared_738_ == 0)
{
lean_ctor_set_tag(v___x_737_, 0);
lean_ctor_set(v___x_737_, 0, v___x_766_);
v___x_768_ = v___x_737_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_766_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec_ref(v_i_730_);
lean_dec_ref(v_ci_729_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v___y_732_);
v___x_773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0___boxed(lean_object* v_ci_774_, lean_object* v_i_775_, lean_object* v_x_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__0(v_ci_774_, v_i_775_, v_x_776_, v___y_777_, v___y_778_);
lean_dec_ref(v___y_778_);
lean_dec_ref(v_x_776_);
return v_res_780_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = l_instMonadEIO(lean_box(0));
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(lean_object* v_msg_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___f_788_; lean_object* v___f_789_; lean_object* v___f_790_; lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_19813__overap_800_; lean_object* v___x_801_; 
v___x_786_ = lean_obj_once(&l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0, &l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0_once, _init_l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___closed__0);
v___x_787_ = l_ReaderT_instMonad___redArg(v___x_786_);
lean_inc_ref_n(v___x_787_, 6);
v___f_788_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_788_, 0, v___x_787_);
v___f_789_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_789_, 0, v___x_787_);
v___f_790_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_790_, 0, v___x_787_);
v___f_791_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_791_, 0, v___x_787_);
v___x_792_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_792_, 0, lean_box(0));
lean_closure_set(v___x_792_, 1, lean_box(0));
lean_closure_set(v___x_792_, 2, v___x_787_);
v___x_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_793_, 0, v___x_792_);
lean_ctor_set(v___x_793_, 1, v___f_788_);
v___x_794_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_794_, 0, lean_box(0));
lean_closure_set(v___x_794_, 1, lean_box(0));
lean_closure_set(v___x_794_, 2, v___x_787_);
v___x_795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_795_, 0, v___x_793_);
lean_ctor_set(v___x_795_, 1, v___x_794_);
lean_ctor_set(v___x_795_, 2, v___f_789_);
lean_ctor_set(v___x_795_, 3, v___f_790_);
lean_ctor_set(v___x_795_, 4, v___f_791_);
v___x_796_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_796_, 0, lean_box(0));
lean_closure_set(v___x_796_, 1, lean_box(0));
lean_closure_set(v___x_796_, 2, v___x_787_);
v___x_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_795_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_box(0);
v___x_799_ = l_instInhabitedOfMonad___redArg(v___x_797_, v___x_798_);
v___x_19813__overap_800_ = lean_panic_fn_borrowed(v___x_799_, v_msg_782_);
lean_dec(v___x_799_);
lean_inc_ref(v___y_784_);
v___x_801_ = lean_apply_3(v___x_19813__overap_800_, v___y_783_, v___y_784_, lean_box(0));
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg___boxed(lean_object* v_msg_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_802_, v___y_803_, v___y_804_);
lean_dec_ref(v___y_804_);
return v_res_806_;
}
}
static lean_object* _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_810_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__2));
v___x_811_ = lean_unsigned_to_nat(21u);
v___x_812_ = lean_unsigned_to_nat(65u);
v___x_813_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__1));
v___x_814_ = ((lean_object*)(l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__0));
v___x_815_ = l_mkPanicMessageWithDecl(v___x_814_, v___x_813_, v___x_812_, v___x_811_, v___x_810_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(lean_object* v_preNode_816_, lean_object* v_postNode_817_, lean_object* v_x_818_, lean_object* v_x_819_, lean_object* v___y_820_, lean_object* v___y_821_){
_start:
{
switch(lean_obj_tag(v_x_819_))
{
case 0:
{
lean_object* v_i_823_; lean_object* v_t_824_; lean_object* v___x_825_; 
v_i_823_ = lean_ctor_get(v_x_819_, 0);
lean_inc_ref(v_i_823_);
v_t_824_ = lean_ctor_get(v_x_819_, 1);
lean_inc_ref(v_t_824_);
lean_dec_ref_known(v_x_819_, 2);
v___x_825_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(v_i_823_, v_x_818_);
v_x_818_ = v___x_825_;
v_x_819_ = v_t_824_;
goto _start;
}
case 1:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec_ref_known(v_x_819_, 2);
lean_dec_ref(v_postNode_817_);
lean_dec_ref(v_preNode_816_);
v___x_827_ = lean_obj_once(&l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3, &l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3_once, _init_l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___closed__3);
v___x_828_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v___x_827_, v___y_820_, v___y_821_);
return v___x_828_;
}
else
{
lean_object* v_i_829_; lean_object* v_children_830_; lean_object* v_val_831_; lean_object* v___x_832_; 
v_i_829_ = lean_ctor_get(v_x_819_, 0);
lean_inc_ref_n(v_i_829_, 2);
v_children_830_ = lean_ctor_get(v_x_819_, 1);
lean_inc_ref_n(v_children_830_, 2);
lean_dec_ref_known(v_x_819_, 2);
v_val_831_ = lean_ctor_get(v_x_818_, 0);
lean_inc_n(v_val_831_, 2);
lean_inc_ref(v_preNode_816_);
lean_inc_ref(v___y_821_);
v___x_832_ = lean_apply_6(v_preNode_816_, v_val_831_, v_i_829_, v_children_830_, v___y_820_, v___y_821_, lean_box(0));
if (lean_obj_tag(v___x_832_) == 0)
{
lean_object* v_a_833_; lean_object* v_fst_834_; lean_object* v_snd_835_; uint8_t v___x_836_; uint8_t v___x_837_; 
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref_known(v___x_832_, 1);
v_fst_834_ = lean_ctor_get(v_a_833_, 0);
lean_inc(v_fst_834_);
v_snd_835_ = lean_ctor_get(v_a_833_, 1);
lean_inc(v_snd_835_);
lean_dec(v_a_833_);
v___x_836_ = lean_unbox(v_fst_834_);
lean_dec(v_fst_834_);
v___x_837_ = lean_bool_not(v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_838_ = l_Lean_Elab_Info_updateContext_x3f(v_x_818_, v_i_829_);
v___x_839_ = l_Lean_PersistentArray_toList___redArg(v_children_830_);
v___x_840_ = lean_box(0);
lean_inc_ref(v_postNode_817_);
v___x_841_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_816_, v_postNode_817_, v___x_838_, v___x_839_, v___x_840_, v_snd_835_, v___y_821_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v_fst_843_; lean_object* v_snd_844_; lean_object* v___x_845_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
v_fst_843_ = lean_ctor_get(v_a_842_, 0);
lean_inc(v_fst_843_);
v_snd_844_ = lean_ctor_get(v_a_842_, 1);
lean_inc(v_snd_844_);
lean_dec(v_a_842_);
lean_inc_ref(v___y_821_);
v___x_845_ = lean_apply_7(v_postNode_817_, v_val_831_, v_i_829_, v_children_830_, v_fst_843_, v_snd_844_, v___y_821_, lean_box(0));
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_863_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_863_ == 0)
{
v___x_848_ = v___x_845_;
v_isShared_849_ = v_isSharedCheck_863_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_863_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_fst_850_; lean_object* v_snd_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_862_; 
v_fst_850_ = lean_ctor_get(v_a_846_, 0);
v_snd_851_ = lean_ctor_get(v_a_846_, 1);
v_isSharedCheck_862_ = !lean_is_exclusive(v_a_846_);
if (v_isSharedCheck_862_ == 0)
{
v___x_853_ = v_a_846_;
v_isShared_854_ = v_isSharedCheck_862_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_snd_851_);
lean_inc(v_fst_850_);
lean_dec(v_a_846_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_862_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_855_, 0, v_fst_850_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_855_);
v___x_857_ = v___x_853_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v_snd_851_);
v___x_857_ = v_reuseFailAlloc_861_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_859_; 
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_857_);
v___x_859_ = v___x_848_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v___x_857_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
v_a_864_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_845_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_845_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_val_831_);
lean_dec_ref(v_children_830_);
lean_dec_ref(v_i_829_);
lean_dec_ref(v_postNode_817_);
v_a_872_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_841_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_841_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_913_; 
lean_dec_ref(v_preNode_816_);
v_isSharedCheck_913_ = !lean_is_exclusive(v_x_818_);
if (v_isSharedCheck_913_ == 0)
{
lean_object* v_unused_914_; 
v_unused_914_ = lean_ctor_get(v_x_818_, 0);
lean_dec(v_unused_914_);
v___x_881_ = v_x_818_;
v_isShared_882_ = v_isSharedCheck_913_;
goto v_resetjp_880_;
}
else
{
lean_dec(v_x_818_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_913_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = lean_box(0);
lean_inc_ref(v___y_821_);
v___x_884_ = lean_apply_7(v_postNode_817_, v_val_831_, v_i_829_, v_children_830_, v___x_883_, v_snd_835_, v___y_821_, lean_box(0));
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_904_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_904_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_904_ == 0)
{
v___x_887_ = v___x_884_;
v_isShared_888_ = v_isSharedCheck_904_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_884_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_904_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v_fst_889_; lean_object* v_snd_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_903_; 
v_fst_889_ = lean_ctor_get(v_a_885_, 0);
v_snd_890_ = lean_ctor_get(v_a_885_, 1);
v_isSharedCheck_903_ = !lean_is_exclusive(v_a_885_);
if (v_isSharedCheck_903_ == 0)
{
v___x_892_ = v_a_885_;
v_isShared_893_ = v_isSharedCheck_903_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_snd_890_);
lean_inc(v_fst_889_);
lean_dec(v_a_885_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_903_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v_fst_889_);
v___x_895_ = v___x_881_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_fst_889_);
v___x_895_ = v_reuseFailAlloc_902_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
lean_object* v___x_897_; 
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_895_);
v___x_897_ = v___x_892_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_895_);
lean_ctor_set(v_reuseFailAlloc_901_, 1, v_snd_890_);
v___x_897_ = v_reuseFailAlloc_901_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
lean_object* v___x_899_; 
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 0, v___x_897_);
v___x_899_ = v___x_887_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_del_object(v___x_881_);
v_a_905_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_884_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_884_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec(v_val_831_);
lean_dec_ref(v_children_830_);
lean_dec_ref(v_i_829_);
lean_dec_ref_known(v_x_818_, 1);
lean_dec_ref(v_postNode_817_);
lean_dec_ref(v_preNode_816_);
v_a_915_ = lean_ctor_get(v___x_832_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_832_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_832_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_832_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
default: 
{
lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_931_; 
lean_dec(v_x_818_);
lean_dec_ref(v_postNode_817_);
lean_dec_ref(v_preNode_816_);
v_isSharedCheck_931_ = !lean_is_exclusive(v_x_819_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v_x_819_, 0);
lean_dec(v_unused_932_);
v___x_924_ = v_x_819_;
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
else
{
lean_dec(v_x_819_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_931_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_929_; 
v___x_926_ = lean_box(0);
v___x_927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_926_);
lean_ctor_set(v___x_927_, 1, v___y_820_);
if (v_isShared_925_ == 0)
{
lean_ctor_set_tag(v___x_924_, 0);
lean_ctor_set(v___x_924_, 0, v___x_927_);
v___x_929_ = v___x_924_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v___x_927_);
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
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(lean_object* v_preNode_933_, lean_object* v_postNode_934_, lean_object* v___x_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
if (lean_obj_tag(v_x_936_) == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v___x_935_);
lean_dec_ref(v_postNode_934_);
lean_dec_ref(v_preNode_933_);
v___x_941_ = l_List_reverse___redArg(v_x_937_);
v___x_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___y_938_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
return v___x_943_;
}
else
{
lean_object* v_head_944_; lean_object* v_tail_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_965_; 
v_head_944_ = lean_ctor_get(v_x_936_, 0);
v_tail_945_ = lean_ctor_get(v_x_936_, 1);
v_isSharedCheck_965_ = !lean_is_exclusive(v_x_936_);
if (v_isSharedCheck_965_ == 0)
{
v___x_947_ = v_x_936_;
v_isShared_948_ = v_isSharedCheck_965_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_tail_945_);
lean_inc(v_head_944_);
lean_dec(v_x_936_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_965_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; 
lean_inc(v___x_935_);
lean_inc_ref(v_postNode_934_);
lean_inc_ref(v_preNode_933_);
v___x_949_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_933_, v_postNode_934_, v___x_935_, v_head_944_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v_fst_951_; lean_object* v_snd_952_; lean_object* v___x_954_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_a_950_);
lean_dec_ref_known(v___x_949_, 1);
v_fst_951_ = lean_ctor_get(v_a_950_, 0);
lean_inc(v_fst_951_);
v_snd_952_ = lean_ctor_get(v_a_950_, 1);
lean_inc(v_snd_952_);
lean_dec(v_a_950_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 1, v_x_937_);
lean_ctor_set(v___x_947_, 0, v_fst_951_);
v___x_954_ = v___x_947_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_fst_951_);
lean_ctor_set(v_reuseFailAlloc_956_, 1, v_x_937_);
v___x_954_ = v_reuseFailAlloc_956_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
v_x_936_ = v_tail_945_;
v_x_937_ = v___x_954_;
v___y_938_ = v_snd_952_;
goto _start;
}
}
else
{
lean_object* v_a_957_; lean_object* v___x_959_; uint8_t v_isShared_960_; uint8_t v_isSharedCheck_964_; 
lean_del_object(v___x_947_);
lean_dec(v_tail_945_);
lean_dec(v_x_937_);
lean_dec(v___x_935_);
lean_dec_ref(v_postNode_934_);
lean_dec_ref(v_preNode_933_);
v_a_957_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_964_ == 0)
{
v___x_959_ = v___x_949_;
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
else
{
lean_inc(v_a_957_);
lean_dec(v___x_949_);
v___x_959_ = lean_box(0);
v_isShared_960_ = v_isSharedCheck_964_;
goto v_resetjp_958_;
}
v_resetjp_958_:
{
lean_object* v___x_962_; 
if (v_isShared_960_ == 0)
{
v___x_962_ = v___x_959_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v_a_957_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg___boxed(lean_object* v_preNode_966_, lean_object* v_postNode_967_, lean_object* v___x_968_, lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_966_, v_postNode_967_, v___x_968_, v_x_969_, v_x_970_, v___y_971_, v___y_972_);
lean_dec_ref(v___y_972_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg___boxed(lean_object* v_preNode_975_, lean_object* v_postNode_976_, lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_975_, v_postNode_976_, v_x_977_, v_x_978_, v___y_979_, v___y_980_);
lean_dec_ref(v___y_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(lean_object* v_postNode_983_, lean_object* v_ci_984_, lean_object* v_i_985_, lean_object* v_cs_986_, lean_object* v_x_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
lean_object* v___x_991_; 
lean_inc_ref(v___y_989_);
v___x_991_ = lean_apply_6(v_postNode_983_, v_ci_984_, v_i_985_, v_cs_986_, v___y_988_, v___y_989_, lean_box(0));
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed(lean_object* v_postNode_992_, lean_object* v_ci_993_, lean_object* v_i_994_, lean_object* v_cs_995_, lean_object* v_x_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0(v_postNode_992_, v_ci_993_, v_i_994_, v_cs_995_, v_x_996_, v___y_997_, v___y_998_);
lean_dec_ref(v___y_998_);
lean_dec(v_x_996_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(lean_object* v_preNode_1001_, lean_object* v_postNode_1002_, lean_object* v_ctx_x3f_1003_, lean_object* v_t_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v___f_1008_; lean_object* v___x_1009_; 
v___f_1008_ = lean_alloc_closure((void*)(l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1008_, 0, v_postNode_1002_);
v___x_1009_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_1001_, v___f_1008_, v_ctx_x3f_1003_, v_t_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1027_; 
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1027_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1027_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v_snd_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1025_; 
v_snd_1014_ = lean_ctor_get(v_a_1010_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_a_1010_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v_a_1010_, 0);
lean_dec(v_unused_1026_);
v___x_1016_ = v_a_1010_;
v_isShared_1017_ = v_isSharedCheck_1025_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_snd_1014_);
lean_dec(v_a_1010_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1025_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = lean_box(0);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_snd_1014_);
v___x_1020_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
lean_object* v___x_1022_; 
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1020_);
v___x_1022_ = v___x_1012_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1009_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1009_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3___boxed(lean_object* v_preNode_1036_, lean_object* v_postNode_1037_, lean_object* v_ctx_x3f_1038_, lean_object* v_t_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v_preNode_1036_, v_postNode_1037_, v_ctx_x3f_1038_, v_t_1039_, v___y_1040_, v___y_1041_);
lean_dec_ref(v___y_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(lean_object* v_a_1045_, lean_object* v_b_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
lean_object* v_array_1050_; lean_object* v_start_1051_; lean_object* v_stop_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1075_; 
v_array_1050_ = lean_ctor_get(v_a_1045_, 0);
v_start_1051_ = lean_ctor_get(v_a_1045_, 1);
v_stop_1052_ = lean_ctor_get(v_a_1045_, 2);
v_isSharedCheck_1075_ = !lean_is_exclusive(v_a_1045_);
if (v_isSharedCheck_1075_ == 0)
{
v___x_1054_ = v_a_1045_;
v_isShared_1055_ = v_isSharedCheck_1075_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_stop_1052_);
lean_inc(v_start_1051_);
lean_inc(v_array_1050_);
lean_dec(v_a_1045_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1075_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
uint8_t v___x_1056_; 
v___x_1056_ = lean_nat_dec_lt(v_start_1051_, v_stop_1052_);
if (v___x_1056_ == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_del_object(v___x_1054_);
lean_dec(v_stop_1052_);
lean_dec(v_start_1051_);
lean_dec_ref(v_array_1050_);
v___x_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1057_, 0, v_b_1046_);
lean_ctor_set(v___x_1057_, 1, v___y_1047_);
v___x_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
return v___x_1058_;
}
else
{
lean_object* v___f_1059_; lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___f_1059_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___closed__0));
v___x_1060_ = lean_box(v___x_1056_);
v___f_1061_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___lam__1___boxed), 7, 1);
lean_closure_set(v___f_1061_, 0, v___x_1060_);
v___x_1062_ = lean_array_fget_borrowed(v_array_1050_, v_start_1051_);
v___x_1063_ = lean_box(0);
lean_inc(v___x_1062_);
v___x_1064_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v___x_1062_);
v___x_1065_ = l_Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3(v___f_1061_, v___f_1059_, v___x_1063_, v___x_1064_, v___y_1047_, v___y_1048_);
if (lean_obj_tag(v___x_1065_) == 0)
{
lean_object* v_a_1066_; lean_object* v_snd_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v_a_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_a_1066_);
lean_dec_ref_known(v___x_1065_, 1);
v_snd_1067_ = lean_ctor_get(v_a_1066_, 1);
lean_inc(v_snd_1067_);
lean_dec(v_a_1066_);
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_unsigned_to_nat(1u);
v___x_1070_ = lean_nat_add(v_start_1051_, v___x_1069_);
lean_dec(v_start_1051_);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 1, v___x_1070_);
v___x_1072_ = v___x_1054_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_array_1050_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1074_, 2, v_stop_1052_);
v___x_1072_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
v_a_1045_ = v___x_1072_;
v_b_1046_ = v___x_1068_;
v___y_1047_ = v_snd_1067_;
goto _start;
}
}
else
{
lean_del_object(v___x_1054_);
lean_dec(v_stop_1052_);
lean_dec(v_start_1051_);
lean_dec_ref(v_array_1050_);
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg___boxed(lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_1076_, v_b_1077_, v___y_1078_, v___y_1079_);
lean_dec_ref(v___y_1079_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(lean_object* v___x_1082_, uint8_t v_val_1083_, lean_object* v_as_1084_, size_t v_i_1085_, size_t v_stop_1086_, lean_object* v_b_1087_){
_start:
{
lean_object* v___y_1089_; uint8_t v___x_1093_; 
v___x_1093_ = lean_usize_dec_eq(v_i_1085_, v_stop_1086_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; lean_object* v_position_1095_; uint8_t v___x_1096_; uint8_t v___x_1097_; 
v___x_1094_ = lean_array_uget_borrowed(v_as_1084_, v_i_1085_);
v_position_1095_ = lean_ctor_get(v___x_1094_, 0);
v___x_1096_ = l_Lean_Syntax_Range_contains(v___x_1082_, v_position_1095_, v_val_1083_);
v___x_1097_ = lean_bool_not(v___x_1096_);
if (v___x_1097_ == 0)
{
v___y_1089_ = v_b_1087_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1098_; 
lean_inc(v___x_1094_);
v___x_1098_ = lean_array_push(v_b_1087_, v___x_1094_);
v___y_1089_ = v___x_1098_;
goto v___jp_1088_;
}
}
else
{
return v_b_1087_;
}
v___jp_1088_:
{
size_t v___x_1090_; size_t v___x_1091_; 
v___x_1090_ = ((size_t)1ULL);
v___x_1091_ = lean_usize_add(v_i_1085_, v___x_1090_);
v_i_1085_ = v___x_1091_;
v_b_1087_ = v___y_1089_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5___boxed(lean_object* v___x_1099_, lean_object* v_val_1100_, lean_object* v_as_1101_, lean_object* v_i_1102_, lean_object* v_stop_1103_, lean_object* v_b_1104_){
_start:
{
uint8_t v_val_21021__boxed_1105_; size_t v_i_boxed_1106_; size_t v_stop_boxed_1107_; lean_object* v_res_1108_; 
v_val_21021__boxed_1105_ = lean_unbox(v_val_1100_);
v_i_boxed_1106_ = lean_unbox_usize(v_i_1102_);
lean_dec(v_i_1102_);
v_stop_boxed_1107_ = lean_unbox_usize(v_stop_1103_);
lean_dec(v_stop_1103_);
v_res_1108_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1099_, v_val_21021__boxed_1105_, v_as_1101_, v_i_boxed_1106_, v_stop_boxed_1107_, v_b_1104_);
lean_dec_ref(v_as_1101_);
lean_dec_ref(v___x_1099_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(lean_object* v___x_1109_, lean_object* v_as_1110_, size_t v_i_1111_, size_t v_stop_1112_, lean_object* v_b_1113_){
_start:
{
lean_object* v___y_1115_; uint8_t v___x_1119_; 
v___x_1119_ = lean_usize_dec_eq(v_i_1111_, v_stop_1112_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v_position_1121_; uint8_t v___x_1122_; uint8_t v___x_1123_; 
v___x_1120_ = lean_array_uget_borrowed(v_as_1110_, v_i_1111_);
v_position_1121_ = lean_ctor_get(v___x_1120_, 0);
v___x_1122_ = 1;
v___x_1123_ = l_Lean_Syntax_Range_contains(v___x_1109_, v_position_1121_, v___x_1122_);
if (v___x_1123_ == 0)
{
v___y_1115_ = v_b_1113_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1124_; 
lean_inc(v___x_1120_);
v___x_1124_ = lean_array_push(v_b_1113_, v___x_1120_);
v___y_1115_ = v___x_1124_;
goto v___jp_1114_;
}
}
else
{
return v_b_1113_;
}
v___jp_1114_:
{
size_t v___x_1116_; size_t v___x_1117_; 
v___x_1116_ = ((size_t)1ULL);
v___x_1117_ = lean_usize_add(v_i_1111_, v___x_1116_);
v_i_1111_ = v___x_1117_;
v_b_1113_ = v___y_1115_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2___boxed(lean_object* v___x_1125_, lean_object* v_as_1126_, lean_object* v_i_1127_, lean_object* v_stop_1128_, lean_object* v_b_1129_){
_start:
{
size_t v_i_boxed_1130_; size_t v_stop_boxed_1131_; lean_object* v_res_1132_; 
v_i_boxed_1130_ = lean_unbox_usize(v_i_1127_);
lean_dec(v_i_1127_);
v_stop_boxed_1131_ = lean_unbox_usize(v_stop_1128_);
lean_dec(v_stop_1128_);
v_res_1132_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1125_, v_as_1126_, v_i_boxed_1130_, v_stop_boxed_1131_, v_b_1129_);
lean_dec_ref(v_as_1126_);
lean_dec_ref(v___x_1125_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(lean_object* v___x_1133_, size_t v_sz_1134_, size_t v_i_1135_, lean_object* v_bs_1136_){
_start:
{
uint8_t v___x_1138_; 
v___x_1138_ = lean_usize_dec_lt(v_i_1135_, v_sz_1134_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec_ref(v___x_1133_);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_bs_1136_);
return v___x_1139_;
}
else
{
lean_object* v_v_1140_; lean_object* v___x_1141_; 
v_v_1140_ = lean_array_uget_borrowed(v_bs_1136_, v_i_1135_);
lean_inc(v_v_1140_);
lean_inc_ref(v___x_1133_);
v___x_1141_ = l_Lean_Elab_InlayHintInfo_toLspInlayHint(v___x_1133_, v_v_1140_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v_bs_x27_1144_; size_t v___x_1145_; size_t v___x_1146_; lean_object* v___x_1147_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = lean_unsigned_to_nat(0u);
v_bs_x27_1144_ = lean_array_uset(v_bs_1136_, v_i_1135_, v___x_1143_);
v___x_1145_ = ((size_t)1ULL);
v___x_1146_ = lean_usize_add(v_i_1135_, v___x_1145_);
v___x_1147_ = lean_array_uset(v_bs_x27_1144_, v_i_1135_, v_a_1142_);
v_i_1135_ = v___x_1146_;
v_bs_1136_ = v___x_1147_;
goto _start;
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_bs_1136_);
lean_dec_ref(v___x_1133_);
v_a_1149_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1151_ = v___x_1141_;
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1141_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_Server_RequestError_ofIoError(v_a_1149_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg___boxed(lean_object* v___x_1158_, lean_object* v_sz_1159_, lean_object* v_i_1160_, lean_object* v_bs_1161_, lean_object* v___y_1162_){
_start:
{
size_t v_sz_boxed_1163_; size_t v_i_boxed_1164_; lean_object* v_res_1165_; 
v_sz_boxed_1163_ = lean_unbox_usize(v_sz_1159_);
lean_dec(v_sz_1159_);
v_i_boxed_1164_ = lean_unbox_usize(v_i_1160_);
lean_dec(v_i_1160_);
v_res_1165_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_1158_, v_sz_boxed_1163_, v_i_boxed_1164_, v_bs_1161_);
return v_res_1165_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2(void){
_start:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1168_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__1));
v___x_1169_ = lean_unsigned_to_nat(2u);
v___x_1170_ = lean_unsigned_to_nat(162u);
v___x_1171_ = ((lean_object*)(l_Lean_Server_FileWorker_handleInlayHints___closed__0));
v___x_1172_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_applyEditToHint_x3f_spec__2___lam__0___closed__0));
v___x_1173_ = l_mkPanicMessageWithDecl(v___x_1172_, v___x_1171_, v___x_1170_, v___x_1169_, v___x_1168_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints(lean_object* v_p_1174_, lean_object* v_s_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_doc_1178_; lean_object* v_toEditableDocumentCore_1179_; lean_object* v_meta_1180_; lean_object* v_cancelTk_1181_; lean_object* v_cmdSnaps_1182_; lean_object* v_text_1183_; lean_object* v_oldInlayHints_1184_; lean_object* v_oldFinishedSnaps_1185_; lean_object* v_lastEditTimestamp_x3f_1186_; uint8_t v_isFirstRequestAfterEdit_1187_; lean_object* v___y_1189_; lean_object* v___y_1190_; uint8_t v___y_1191_; lean_object* v___y_1192_; 
v_doc_1178_ = lean_ctor_get(v_a_1176_, 1);
v_toEditableDocumentCore_1179_ = lean_ctor_get(v_doc_1178_, 0);
v_meta_1180_ = lean_ctor_get(v_toEditableDocumentCore_1179_, 0);
v_cancelTk_1181_ = lean_ctor_get(v_a_1176_, 4);
v_cmdSnaps_1182_ = lean_ctor_get(v_toEditableDocumentCore_1179_, 2);
v_text_1183_ = lean_ctor_get(v_meta_1180_, 3);
v_oldInlayHints_1184_ = lean_ctor_get(v_s_1175_, 0);
v_oldFinishedSnaps_1185_ = lean_ctor_get(v_s_1175_, 1);
v_lastEditTimestamp_x3f_1186_ = lean_ctor_get(v_s_1175_, 2);
v_isFirstRequestAfterEdit_1187_ = lean_ctor_get_uint8(v_s_1175_, sizeof(void*)*3);
if (v_isFirstRequestAfterEdit_1187_ == 0)
{
lean_object* v___x_1215_; lean_object* v_range_1216_; lean_object* v___x_1217_; lean_object* v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1221_; lean_object* v___y_1222_; lean_object* v_snd_1223_; lean_object* v___y_1236_; lean_object* v___y_1237_; uint8_t v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v_lower_1241_; lean_object* v_upper_1242_; lean_object* v___y_1260_; uint8_t v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1267_; uint8_t v___y_1268_; uint8_t v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1286_; uint8_t v___y_1287_; uint8_t v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1298_; 
v___x_1215_ = lean_io_mono_ms_now();
v_range_1216_ = lean_ctor_get(v_p_1174_, 2);
lean_inc_ref(v_range_1216_);
lean_dec_ref(v_p_1174_);
v___x_1217_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_1183_, v_range_1216_);
if (lean_obj_tag(v_lastEditTimestamp_x3f_1186_) == 0)
{
lean_object* v___x_1347_; 
lean_dec(v___x_1215_);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___y_1298_ = v___x_1347_;
goto v___jp_1297_;
}
else
{
lean_object* v_val_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_val_1348_ = lean_ctor_get(v_lastEditTimestamp_x3f_1186_, 0);
v___x_1349_ = lean_unsigned_to_nat(3000u);
v___x_1350_ = lean_nat_sub(v___x_1215_, v_val_1348_);
lean_dec(v___x_1215_);
v___x_1351_ = lean_nat_sub(v___x_1349_, v___x_1350_);
lean_dec(v___x_1350_);
v___y_1298_ = v___x_1351_;
goto v___jp_1297_;
}
v___jp_1218_:
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1224_ = l_Array_append___redArg(v_snd_1223_, v___y_1220_);
lean_dec_ref(v___y_1220_);
v___x_1225_ = lean_array_get_size(v___x_1224_);
v___x_1226_ = lean_mk_empty_array_with_capacity(v___y_1222_);
v___x_1227_ = lean_nat_dec_lt(v___y_1222_, v___x_1225_);
lean_dec(v___y_1222_);
if (v___x_1227_ == 0)
{
lean_dec_ref(v___x_1217_);
v___y_1189_ = v___y_1219_;
v___y_1190_ = v___x_1224_;
v___y_1191_ = v___y_1221_;
v___y_1192_ = v___x_1226_;
goto v___jp_1188_;
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = lean_nat_dec_le(v___x_1225_, v___x_1225_);
if (v___x_1228_ == 0)
{
if (v___x_1227_ == 0)
{
lean_dec_ref(v___x_1217_);
v___y_1189_ = v___y_1219_;
v___y_1190_ = v___x_1224_;
v___y_1191_ = v___y_1221_;
v___y_1192_ = v___x_1226_;
goto v___jp_1188_;
}
else
{
size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = lean_usize_of_nat(v___x_1225_);
v___x_1231_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1217_, v___x_1224_, v___x_1229_, v___x_1230_, v___x_1226_);
lean_dec_ref(v___x_1217_);
v___y_1189_ = v___y_1219_;
v___y_1190_ = v___x_1224_;
v___y_1191_ = v___y_1221_;
v___y_1192_ = v___x_1231_;
goto v___jp_1188_;
}
}
else
{
size_t v___x_1232_; size_t v___x_1233_; lean_object* v___x_1234_; 
v___x_1232_ = ((size_t)0ULL);
v___x_1233_ = lean_usize_of_nat(v___x_1225_);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__2(v___x_1217_, v___x_1224_, v___x_1232_, v___x_1233_, v___x_1226_);
lean_dec_ref(v___x_1217_);
v___y_1189_ = v___y_1219_;
v___y_1190_ = v___x_1224_;
v___y_1191_ = v___y_1221_;
v___y_1192_ = v___x_1234_;
goto v___jp_1188_;
}
}
}
v___jp_1235_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1243_ = l_Array_toSubarray___redArg(v___y_1240_, v_lower_1241_, v_upper_1242_);
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_mk_empty_array_with_capacity(v___y_1239_);
v___x_1246_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v___x_1243_, v___x_1244_, v___x_1245_, v_a_1176_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; lean_object* v_snd_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1247_);
lean_dec_ref_known(v___x_1246_, 1);
v_snd_1248_ = lean_ctor_get(v_a_1247_, 1);
lean_inc(v_snd_1248_);
lean_dec(v_a_1247_);
v___y_1219_ = v___y_1236_;
v___y_1220_ = v___y_1237_;
v___y_1221_ = v___y_1238_;
v___y_1222_ = v___y_1239_;
v_snd_1223_ = v_snd_1248_;
goto v___jp_1218_;
}
else
{
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1249_; lean_object* v_snd_1250_; 
v_a_1249_ = lean_ctor_get(v___x_1246_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1246_, 1);
v_snd_1250_ = lean_ctor_get(v_a_1249_, 1);
lean_inc(v_snd_1250_);
lean_dec(v_a_1249_);
v___y_1219_ = v___y_1236_;
v___y_1220_ = v___y_1237_;
v___y_1221_ = v___y_1238_;
v___y_1222_ = v___y_1239_;
v_snd_1223_ = v_snd_1250_;
goto v___jp_1218_;
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___x_1217_);
lean_dec(v_lastEditTimestamp_x3f_1186_);
v_a_1251_ = lean_ctor_get(v___x_1246_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1246_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1246_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1246_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
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
v___jp_1259_:
{
uint8_t v___x_1265_; 
v___x_1265_ = lean_nat_dec_le(v_oldFinishedSnaps_1185_, v___y_1263_);
if (v___x_1265_ == 0)
{
lean_inc(v___y_1260_);
v___y_1236_ = v___y_1260_;
v___y_1237_ = v___y_1264_;
v___y_1238_ = v___y_1261_;
v___y_1239_ = v___y_1263_;
v___y_1240_ = v___y_1262_;
v_lower_1241_ = v_oldFinishedSnaps_1185_;
v_upper_1242_ = v___y_1260_;
goto v___jp_1235_;
}
else
{
lean_dec(v_oldFinishedSnaps_1185_);
lean_inc(v___y_1263_);
lean_inc(v___y_1260_);
v___y_1236_ = v___y_1260_;
v___y_1237_ = v___y_1264_;
v___y_1238_ = v___y_1261_;
v___y_1239_ = v___y_1263_;
v___y_1240_ = v___y_1262_;
v_lower_1241_ = v___y_1263_;
v_upper_1242_ = v___y_1260_;
goto v___jp_1235_;
}
}
v___jp_1266_:
{
lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; uint8_t v___x_1276_; 
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_array_get_size(v_oldInlayHints_1184_);
v___x_1275_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init___closed__0));
v___x_1276_ = lean_nat_dec_lt(v___x_1273_, v___x_1274_);
if (v___x_1276_ == 0)
{
lean_dec(v___y_1272_);
lean_dec(v___y_1270_);
lean_dec_ref(v_oldInlayHints_1184_);
v___y_1260_ = v___y_1267_;
v___y_1261_ = v___y_1268_;
v___y_1262_ = v___y_1271_;
v___y_1263_ = v___x_1273_;
v___y_1264_ = v___x_1275_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1277_, 0, v___y_1270_);
lean_ctor_set(v___x_1277_, 1, v___y_1272_);
v___x_1278_ = lean_nat_dec_le(v___x_1274_, v___x_1274_);
if (v___x_1278_ == 0)
{
if (v___x_1276_ == 0)
{
lean_dec_ref_known(v___x_1277_, 2);
lean_dec_ref(v_oldInlayHints_1184_);
v___y_1260_ = v___y_1267_;
v___y_1261_ = v___y_1268_;
v___y_1262_ = v___y_1271_;
v___y_1263_ = v___x_1273_;
v___y_1264_ = v___x_1275_;
goto v___jp_1259_;
}
else
{
size_t v___x_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = lean_usize_of_nat(v___x_1274_);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1277_, v___y_1269_, v_oldInlayHints_1184_, v___x_1279_, v___x_1280_, v___x_1275_);
lean_dec_ref(v_oldInlayHints_1184_);
lean_dec_ref_known(v___x_1277_, 2);
v___y_1260_ = v___y_1267_;
v___y_1261_ = v___y_1268_;
v___y_1262_ = v___y_1271_;
v___y_1263_ = v___x_1273_;
v___y_1264_ = v___x_1281_;
goto v___jp_1259_;
}
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = lean_usize_of_nat(v___x_1274_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_handleInlayHints_spec__5(v___x_1277_, v___y_1269_, v_oldInlayHints_1184_, v___x_1282_, v___x_1283_, v___x_1275_);
lean_dec_ref(v_oldInlayHints_1184_);
lean_dec_ref_known(v___x_1277_, 2);
v___y_1260_ = v___y_1267_;
v___y_1261_ = v___y_1268_;
v___y_1262_ = v___y_1271_;
v___y_1263_ = v___x_1273_;
v___y_1264_ = v___x_1284_;
goto v___jp_1259_;
}
}
}
v___jp_1285_:
{
lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1292_ = lean_nat_sub(v___y_1286_, v___y_1289_);
v___x_1293_ = lean_nat_dec_lt(v___x_1292_, v___y_1286_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; 
lean_dec(v___x_1292_);
v___x_1294_ = lean_unsigned_to_nat(0u);
v___y_1267_ = v___y_1286_;
v___y_1268_ = v___y_1287_;
v___y_1269_ = v___y_1288_;
v___y_1270_ = v___y_1291_;
v___y_1271_ = v___y_1290_;
v___y_1272_ = v___x_1294_;
goto v___jp_1266_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_array_fget_borrowed(v___y_1290_, v___x_1292_);
lean_dec(v___x_1292_);
v___x_1296_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1295_);
v___y_1267_ = v___y_1286_;
v___y_1268_ = v___y_1287_;
v___y_1269_ = v___y_1288_;
v___y_1270_ = v___y_1291_;
v___y_1271_ = v___y_1290_;
v___y_1272_ = v___x_1296_;
goto v___jp_1266_;
}
}
v___jp_1297_:
{
uint32_t v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_snd_1302_; lean_object* v_fst_1303_; lean_object* v_snd_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1345_; 
v___x_1299_ = lean_uint32_of_nat(v___y_1298_);
lean_dec(v___y_1298_);
v___x_1300_ = l_Lean_Server_RequestCancellationToken_cancellationTasks(v_cancelTk_1181_);
lean_inc(v_cmdSnaps_1182_);
v___x_1301_ = l_Lean_AsyncList_getFinishedPrefixWithConsistentLatency___redArg(v_cmdSnaps_1182_, v___x_1299_, v___x_1300_);
v_snd_1302_ = lean_ctor_get(v___x_1301_, 1);
lean_inc(v_snd_1302_);
v_fst_1303_ = lean_ctor_get(v___x_1301_, 0);
lean_inc(v_fst_1303_);
lean_dec_ref(v___x_1301_);
v_snd_1304_ = lean_ctor_get(v_snd_1302_, 1);
v_isSharedCheck_1345_ = !lean_is_exclusive(v_snd_1302_);
if (v_isSharedCheck_1345_ == 0)
{
lean_object* v_unused_1346_; 
v_unused_1346_ = lean_ctor_get(v_snd_1302_, 0);
lean_dec(v_unused_1346_);
v___x_1306_ = v_snd_1302_;
v_isShared_1307_ = v_isSharedCheck_1345_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_snd_1304_);
lean_dec(v_snd_1302_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1345_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
uint8_t v___x_1308_; 
v___x_1308_ = l_Lean_Server_RequestCancellationToken_wasCancelled(v_cancelTk_1181_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
lean_inc(v_lastEditTimestamp_x3f_1186_);
lean_inc(v_oldFinishedSnaps_1185_);
lean_inc_ref(v_oldInlayHints_1184_);
lean_del_object(v___x_1306_);
lean_dec_ref(v_s_1175_);
v___x_1309_ = lean_array_mk(v_fst_1303_);
v___x_1310_ = lean_array_get_size(v___x_1309_);
v___x_1311_ = lean_nat_dec_le(v_oldFinishedSnaps_1185_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
lean_dec_ref(v___x_1309_);
lean_dec(v_snd_1304_);
lean_dec_ref(v___x_1217_);
lean_dec(v_lastEditTimestamp_x3f_1186_);
lean_dec(v_oldFinishedSnaps_1185_);
lean_dec_ref(v_oldInlayHints_1184_);
v___x_1312_ = lean_obj_once(&l_Lean_Server_FileWorker_handleInlayHints___closed__2, &l_Lean_Server_FileWorker_handleInlayHints___closed__2_once, _init_l_Lean_Server_FileWorker_handleInlayHints___closed__2);
v___x_1313_ = l_panic___at___00Lean_Server_FileWorker_handleInlayHints_spec__0(v___x_1312_, v_a_1176_);
return v___x_1313_;
}
else
{
lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1314_ = lean_unsigned_to_nat(1u);
v___x_1315_ = lean_nat_sub(v_oldFinishedSnaps_1185_, v___x_1314_);
v___x_1316_ = lean_nat_dec_lt(v___x_1315_, v___x_1310_);
if (v___x_1316_ == 0)
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
lean_dec(v___x_1315_);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_unbox(v_snd_1304_);
lean_dec(v_snd_1304_);
v___y_1286_ = v___x_1310_;
v___y_1287_ = v___x_1318_;
v___y_1288_ = v___x_1308_;
v___y_1289_ = v___x_1314_;
v___y_1290_ = v___x_1309_;
v___y_1291_ = v___x_1317_;
goto v___jp_1285_;
}
else
{
lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1319_ = lean_array_fget(v___x_1309_, v___x_1315_);
lean_dec(v___x_1315_);
v___x_1320_ = l_Lean_Server_Snapshots_Snapshot_endPos(v___x_1319_);
lean_dec(v___x_1319_);
v___x_1321_ = lean_unbox(v_snd_1304_);
lean_dec(v_snd_1304_);
v___y_1286_ = v___x_1310_;
v___y_1287_ = v___x_1321_;
v___y_1288_ = v___x_1308_;
v___y_1289_ = v___x_1314_;
v___y_1290_ = v___x_1309_;
v___y_1291_ = v___x_1320_;
goto v___jp_1285_;
}
}
}
else
{
size_t v_sz_1322_; size_t v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_snd_1304_);
lean_dec(v_fst_1303_);
lean_dec_ref(v___x_1217_);
v_sz_1322_ = lean_array_size(v_oldInlayHints_1184_);
v___x_1323_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1184_);
lean_inc_ref(v_text_1183_);
v___x_1324_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1183_, v_sz_1322_, v___x_1323_, v_oldInlayHints_1184_);
if (lean_obj_tag(v___x_1324_) == 0)
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1336_; 
v_a_1325_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1327_ = v___x_1324_;
v_isShared_1328_ = v_isSharedCheck_1336_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1324_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1336_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1329_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1329_, 0, v_a_1325_);
lean_ctor_set_uint8(v___x_1329_, sizeof(void*)*1, v_isFirstRequestAfterEdit_1187_);
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 1, v_s_1175_);
lean_ctor_set(v___x_1306_, 0, v___x_1329_);
v___x_1331_ = v___x_1306_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1329_);
lean_ctor_set(v_reuseFailAlloc_1335_, 1, v_s_1175_);
v___x_1331_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
lean_object* v___x_1333_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v___x_1331_);
v___x_1333_ = v___x_1327_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v___x_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_del_object(v___x_1306_);
lean_dec_ref(v_s_1175_);
v_a_1337_ = lean_ctor_get(v___x_1324_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1324_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1324_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
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
}
}
}
else
{
lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1380_; 
lean_inc(v_lastEditTimestamp_x3f_1186_);
lean_inc(v_oldFinishedSnaps_1185_);
lean_inc_ref(v_oldInlayHints_1184_);
lean_dec_ref(v_p_1174_);
v_isSharedCheck_1380_ = !lean_is_exclusive(v_s_1175_);
if (v_isSharedCheck_1380_ == 0)
{
lean_object* v_unused_1381_; lean_object* v_unused_1382_; lean_object* v_unused_1383_; 
v_unused_1381_ = lean_ctor_get(v_s_1175_, 2);
lean_dec(v_unused_1381_);
v_unused_1382_ = lean_ctor_get(v_s_1175_, 1);
lean_dec(v_unused_1382_);
v_unused_1383_ = lean_ctor_get(v_s_1175_, 0);
lean_dec(v_unused_1383_);
v___x_1353_ = v_s_1175_;
v_isShared_1354_ = v_isSharedCheck_1380_;
goto v_resetjp_1352_;
}
else
{
lean_dec(v_s_1175_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1380_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
size_t v_sz_1355_; size_t v___x_1356_; lean_object* v___x_1357_; 
v_sz_1355_ = lean_array_size(v_oldInlayHints_1184_);
v___x_1356_ = ((size_t)0ULL);
lean_inc_ref(v_oldInlayHints_1184_);
lean_inc_ref(v_text_1183_);
v___x_1357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1183_, v_sz_1355_, v___x_1356_, v_oldInlayHints_1184_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1371_; 
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1371_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1371_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
uint8_t v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1362_ = 0;
v___x_1363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1363_, 0, v_a_1358_);
lean_ctor_set_uint8(v___x_1363_, sizeof(void*)*1, v___x_1362_);
if (v_isShared_1354_ == 0)
{
v___x_1365_ = v___x_1353_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_oldInlayHints_1184_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v_oldFinishedSnaps_1185_);
lean_ctor_set(v_reuseFailAlloc_1370_, 2, v_lastEditTimestamp_x3f_1186_);
v___x_1365_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1366_; lean_object* v___x_1368_; 
lean_ctor_set_uint8(v___x_1365_, sizeof(void*)*3, v___x_1362_);
v___x_1366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1363_);
lean_ctor_set(v___x_1366_, 1, v___x_1365_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set(v___x_1360_, 0, v___x_1366_);
v___x_1368_ = v___x_1360_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_del_object(v___x_1353_);
lean_dec(v_lastEditTimestamp_x3f_1186_);
lean_dec(v_oldFinishedSnaps_1185_);
lean_dec_ref(v_oldInlayHints_1184_);
v_a_1372_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1357_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1357_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
v___jp_1188_:
{
size_t v_sz_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
v_sz_1193_ = lean_array_size(v___y_1192_);
v___x_1194_ = ((size_t)0ULL);
lean_inc_ref(v_text_1183_);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v_text_1183_, v_sz_1193_, v___x_1194_, v___y_1192_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1206_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1206_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
v___x_1200_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1200_, 0, v_a_1196_);
lean_ctor_set_uint8(v___x_1200_, sizeof(void*)*1, v___y_1191_);
v___x_1201_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1201_, 0, v___y_1190_);
lean_ctor_set(v___x_1201_, 1, v___y_1189_);
lean_ctor_set(v___x_1201_, 2, v_lastEditTimestamp_x3f_1186_);
lean_ctor_set_uint8(v___x_1201_, sizeof(void*)*3, v_isFirstRequestAfterEdit_1187_);
v___x_1202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1200_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 0, v___x_1202_);
v___x_1204_ = v___x_1198_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec(v_lastEditTimestamp_x3f_1186_);
v_a_1207_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1195_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1195_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHints___boxed(lean_object* v_p_1384_, lean_object* v_s_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Lean_Server_FileWorker_handleInlayHints(v_p_1384_, v_s_1385_, v_a_1386_);
lean_dec_ref(v_a_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(lean_object* v___x_1389_, size_t v_sz_1390_, size_t v_i_1391_, lean_object* v_bs_1392_, lean_object* v___y_1393_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___redArg(v___x_1389_, v_sz_1390_, v_i_1391_, v_bs_1392_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1___boxed(lean_object* v___x_1396_, lean_object* v_sz_1397_, lean_object* v_i_1398_, lean_object* v_bs_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
size_t v_sz_boxed_1402_; size_t v_i_boxed_1403_; lean_object* v_res_1404_; 
v_sz_boxed_1402_ = lean_unbox_usize(v_sz_1397_);
lean_dec(v_sz_1397_);
v_i_boxed_1403_ = lean_unbox_usize(v_i_1398_);
lean_dec(v_i_1398_);
v_res_1404_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Server_FileWorker_handleInlayHints_spec__1(v___x_1396_, v_sz_boxed_1402_, v_i_boxed_1403_, v_bs_1399_, v___y_1400_);
lean_dec_ref(v___y_1400_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(lean_object* v_inst_1405_, lean_object* v_R_1406_, lean_object* v_a_1407_, lean_object* v_b_1408_, lean_object* v_c_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___redArg(v_a_1407_, v_b_1408_, v___y_1410_, v___y_1411_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4___boxed(lean_object* v_inst_1414_, lean_object* v_R_1415_, lean_object* v_a_1416_, lean_object* v_b_1417_, lean_object* v_c_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Server_FileWorker_handleInlayHints_spec__4(v_inst_1414_, v_R_1415_, v_a_1416_, v_b_1417_, v_c_1418_, v___y_1419_, v___y_1420_);
lean_dec_ref(v___y_1420_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(lean_object* v_00_u03b1_1423_, lean_object* v_msg_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___redArg(v_msg_1424_, v___y_1425_, v___y_1426_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4___boxed(lean_object* v_00_u03b1_1429_, lean_object* v_msg_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_panic___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__4(v_00_u03b1_1429_, v_msg_1430_, v___y_1431_, v___y_1432_);
lean_dec_ref(v___y_1432_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(lean_object* v_00_u03b1_1435_, lean_object* v_preNode_1436_, lean_object* v_postNode_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___redArg(v_preNode_1436_, v_postNode_1437_, v_x_1438_, v_x_1439_, v___y_1440_, v___y_1441_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3___boxed(lean_object* v_00_u03b1_1444_, lean_object* v_preNode_1445_, lean_object* v_postNode_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l___private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3(v_00_u03b1_1444_, v_preNode_1445_, v_postNode_1446_, v_x_1447_, v_x_1448_, v___y_1449_, v___y_1450_);
lean_dec_ref(v___y_1450_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(lean_object* v_00_u03b1_1453_, lean_object* v_preNode_1454_, lean_object* v_postNode_1455_, lean_object* v___x_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___redArg(v_preNode_1454_, v_postNode_1455_, v___x_1456_, v_x_1457_, v_x_1458_, v___y_1459_, v___y_1460_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1463_, lean_object* v_preNode_1464_, lean_object* v_postNode_1465_, lean_object* v___x_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_List_mapM_loop___at___00__private_Lean_Server_InfoUtils_0__Lean_Elab_InfoTree_visitM_go___at___00Lean_Elab_InfoTree_visitM_x27___at___00Lean_Server_FileWorker_handleInlayHints_spec__3_spec__3_spec__5(v_00_u03b1_1463_, v_preNode_1464_, v_postNode_1465_, v___x_1466_, v_x_1467_, v_x_1468_, v___y_1469_, v___y_1470_);
lean_dec_ref(v___y_1470_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v_as_1477_, size_t v_sz_1478_, size_t v_i_1479_, lean_object* v_b_1480_){
_start:
{
uint8_t v___x_1482_; 
v___x_1482_ = lean_usize_dec_lt(v_i_1479_, v_sz_1478_);
if (v___x_1482_ == 0)
{
lean_object* v___x_1483_; 
v___x_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1483_, 0, v_b_1480_);
return v___x_1483_;
}
else
{
lean_object* v_snd_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1527_; 
v_snd_1484_ = lean_ctor_get(v_b_1480_, 1);
v_isSharedCheck_1527_ = !lean_is_exclusive(v_b_1480_);
if (v_isSharedCheck_1527_ == 0)
{
lean_object* v_unused_1528_; 
v_unused_1528_ = lean_ctor_get(v_b_1480_, 0);
lean_dec(v_unused_1528_);
v___x_1486_ = v_b_1480_;
v_isShared_1487_ = v_isSharedCheck_1527_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_snd_1484_);
lean_dec(v_b_1480_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1527_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_fst_1488_; lean_object* v_snd_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1526_; 
v_fst_1488_ = lean_ctor_get(v_snd_1484_, 0);
v_snd_1489_ = lean_ctor_get(v_snd_1484_, 1);
v_isSharedCheck_1526_ = !lean_is_exclusive(v_snd_1484_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1491_ = v_snd_1484_;
v_isShared_1492_ = v_isSharedCheck_1526_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_snd_1489_);
lean_inc(v_fst_1488_);
lean_dec(v_snd_1484_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1526_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_a_1493_; 
v_a_1493_ = lean_array_uget_borrowed(v_as_1477_, v_i_1479_);
if (lean_obj_tag(v_a_1493_) == 0)
{
lean_object* v_range_1494_; lean_object* v_text_1495_; lean_object* v_mod_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
v_range_1494_ = lean_ctor_get(v_a_1493_, 0);
v_text_1495_ = lean_ctor_get(v_a_1493_, 1);
v_mod_1496_ = lean_ctor_get(v___x_1476_, 1);
v___x_1497_ = lean_box(0);
lean_inc_ref(v_range_1494_);
v___x_1498_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1475_, v_range_1494_);
lean_inc(v_fst_1488_);
v___x_1499_ = l_Lean_Server_FileWorker_applyEditToHint_x3f(v_mod_1496_, v_fst_1488_, v___x_1498_, v_text_1495_);
if (lean_obj_tag(v___x_1499_) == 1)
{
lean_object* v_val_1500_; lean_object* v___x_1502_; 
lean_dec(v_fst_1488_);
v_val_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1499_, 1);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v_val_1500_);
v___x_1502_ = v___x_1491_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v_val_1500_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_snd_1489_);
v___x_1502_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
lean_object* v___x_1504_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v___x_1502_);
lean_ctor_set(v___x_1486_, 0, v___x_1497_);
v___x_1504_ = v___x_1486_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v___x_1502_);
v___x_1504_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
size_t v___x_1505_; size_t v___x_1506_; 
v___x_1505_ = ((size_t)1ULL);
v___x_1506_ = lean_usize_add(v_i_1479_, v___x_1505_);
v_i_1479_ = v___x_1506_;
v_b_1480_ = v___x_1504_;
goto _start;
}
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1512_; 
lean_dec(v___x_1499_);
lean_dec(v_snd_1489_);
v___x_1510_ = lean_box(v___x_1482_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 1, v___x_1510_);
v___x_1512_ = v___x_1491_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_fst_1488_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1510_);
v___x_1512_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1514_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v___x_1512_);
lean_ctor_set(v___x_1486_, 0, v___x_1497_);
v___x_1514_ = v___x_1486_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v___x_1497_);
lean_ctor_set(v_reuseFailAlloc_1516_, 1, v___x_1512_);
v___x_1514_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
}
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1520_; 
v___x_1518_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___closed__0));
if (v_isShared_1492_ == 0)
{
v___x_1520_ = v___x_1491_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_fst_1488_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v_snd_1489_);
v___x_1520_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
lean_object* v___x_1522_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 1, v___x_1520_);
lean_ctor_set(v___x_1486_, 0, v___x_1518_);
v___x_1522_ = v___x_1486_;
goto v_reusejp_1521_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1518_);
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
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg___boxed(lean_object* v___x_1529_, lean_object* v___x_1530_, lean_object* v_as_1531_, lean_object* v_sz_1532_, lean_object* v_i_1533_, lean_object* v_b_1534_, lean_object* v___y_1535_){
_start:
{
size_t v_sz_boxed_1536_; size_t v_i_boxed_1537_; lean_object* v_res_1538_; 
v_sz_boxed_1536_ = lean_unbox_usize(v_sz_1532_);
lean_dec(v_sz_1532_);
v_i_boxed_1537_ = lean_unbox_usize(v_i_1533_);
lean_dec(v_i_1533_);
v_res_1538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1529_, v___x_1530_, v_as_1531_, v_sz_boxed_1536_, v_i_boxed_1537_, v_b_1534_);
lean_dec_ref(v_as_1531_);
lean_dec_ref(v___x_1530_);
lean_dec_ref(v___x_1529_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(lean_object* v_p_1539_, lean_object* v___x_1540_, lean_object* v___x_1541_, lean_object* v_as_1542_, size_t v_sz_1543_, size_t v_i_1544_, lean_object* v_b_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_a_1549_; uint8_t v___x_1553_; 
v___x_1553_ = lean_usize_dec_lt(v_i_1544_, v_sz_1543_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
v___x_1554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1554_, 0, v_b_1545_);
return v___x_1554_;
}
else
{
lean_object* v_contentChanges_1555_; lean_object* v___x_1556_; lean_object* v_a_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; size_t v_sz_1562_; size_t v___x_1563_; lean_object* v___x_1564_; 
v_contentChanges_1555_ = lean_ctor_get(v_p_1539_, 1);
v___x_1556_ = lean_box(0);
v_a_1557_ = lean_array_uget_borrowed(v_as_1542_, v_i_1544_);
v___x_1558_ = 0;
v___x_1559_ = lean_box(v___x_1558_);
lean_inc(v_a_1557_);
v___x_1560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1560_, 0, v_a_1557_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1556_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v_sz_1562_ = lean_array_size(v_contentChanges_1555_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1540_, v___x_1541_, v_contentChanges_1555_, v_sz_1562_, v___x_1563_, v___x_1561_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1600_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1567_ = v___x_1564_;
v_isShared_1568_ = v_isSharedCheck_1600_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1564_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1600_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v_fst_1569_; 
v_fst_1569_ = lean_ctor_get(v_a_1565_, 0);
if (lean_obj_tag(v_fst_1569_) == 0)
{
lean_object* v_snd_1570_; lean_object* v_snd_1571_; lean_object* v_fst_1572_; lean_object* v_snd_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1586_; 
lean_del_object(v___x_1567_);
v_snd_1570_ = lean_ctor_get(v_a_1565_, 1);
lean_inc(v_snd_1570_);
lean_dec(v_a_1565_);
v_snd_1571_ = lean_ctor_get(v_b_1545_, 1);
lean_inc(v_snd_1571_);
lean_dec_ref(v_b_1545_);
v_fst_1572_ = lean_ctor_get(v_snd_1570_, 0);
v_snd_1573_ = lean_ctor_get(v_snd_1570_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_snd_1570_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1575_ = v_snd_1570_;
v_isShared_1576_ = v_isSharedCheck_1586_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_snd_1573_);
lean_inc(v_fst_1572_);
lean_dec(v_snd_1570_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1586_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
uint8_t v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = lean_unbox(v_snd_1573_);
lean_dec(v_snd_1573_);
v___x_1578_ = lean_bool_not(v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1580_; 
lean_dec(v_fst_1572_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v_snd_1571_);
lean_ctor_set(v___x_1575_, 0, v___x_1556_);
v___x_1580_ = v___x_1575_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_snd_1571_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
v_a_1549_ = v___x_1580_;
goto v___jp_1548_;
}
}
else
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_array_push(v_snd_1571_, v_fst_1572_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v___x_1582_);
lean_ctor_set(v___x_1575_, 0, v___x_1556_);
v___x_1584_ = v___x_1575_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
v_a_1549_ = v___x_1584_;
goto v___jp_1548_;
}
}
}
}
else
{
lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1597_; 
lean_inc_ref(v_fst_1569_);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_a_1565_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; lean_object* v_unused_1599_; 
v_unused_1598_ = lean_ctor_get(v_a_1565_, 1);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_a_1565_, 0);
lean_dec(v_unused_1599_);
v___x_1588_ = v_a_1565_;
v_isShared_1589_ = v_isSharedCheck_1597_;
goto v_resetjp_1587_;
}
else
{
lean_dec(v_a_1565_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1597_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v_snd_1590_; lean_object* v___x_1592_; 
v_snd_1590_ = lean_ctor_get(v_b_1545_, 1);
lean_inc(v_snd_1590_);
lean_dec_ref(v_b_1545_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 1, v_snd_1590_);
v___x_1592_ = v___x_1588_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v_fst_1569_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_snd_1590_);
v___x_1592_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
lean_object* v___x_1594_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1592_);
v___x_1594_ = v___x_1567_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
}
}
}
else
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
lean_dec_ref(v_b_1545_);
v_a_1601_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v___x_1564_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v___x_1564_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
v___jp_1548_:
{
size_t v___x_1550_; size_t v___x_1551_; 
v___x_1550_ = ((size_t)1ULL);
v___x_1551_ = lean_usize_add(v_i_1544_, v___x_1550_);
v_i_1544_ = v___x_1551_;
v_b_1545_ = v_a_1549_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1___boxed(lean_object* v_p_1609_, lean_object* v___x_1610_, lean_object* v___x_1611_, lean_object* v_as_1612_, lean_object* v_sz_1613_, lean_object* v_i_1614_, lean_object* v_b_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
size_t v_sz_boxed_1618_; size_t v_i_boxed_1619_; lean_object* v_res_1620_; 
v_sz_boxed_1618_ = lean_unbox_usize(v_sz_1613_);
lean_dec(v_sz_1613_);
v_i_boxed_1619_ = lean_unbox_usize(v_i_1614_);
lean_dec(v_i_1614_);
v_res_1620_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1609_, v___x_1610_, v___x_1611_, v_as_1612_, v_sz_boxed_1618_, v_i_boxed_1619_, v_b_1615_, v___y_1616_);
lean_dec_ref(v___y_1616_);
lean_dec_ref(v_as_1612_);
lean_dec_ref(v___x_1611_);
lean_dec_ref(v___x_1610_);
lean_dec_ref(v_p_1609_);
return v_res_1620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(lean_object* v_p_1624_, lean_object* v_oldInlayHints_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v_doc_1628_; lean_object* v_toEditableDocumentCore_1629_; lean_object* v_meta_1630_; lean_object* v_text_1631_; lean_object* v___x_1632_; size_t v_sz_1633_; size_t v___x_1634_; lean_object* v___x_1635_; 
v_doc_1628_ = lean_ctor_get(v_a_1626_, 1);
v_toEditableDocumentCore_1629_ = lean_ctor_get(v_doc_1628_, 0);
v_meta_1630_ = lean_ctor_get(v_toEditableDocumentCore_1629_, 0);
v_text_1631_ = lean_ctor_get(v_meta_1630_, 3);
v___x_1632_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___closed__0));
v_sz_1633_ = lean_array_size(v_oldInlayHints_1625_);
v___x_1634_ = ((size_t)0ULL);
v___x_1635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__1(v_p_1624_, v_text_1631_, v_meta_1630_, v_oldInlayHints_1625_, v_sz_1633_, v___x_1634_, v___x_1632_, v_a_1626_);
if (lean_obj_tag(v___x_1635_) == 0)
{
lean_object* v_a_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1649_; 
v_a_1636_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1649_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1649_ == 0)
{
v___x_1638_ = v___x_1635_;
v_isShared_1639_ = v_isSharedCheck_1649_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_a_1636_);
lean_dec(v___x_1635_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1649_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
lean_object* v_fst_1640_; 
v_fst_1640_ = lean_ctor_get(v_a_1636_, 0);
if (lean_obj_tag(v_fst_1640_) == 0)
{
lean_object* v_snd_1641_; lean_object* v___x_1643_; 
v_snd_1641_ = lean_ctor_get(v_a_1636_, 1);
lean_inc(v_snd_1641_);
lean_dec(v_a_1636_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v_snd_1641_);
v___x_1643_ = v___x_1638_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_snd_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
else
{
lean_object* v_val_1645_; lean_object* v___x_1647_; 
lean_inc_ref(v_fst_1640_);
lean_dec(v_a_1636_);
v_val_1645_ = lean_ctor_get(v_fst_1640_, 0);
lean_inc(v_val_1645_);
lean_dec_ref_known(v_fst_1640_, 1);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v_val_1645_);
v___x_1647_ = v___x_1638_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_val_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
else
{
lean_object* v_a_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1657_; 
v_a_1650_ = lean_ctor_get(v___x_1635_, 0);
v_isSharedCheck_1657_ = !lean_is_exclusive(v___x_1635_);
if (v_isSharedCheck_1657_ == 0)
{
v___x_1652_ = v___x_1635_;
v_isShared_1653_ = v_isSharedCheck_1657_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_a_1650_);
lean_dec(v___x_1635_);
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
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints___boxed(lean_object* v_p_1658_, lean_object* v_oldInlayHints_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1658_, v_oldInlayHints_1659_, v_a_1660_);
lean_dec_ref(v_a_1660_);
lean_dec_ref(v_oldInlayHints_1659_);
lean_dec_ref(v_p_1658_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(lean_object* v___x_1663_, lean_object* v___x_1664_, lean_object* v_as_1665_, size_t v_sz_1666_, size_t v_i_1667_, lean_object* v_b_1668_, lean_object* v___y_1669_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___redArg(v___x_1663_, v___x_1664_, v_as_1665_, v_sz_1666_, v_i_1667_, v_b_1668_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0___boxed(lean_object* v___x_1672_, lean_object* v___x_1673_, lean_object* v_as_1674_, lean_object* v_sz_1675_, lean_object* v_i_1676_, lean_object* v_b_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
size_t v_sz_boxed_1680_; size_t v_i_boxed_1681_; lean_object* v_res_1682_; 
v_sz_boxed_1680_ = lean_unbox_usize(v_sz_1675_);
lean_dec(v_sz_1675_);
v_i_boxed_1681_ = lean_unbox_usize(v_i_1676_);
lean_dec(v_i_1676_);
v_res_1682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints_spec__0(v___x_1672_, v___x_1673_, v_as_1674_, v_sz_boxed_1680_, v_i_boxed_1681_, v_b_1677_, v___y_1678_);
lean_dec_ref(v___y_1678_);
lean_dec_ref(v_as_1674_);
lean_dec_ref(v___x_1673_);
lean_dec_ref(v___x_1672_);
return v_res_1682_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(lean_object* v_a_1683_, lean_object* v_as_1684_, size_t v_i_1685_, size_t v_stop_1686_){
_start:
{
uint8_t v___x_1687_; 
v___x_1687_ = lean_usize_dec_eq(v_i_1685_, v_stop_1686_);
if (v___x_1687_ == 0)
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = lean_array_uget_borrowed(v_as_1684_, v_i_1685_);
v___x_1689_ = l_Lean_Elab_instBEqInlayHintTextEdit_beq(v_a_1683_, v___x_1688_);
if (v___x_1689_ == 0)
{
size_t v___x_1690_; size_t v___x_1691_; 
v___x_1690_ = ((size_t)1ULL);
v___x_1691_ = lean_usize_add(v_i_1685_, v___x_1690_);
v_i_1685_ = v___x_1691_;
goto _start;
}
else
{
return v___x_1689_;
}
}
else
{
uint8_t v___x_1693_; 
v___x_1693_ = 0;
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0___boxed(lean_object* v_a_1694_, lean_object* v_as_1695_, lean_object* v_i_1696_, lean_object* v_stop_1697_){
_start:
{
size_t v_i_boxed_1698_; size_t v_stop_boxed_1699_; uint8_t v_res_1700_; lean_object* v_r_1701_; 
v_i_boxed_1698_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_stop_boxed_1699_ = lean_unbox_usize(v_stop_1697_);
lean_dec(v_stop_1697_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1694_, v_as_1695_, v_i_boxed_1698_, v_stop_boxed_1699_);
lean_dec_ref(v_as_1695_);
lean_dec_ref(v_a_1694_);
v_r_1701_ = lean_box(v_res_1700_);
return v_r_1701_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(lean_object* v_as_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; uint8_t v___x_1706_; 
v___x_1704_ = lean_unsigned_to_nat(0u);
v___x_1705_ = lean_array_get_size(v_as_1702_);
v___x_1706_ = lean_nat_dec_lt(v___x_1704_, v___x_1705_);
if (v___x_1706_ == 0)
{
return v___x_1706_;
}
else
{
if (v___x_1706_ == 0)
{
return v___x_1706_;
}
else
{
size_t v___x_1707_; size_t v___x_1708_; uint8_t v___x_1709_; 
v___x_1707_ = ((size_t)0ULL);
v___x_1708_ = lean_usize_of_nat(v___x_1705_);
v___x_1709_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0_spec__0(v_a_1703_, v_as_1702_, v___x_1707_, v___x_1708_);
return v___x_1709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0___boxed(lean_object* v_as_1710_, lean_object* v_a_1711_){
_start:
{
uint8_t v_res_1712_; lean_object* v_r_1713_; 
v_res_1712_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_as_1710_, v_a_1711_);
lean_dec_ref(v_a_1711_);
lean_dec_ref(v_as_1710_);
v_r_1713_ = lean_box(v_res_1712_);
return v_r_1713_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(lean_object* v___x_1714_, lean_object* v_as_1715_, size_t v_i_1716_, size_t v_stop_1717_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = lean_usize_dec_eq(v_i_1716_, v_stop_1717_);
if (v___x_1718_ == 0)
{
lean_object* v___x_1719_; lean_object* v_textEdits_1720_; uint8_t v___x_1721_; 
v___x_1719_ = lean_array_uget_borrowed(v_as_1715_, v_i_1716_);
v_textEdits_1720_ = lean_ctor_get(v___x_1719_, 3);
v___x_1721_ = l_Array_contains___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__0(v_textEdits_1720_, v___x_1714_);
if (v___x_1721_ == 0)
{
size_t v___x_1722_; size_t v___x_1723_; 
v___x_1722_ = ((size_t)1ULL);
v___x_1723_ = lean_usize_add(v_i_1716_, v___x_1722_);
v_i_1716_ = v___x_1723_;
goto _start;
}
else
{
return v___x_1721_;
}
}
else
{
uint8_t v___x_1725_; 
v___x_1725_ = 0;
return v___x_1725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1___boxed(lean_object* v___x_1726_, lean_object* v_as_1727_, lean_object* v_i_1728_, lean_object* v_stop_1729_){
_start:
{
size_t v_i_boxed_1730_; size_t v_stop_boxed_1731_; uint8_t v_res_1732_; lean_object* v_r_1733_; 
v_i_boxed_1730_ = lean_unbox_usize(v_i_1728_);
lean_dec(v_i_1728_);
v_stop_boxed_1731_ = lean_unbox_usize(v_stop_1729_);
lean_dec(v_stop_1729_);
v_res_1732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1726_, v_as_1727_, v_i_boxed_1730_, v_stop_boxed_1731_);
lean_dec_ref(v_as_1727_);
lean_dec_ref(v___x_1726_);
v_r_1733_ = lean_box(v_res_1732_);
return v_r_1733_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(lean_object* v_oldInlayHints_1734_, lean_object* v___x_1735_, lean_object* v_as_1736_, size_t v_i_1737_, size_t v_stop_1738_){
_start:
{
uint8_t v___x_1739_; 
v___x_1739_ = lean_usize_dec_eq(v_i_1737_, v_stop_1738_);
if (v___x_1739_ == 0)
{
uint8_t v___x_1740_; uint8_t v___y_1742_; lean_object* v___x_1746_; 
v___x_1740_ = 1;
v___x_1746_ = lean_array_uget(v_as_1736_, v_i_1737_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_range_1747_; lean_object* v_text_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1765_; 
v_range_1747_ = lean_ctor_get(v___x_1746_, 0);
v_text_1748_ = lean_ctor_get(v___x_1746_, 1);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1746_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1750_ = v___x_1746_;
v_isShared_1751_ = v_isSharedCheck_1765_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_text_1748_);
lean_inc(v_range_1747_);
lean_dec(v___x_1746_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1765_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = lean_array_get_size(v_oldInlayHints_1734_);
v___x_1754_ = lean_nat_dec_lt(v___x_1752_, v___x_1753_);
if (v___x_1754_ == 0)
{
uint8_t v___x_1755_; 
lean_del_object(v___x_1750_);
lean_dec_ref(v_text_1748_);
lean_dec_ref(v_range_1747_);
v___x_1755_ = lean_bool_not(v___x_1739_);
v___y_1742_ = v___x_1755_;
goto v___jp_1741_;
}
else
{
if (v___x_1754_ == 0)
{
uint8_t v___x_1756_; 
lean_del_object(v___x_1750_);
lean_dec_ref(v_text_1748_);
lean_dec_ref(v_range_1747_);
v___x_1756_ = lean_bool_not(v___x_1739_);
v___y_1742_ = v___x_1756_;
goto v___jp_1741_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1759_; 
v___x_1757_ = l_Lean_FileMap_lspRangeToUtf8Range(v___x_1735_, v_range_1747_);
if (v_isShared_1751_ == 0)
{
lean_ctor_set(v___x_1750_, 0, v___x_1757_);
v___x_1759_ = v___x_1750_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_text_1748_);
v___x_1759_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
size_t v___x_1760_; size_t v___x_1761_; uint8_t v___x_1762_; uint8_t v___x_1763_; 
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = lean_usize_of_nat(v___x_1753_);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__1(v___x_1759_, v_oldInlayHints_1734_, v___x_1760_, v___x_1761_);
lean_dec_ref(v___x_1759_);
v___x_1763_ = lean_bool_not(v___x_1762_);
v___y_1742_ = v___x_1763_;
goto v___jp_1741_;
}
}
}
}
}
else
{
uint8_t v___x_1766_; 
lean_dec(v___x_1746_);
v___x_1766_ = lean_bool_not(v___x_1739_);
v___y_1742_ = v___x_1766_;
goto v___jp_1741_;
}
v___jp_1741_:
{
if (v___y_1742_ == 0)
{
size_t v___x_1743_; size_t v___x_1744_; 
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1737_, v___x_1743_);
v_i_1737_ = v___x_1744_;
goto _start;
}
else
{
return v___x_1740_;
}
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
v___x_1792_ = lean_bool_not(v___x_1791_);
v___y_1782_ = v___x_1792_;
goto v___jp_1781_;
}
else
{
if (v___x_1791_ == 0)
{
uint8_t v___x_1793_; 
v___x_1793_ = lean_bool_not(v___x_1791_);
v___y_1782_ = v___x_1793_;
goto v___jp_1781_;
}
else
{
lean_object* v_doc_1794_; lean_object* v_toEditableDocumentCore_1795_; lean_object* v_meta_1796_; lean_object* v_text_1797_; size_t v___x_1798_; size_t v___x_1799_; uint8_t v___x_1800_; uint8_t v___x_1801_; 
v_doc_1794_ = lean_ctor_get(v_a_1779_, 1);
v_toEditableDocumentCore_1795_ = lean_ctor_get(v_doc_1794_, 0);
v_meta_1796_ = lean_ctor_get(v_toEditableDocumentCore_1795_, 0);
v_text_1797_ = lean_ctor_get(v_meta_1796_, 3);
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = lean_usize_of_nat(v___x_1790_);
v___x_1800_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f_spec__2(v_oldInlayHints_1778_, v_text_1797_, v_contentChanges_1788_, v___x_1798_, v___x_1799_);
v___x_1801_ = lean_bool_not(v___x_1800_);
v___y_1782_ = v___x_1801_;
goto v___jp_1781_;
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
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f___boxed(lean_object* v_p_1802_, lean_object* v_oldInlayHints_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1802_, v_oldInlayHints_1803_, v_a_1804_);
lean_dec_ref(v_a_1804_);
lean_dec_ref(v_oldInlayHints_1803_);
lean_dec_ref(v_p_1802_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange(lean_object* v_p_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v_oldInlayHints_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1841_; 
v_oldInlayHints_1811_ = lean_ctor_get(v_a_1808_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_a_1808_);
if (v_isSharedCheck_1841_ == 0)
{
lean_object* v_unused_1842_; lean_object* v_unused_1843_; 
v_unused_1842_ = lean_ctor_get(v_a_1808_, 2);
lean_dec(v_unused_1842_);
v_unused_1843_ = lean_ctor_get(v_a_1808_, 1);
lean_dec(v_unused_1843_);
v___x_1813_ = v_a_1808_;
v_isShared_1814_ = v_isSharedCheck_1841_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_oldInlayHints_1811_);
lean_dec(v_a_1808_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1841_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; 
v___x_1815_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_updateOldInlayHints(v_p_1807_, v_oldInlayHints_1811_, v_a_1809_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1817_; lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1832_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
lean_inc(v_a_1816_);
lean_dec_ref_known(v___x_1815_, 1);
v___x_1817_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_handleInlayHintsDidChange_determineLastEditTimestamp_x3f(v_p_1807_, v_oldInlayHints_1811_, v_a_1809_);
lean_dec_ref(v_oldInlayHints_1811_);
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1832_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1832_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1832_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1832_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; uint8_t v___x_1823_; lean_object* v___x_1825_; 
v___x_1822_ = lean_unsigned_to_nat(0u);
v___x_1823_ = 1;
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 2, v_a_1818_);
lean_ctor_set(v___x_1813_, 1, v___x_1822_);
lean_ctor_set(v___x_1813_, 0, v_a_1816_);
v___x_1825_ = v___x_1813_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1831_; 
v_reuseFailAlloc_1831_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1831_, 0, v_a_1816_);
lean_ctor_set(v_reuseFailAlloc_1831_, 1, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1831_, 2, v_a_1818_);
v___x_1825_ = v_reuseFailAlloc_1831_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_ctor_set_uint8(v___x_1825_, sizeof(void*)*3, v___x_1823_);
v___x_1826_ = lean_box(0);
v___x_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v___x_1825_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1827_);
v___x_1829_ = v___x_1820_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1840_; 
lean_del_object(v___x_1813_);
lean_dec_ref(v_oldInlayHints_1811_);
v_a_1833_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1835_ = v___x_1815_;
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1815_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1840_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1838_; 
if (v_isShared_1836_ == 0)
{
v___x_1838_ = v___x_1835_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_a_1833_);
v___x_1838_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
return v___x_1838_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_handleInlayHintsDidChange___boxed(lean_object* v_p_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Lean_Server_FileWorker_handleInlayHintsDidChange(v_p_1844_, v_a_1845_, v_a_1846_);
lean_dec_ref(v_a_1846_);
lean_dec_ref(v_p_1844_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(lean_object* v___x_1849_, lean_object* v_x_1850_){
_start:
{
return v___x_1849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3___boxed(lean_object* v___x_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__3(v___x_1851_, v_x_1852_);
lean_dec_ref(v_x_1852_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_, lean_object* v_x_1857_){
_start:
{
lean_object* v_ks_1858_; lean_object* v_vs_1859_; lean_object* v___x_1861_; uint8_t v_isShared_1862_; uint8_t v_isSharedCheck_1883_; 
v_ks_1858_ = lean_ctor_get(v_x_1854_, 0);
v_vs_1859_ = lean_ctor_get(v_x_1854_, 1);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_x_1854_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1861_ = v_x_1854_;
v_isShared_1862_ = v_isSharedCheck_1883_;
goto v_resetjp_1860_;
}
else
{
lean_inc(v_vs_1859_);
lean_inc(v_ks_1858_);
lean_dec(v_x_1854_);
v___x_1861_ = lean_box(0);
v_isShared_1862_ = v_isSharedCheck_1883_;
goto v_resetjp_1860_;
}
v_resetjp_1860_:
{
lean_object* v___x_1863_; uint8_t v___x_1864_; 
v___x_1863_ = lean_array_get_size(v_ks_1858_);
v___x_1864_ = lean_nat_dec_lt(v_x_1855_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1868_; 
lean_dec(v_x_1855_);
v___x_1865_ = lean_array_push(v_ks_1858_, v_x_1856_);
v___x_1866_ = lean_array_push(v_vs_1859_, v_x_1857_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v___x_1866_);
lean_ctor_set(v___x_1861_, 0, v___x_1865_);
v___x_1868_ = v___x_1861_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
else
{
lean_object* v_k_x27_1870_; uint8_t v___x_1871_; 
v_k_x27_1870_ = lean_array_fget_borrowed(v_ks_1858_, v_x_1855_);
v___x_1871_ = lean_string_dec_eq(v_x_1856_, v_k_x27_1870_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1873_; 
if (v_isShared_1862_ == 0)
{
v___x_1873_ = v___x_1861_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_ks_1858_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_vs_1859_);
v___x_1873_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1874_ = lean_unsigned_to_nat(1u);
v___x_1875_ = lean_nat_add(v_x_1855_, v___x_1874_);
lean_dec(v_x_1855_);
v_x_1854_ = v___x_1873_;
v_x_1855_ = v___x_1875_;
goto _start;
}
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1878_ = lean_array_fset(v_ks_1858_, v_x_1855_, v_x_1856_);
v___x_1879_ = lean_array_fset(v_vs_1859_, v_x_1855_, v_x_1857_);
lean_dec(v_x_1855_);
if (v_isShared_1862_ == 0)
{
lean_ctor_set(v___x_1861_, 1, v___x_1879_);
lean_ctor_set(v___x_1861_, 0, v___x_1878_);
v___x_1881_ = v___x_1861_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1878_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v___x_1879_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
return v___x_1881_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(lean_object* v_n_1884_, lean_object* v_k_1885_, lean_object* v_v_1886_){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_unsigned_to_nat(0u);
v___x_1888_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_n_1884_, v___x_1887_, v_k_1885_, v_v_1886_);
return v___x_1888_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(lean_object* v_x_1890_, size_t v_x_1891_, size_t v_x_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
if (lean_obj_tag(v_x_1890_) == 0)
{
lean_object* v_es_1895_; size_t v___x_1896_; size_t v___x_1897_; lean_object* v_j_1898_; lean_object* v___x_1899_; uint8_t v___x_1900_; 
v_es_1895_ = lean_ctor_get(v_x_1890_, 0);
v___x_1896_ = ((size_t)31ULL);
v___x_1897_ = lean_usize_land(v_x_1891_, v___x_1896_);
v_j_1898_ = lean_usize_to_nat(v___x_1897_);
v___x_1899_ = lean_array_get_size(v_es_1895_);
v___x_1900_ = lean_nat_dec_lt(v_j_1898_, v___x_1899_);
if (v___x_1900_ == 0)
{
lean_dec(v_j_1898_);
lean_dec(v_x_1894_);
lean_dec_ref(v_x_1893_);
return v_x_1890_;
}
else
{
lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1939_; 
lean_inc_ref(v_es_1895_);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_x_1890_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v_x_1890_, 0);
lean_dec(v_unused_1940_);
v___x_1902_ = v_x_1890_;
v_isShared_1903_ = v_isSharedCheck_1939_;
goto v_resetjp_1901_;
}
else
{
lean_dec(v_x_1890_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1939_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
lean_object* v_v_1904_; lean_object* v___x_1905_; lean_object* v_xs_x27_1906_; lean_object* v___y_1908_; 
v_v_1904_ = lean_array_fget(v_es_1895_, v_j_1898_);
v___x_1905_ = lean_box(0);
v_xs_x27_1906_ = lean_array_fset(v_es_1895_, v_j_1898_, v___x_1905_);
switch(lean_obj_tag(v_v_1904_))
{
case 0:
{
lean_object* v_key_1913_; lean_object* v_val_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1924_; 
v_key_1913_ = lean_ctor_get(v_v_1904_, 0);
v_val_1914_ = lean_ctor_get(v_v_1904_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_v_1904_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1916_ = v_v_1904_;
v_isShared_1917_ = v_isSharedCheck_1924_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_val_1914_);
lean_inc(v_key_1913_);
lean_dec(v_v_1904_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1924_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
uint8_t v___x_1918_; 
v___x_1918_ = lean_string_dec_eq(v_x_1893_, v_key_1913_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_del_object(v___x_1916_);
v___x_1919_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1913_, v_val_1914_, v_x_1893_, v_x_1894_);
v___x_1920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
v___y_1908_ = v___x_1920_;
goto v___jp_1907_;
}
else
{
lean_object* v___x_1922_; 
lean_dec(v_val_1914_);
lean_dec(v_key_1913_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v_x_1894_);
lean_ctor_set(v___x_1916_, 0, v_x_1893_);
v___x_1922_ = v___x_1916_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_x_1893_);
lean_ctor_set(v_reuseFailAlloc_1923_, 1, v_x_1894_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
v___y_1908_ = v___x_1922_;
goto v___jp_1907_;
}
}
}
}
case 1:
{
lean_object* v_node_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1937_; 
v_node_1925_ = lean_ctor_get(v_v_1904_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_v_1904_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1927_ = v_v_1904_;
v_isShared_1928_ = v_isSharedCheck_1937_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_node_1925_);
lean_dec(v_v_1904_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1937_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
size_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1929_ = ((size_t)5ULL);
v___x_1930_ = lean_usize_shift_right(v_x_1891_, v___x_1929_);
v___x_1931_ = ((size_t)1ULL);
v___x_1932_ = lean_usize_add(v_x_1892_, v___x_1931_);
v___x_1933_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_node_1925_, v___x_1930_, v___x_1932_, v_x_1893_, v_x_1894_);
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 0, v___x_1933_);
v___x_1935_ = v___x_1927_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
v___y_1908_ = v___x_1935_;
goto v___jp_1907_;
}
}
}
default: 
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1938_, 0, v_x_1893_);
lean_ctor_set(v___x_1938_, 1, v_x_1894_);
v___y_1908_ = v___x_1938_;
goto v___jp_1907_;
}
}
v___jp_1907_:
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = lean_array_fset(v_xs_x27_1906_, v_j_1898_, v___y_1908_);
lean_dec(v_j_1898_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1909_);
v___x_1911_ = v___x_1902_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
else
{
lean_object* v_ks_1941_; lean_object* v_vs_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1962_; 
v_ks_1941_ = lean_ctor_get(v_x_1890_, 0);
v_vs_1942_ = lean_ctor_get(v_x_1890_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_x_1890_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1944_ = v_x_1890_;
v_isShared_1945_ = v_isSharedCheck_1962_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_vs_1942_);
lean_inc(v_ks_1941_);
lean_dec(v_x_1890_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1962_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_ks_1941_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_vs_1942_);
v___x_1947_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
lean_object* v_newNode_1948_; uint8_t v___y_1950_; size_t v___x_1956_; uint8_t v___x_1957_; 
v_newNode_1948_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v___x_1947_, v_x_1893_, v_x_1894_);
v___x_1956_ = ((size_t)7ULL);
v___x_1957_ = lean_usize_dec_le(v___x_1956_, v_x_1892_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1948_);
v___x_1959_ = lean_unsigned_to_nat(4u);
v___x_1960_ = lean_nat_dec_lt(v___x_1958_, v___x_1959_);
lean_dec(v___x_1958_);
v___y_1950_ = v___x_1960_;
goto v___jp_1949_;
}
else
{
v___y_1950_ = v___x_1957_;
goto v___jp_1949_;
}
v___jp_1949_:
{
if (v___y_1950_ == 0)
{
lean_object* v_ks_1951_; lean_object* v_vs_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; 
v_ks_1951_ = lean_ctor_get(v_newNode_1948_, 0);
lean_inc_ref(v_ks_1951_);
v_vs_1952_ = lean_ctor_get(v_newNode_1948_, 1);
lean_inc_ref(v_vs_1952_);
lean_dec_ref(v_newNode_1948_);
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_1954_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___closed__0);
v___x_1955_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_x_1892_, v_ks_1951_, v_vs_1952_, v___x_1953_, v___x_1954_);
lean_dec_ref(v_vs_1952_);
lean_dec_ref(v_ks_1951_);
return v___x_1955_;
}
else
{
return v_newNode_1948_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(size_t v_depth_1963_, lean_object* v_keys_1964_, lean_object* v_vals_1965_, lean_object* v_i_1966_, lean_object* v_entries_1967_){
_start:
{
lean_object* v___x_1968_; uint8_t v___x_1969_; 
v___x_1968_ = lean_array_get_size(v_keys_1964_);
v___x_1969_ = lean_nat_dec_lt(v_i_1966_, v___x_1968_);
if (v___x_1969_ == 0)
{
lean_dec(v_i_1966_);
return v_entries_1967_;
}
else
{
lean_object* v_k_1970_; lean_object* v_v_1971_; uint64_t v___x_1972_; size_t v_h_1973_; size_t v___x_1974_; lean_object* v___x_1975_; size_t v___x_1976_; size_t v___x_1977_; size_t v___x_1978_; size_t v_h_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_k_1970_ = lean_array_fget_borrowed(v_keys_1964_, v_i_1966_);
v_v_1971_ = lean_array_fget_borrowed(v_vals_1965_, v_i_1966_);
v___x_1972_ = lean_string_hash(v_k_1970_);
v_h_1973_ = lean_uint64_to_usize(v___x_1972_);
v___x_1974_ = ((size_t)5ULL);
v___x_1975_ = lean_unsigned_to_nat(1u);
v___x_1976_ = ((size_t)1ULL);
v___x_1977_ = lean_usize_sub(v_depth_1963_, v___x_1976_);
v___x_1978_ = lean_usize_mul(v___x_1974_, v___x_1977_);
v_h_1979_ = lean_usize_shift_right(v_h_1973_, v___x_1978_);
v___x_1980_ = lean_nat_add(v_i_1966_, v___x_1975_);
lean_dec(v_i_1966_);
lean_inc(v_v_1971_);
lean_inc(v_k_1970_);
v___x_1981_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_entries_1967_, v_h_1979_, v_depth_1963_, v_k_1970_, v_v_1971_);
v_i_1966_ = v___x_1980_;
v_entries_1967_ = v___x_1981_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg___boxed(lean_object* v_depth_1983_, lean_object* v_keys_1984_, lean_object* v_vals_1985_, lean_object* v_i_1986_, lean_object* v_entries_1987_){
_start:
{
size_t v_depth_boxed_1988_; lean_object* v_res_1989_; 
v_depth_boxed_1988_ = lean_unbox_usize(v_depth_1983_);
lean_dec(v_depth_1983_);
v_res_1989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_boxed_1988_, v_keys_1984_, v_vals_1985_, v_i_1986_, v_entries_1987_);
lean_dec_ref(v_vals_1985_);
lean_dec_ref(v_keys_1984_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg___boxed(lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_){
_start:
{
size_t v_x_2355__boxed_1995_; size_t v_x_2356__boxed_1996_; lean_object* v_res_1997_; 
v_x_2355__boxed_1995_ = lean_unbox_usize(v_x_1991_);
lean_dec(v_x_1991_);
v_x_2356__boxed_1996_ = lean_unbox_usize(v_x_1992_);
lean_dec(v_x_1992_);
v_res_1997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_1990_, v_x_2355__boxed_1995_, v_x_2356__boxed_1996_, v_x_1993_, v_x_1994_);
return v_res_1997_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(lean_object* v_x_1998_, lean_object* v_x_1999_, lean_object* v_x_2000_){
_start:
{
uint64_t v___x_2001_; size_t v___x_2002_; size_t v___x_2003_; lean_object* v___x_2004_; 
v___x_2001_ = lean_string_hash(v_x_1999_);
v___x_2002_ = lean_uint64_to_usize(v___x_2001_);
v___x_2003_ = ((size_t)1ULL);
v___x_2004_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_1998_, v___x_2002_, v___x_2003_, v_x_1999_, v_x_2000_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(lean_object* v_mutex_2005_, lean_object* v_a_x3f_2006_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2008_ = lean_io_basemutex_unlock(v_mutex_2005_);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0___boxed(lean_object* v_mutex_2010_, lean_object* v_a_x3f_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2010_, v_a_x3f_2011_);
lean_dec(v_a_x3f_2011_);
lean_dec(v_mutex_2010_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_mutex_2014_, lean_object* v_k_2015_, lean_object* v___y_2016_){
_start:
{
lean_object* v_ref_2018_; lean_object* v_mutex_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v_ref_2018_ = lean_ctor_get(v_mutex_2014_, 0);
lean_inc(v_ref_2018_);
v_mutex_2019_ = lean_ctor_get(v_mutex_2014_, 1);
lean_inc(v_mutex_2019_);
lean_dec_ref(v_mutex_2014_);
v___x_2020_ = lean_io_basemutex_lock(v_mutex_2019_);
lean_inc_ref(v___y_2016_);
v___x_2021_ = lean_apply_3(v_k_2015_, v_ref_2018_, v___y_2016_, lean_box(0));
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2038_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2038_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2038_ == 0)
{
v___x_2024_ = v___x_2021_;
v_isShared_2025_ = v_isSharedCheck_2038_;
goto v_resetjp_2023_;
}
else
{
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2038_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2027_; 
lean_inc(v_a_2022_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set_tag(v___x_2024_, 1);
v___x_2027_ = v___x_2024_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2037_; 
v_reuseFailAlloc_2037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2037_, 0, v_a_2022_);
v___x_2027_ = v_reuseFailAlloc_2037_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
v___x_2028_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2019_, v___x_2027_);
lean_dec_ref(v___x_2027_);
lean_dec(v_mutex_2019_);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v___x_2028_, 0);
lean_dec(v_unused_2036_);
v___x_2030_ = v___x_2028_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_dec(v___x_2028_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v_a_2022_);
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2022_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
else
{
lean_object* v_a_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
v_a_2039_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2040_ = lean_box(0);
v___x_2041_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___lam__0(v_mutex_2019_, v___x_2040_);
lean_dec(v_mutex_2019_);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; 
v_unused_2049_ = lean_ctor_get(v___x_2041_, 0);
lean_dec(v_unused_2049_);
v___x_2043_ = v___x_2041_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_dec(v___x_2041_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set_tag(v___x_2043_, 1);
lean_ctor_set(v___x_2043_, 0, v_a_2039_);
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2039_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_mutex_2050_, lean_object* v_k_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2050_, v_k_2051_, v___y_2052_);
lean_dec_ref(v___y_2052_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(lean_object* v_val_2055_, lean_object* v___f_2056_, lean_object* v_param_2057_, lean_object* v_x_2058_, lean_object* v___y_2059_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2061_ = lean_st_ref_get(v_val_2055_);
lean_inc_ref(v___y_2059_);
v___x_2062_ = lean_apply_4(v___f_2056_, v_param_2057_, v___x_2061_, v___y_2059_, lean_box(0));
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2072_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2065_ = v___x_2062_;
v_isShared_2066_ = v_isSharedCheck_2072_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2062_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2072_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v_snd_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
v_snd_2067_ = lean_ctor_get(v_a_2063_, 1);
lean_inc(v_snd_2067_);
lean_dec(v_a_2063_);
v___x_2068_ = lean_st_ref_set(v_val_2055_, v_snd_2067_);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 0, v___x_2068_);
v___x_2070_ = v___x_2065_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v___x_2068_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
v_a_2073_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2062_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2062_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed(lean_object* v_val_2081_, lean_object* v___f_2082_, lean_object* v_param_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8(v_val_2081_, v___f_2082_, v_param_2083_, v_x_2084_, v___y_2085_);
lean_dec_ref(v___y_2085_);
lean_dec(v_val_2081_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(lean_object* v___f_2088_, lean_object* v___f_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2093_ = lean_st_ref_get(v___y_2090_);
v___x_2094_ = l_Lean_Server_RequestM_mapTaskCostly___redArg(v___x_2093_, v___f_2088_, v___y_2091_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2104_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2097_ = v___x_2094_;
v_isShared_2098_ = v_isSharedCheck_2104_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_a_2095_);
lean_dec(v___x_2094_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2104_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2099_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_2089_, v_a_2095_);
v___x_2100_ = lean_st_ref_set(v___y_2090_, v___x_2099_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 0, v___x_2100_);
v___x_2102_ = v___x_2097_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
lean_dec_ref(v___f_2089_);
v_a_2105_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2094_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2094_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed(lean_object* v___f_2113_, lean_object* v___f_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9(v___f_2113_, v___f_2114_, v___y_2115_, v___y_2116_);
lean_dec_ref(v___y_2116_);
lean_dec(v___y_2115_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(lean_object* v_val_2119_, lean_object* v___f_2120_, lean_object* v___f_2121_, lean_object* v_val_2122_, lean_object* v_param_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___f_2126_; lean_object* v___f_2127_; lean_object* v___x_2128_; 
v___f_2126_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__8___boxed), 6, 3);
lean_closure_set(v___f_2126_, 0, v_val_2119_);
lean_closure_set(v___f_2126_, 1, v___f_2120_);
lean_closure_set(v___f_2126_, 2, v_param_2123_);
v___f_2127_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__9___boxed), 5, 2);
lean_closure_set(v___f_2127_, 0, v___f_2126_);
lean_closure_set(v___f_2127_, 1, v___f_2121_);
v___x_2128_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_val_2122_, v___f_2127_, v___y_2124_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed(lean_object* v_val_2129_, lean_object* v___f_2130_, lean_object* v___f_2131_, lean_object* v_val_2132_, lean_object* v_param_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10(v_val_2129_, v___f_2130_, v___f_2131_, v_val_2132_, v_param_2133_, v___y_2134_);
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
v___x_2367_ = lean_st_ref_set(v___y_2357_, v___x_2366_);
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
v___x_2392_ = lean_st_ref_set(v_val_2378_, v_snd_2391_);
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
static lean_object* _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_box(0);
v___x_2431_ = lean_task_pure(v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_method_2439_, lean_object* v_completeness_2440_, lean_object* v_inst_2441_, lean_object* v_initState_2442_, lean_object* v_handler_2443_, lean_object* v_onDidChange_2444_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_Lean_initializing();
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2480_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2480_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2480_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
uint8_t v___x_2451_; uint8_t v___x_2452_; 
v___x_2451_ = lean_unbox(v_a_2447_);
lean_dec(v_a_2447_);
v___x_2452_ = lean_bool_not(v___x_2451_);
if (v___x_2452_ == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___f_2459_; lean_object* v___f_2460_; lean_object* v___f_2461_; lean_object* v___f_2462_; lean_object* v___f_2463_; lean_object* v___f_2464_; lean_object* v___f_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2470_; 
v___x_2453_ = lean_obj_once(&l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__0);
v___x_2454_ = l_Std_Mutex_new___redArg(v___x_2453_);
lean_inc_n(v_inst_2441_, 2);
v___x_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2455_, 0, v_inst_2441_);
lean_ctor_set(v___x_2455_, 1, v_initState_2442_);
lean_inc_ref(v___x_2455_);
v___x_2456_ = lean_st_mk_ref(v___x_2455_);
v___x_2457_ = l_Lean_Server_statefulRequestHandlers;
v___x_2458_ = lean_st_ref_take(v___x_2457_);
v___f_2459_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__1));
lean_inc_ref_n(v_method_2439_, 2);
v___f_2460_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__1___boxed), 7, 3);
lean_closure_set(v___f_2460_, 0, v_method_2439_);
lean_closure_set(v___f_2460_, 1, v_inst_2441_);
lean_closure_set(v___f_2460_, 2, v_handler_2443_);
v___f_2461_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__2___boxed), 7, 3);
lean_closure_set(v___f_2461_, 0, v_method_2439_);
lean_closure_set(v___f_2461_, 1, v_inst_2441_);
lean_closure_set(v___f_2461_, 2, v_onDidChange_2444_);
v___f_2462_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__2));
v___f_2463_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__3));
lean_inc_ref_n(v___x_2454_, 2);
lean_inc_ref(v___f_2460_);
lean_inc_n(v___x_2456_, 2);
v___f_2464_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__7___boxed), 7, 4);
lean_closure_set(v___f_2464_, 0, v___x_2456_);
lean_closure_set(v___f_2464_, 1, v___f_2460_);
lean_closure_set(v___f_2464_, 2, v___f_2462_);
lean_closure_set(v___f_2464_, 3, v___x_2454_);
lean_inc_ref(v___f_2461_);
v___f_2465_ = lean_alloc_closure((void*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___lam__10___boxed), 7, 4);
lean_closure_set(v___f_2465_, 0, v___x_2456_);
lean_closure_set(v___f_2465_, 1, v___f_2461_);
lean_closure_set(v___f_2465_, 2, v___f_2463_);
lean_closure_set(v___f_2465_, 3, v___x_2454_);
v___x_2466_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_2466_, 0, v___f_2459_);
lean_ctor_set(v___x_2466_, 1, v___f_2460_);
lean_ctor_set(v___x_2466_, 2, v___f_2464_);
lean_ctor_set(v___x_2466_, 3, v___f_2461_);
lean_ctor_set(v___x_2466_, 4, v___f_2465_);
lean_ctor_set(v___x_2466_, 5, v___x_2454_);
lean_ctor_set(v___x_2466_, 6, v___x_2455_);
lean_ctor_set(v___x_2466_, 7, v___x_2456_);
lean_ctor_set(v___x_2466_, 8, v_completeness_2440_);
v___x_2467_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v___x_2458_, v_method_2439_, v___x_2466_);
v___x_2468_ = lean_st_ref_set(v___x_2457_, v___x_2467_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2468_);
v___x_2470_ = v___x_2449_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v___x_2468_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2478_; 
lean_dec_ref(v_onDidChange_2444_);
lean_dec_ref(v_handler_2443_);
lean_dec(v_initState_2442_);
lean_dec(v_inst_2441_);
lean_dec(v_completeness_2440_);
v___x_2472_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4));
v___x_2473_ = lean_string_append(v___x_2472_, v_method_2439_);
lean_dec_ref(v_method_2439_);
v___x_2474_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__5));
v___x_2475_ = lean_string_append(v___x_2473_, v___x_2474_);
v___x_2476_ = lean_mk_io_user_error(v___x_2475_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set_tag(v___x_2449_, 1);
lean_ctor_set(v___x_2449_, 0, v___x_2476_);
v___x_2478_ = v___x_2449_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2476_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v_onDidChange_2444_);
lean_dec_ref(v_handler_2443_);
lean_dec(v_initState_2442_);
lean_dec(v_inst_2441_);
lean_dec(v_completeness_2440_);
lean_dec_ref(v_method_2439_);
v_a_2481_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2446_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2446_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_method_2489_, lean_object* v_completeness_2490_, lean_object* v_inst_2491_, lean_object* v_initState_2492_, lean_object* v_handler_2493_, lean_object* v_onDidChange_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2489_, v_completeness_2490_, v_inst_2491_, v_initState_2492_, v_handler_2493_, v_onDidChange_2494_);
return v_res_2496_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_keys_2497_, lean_object* v_i_2498_, lean_object* v_k_2499_){
_start:
{
lean_object* v___x_2500_; uint8_t v___x_2501_; 
v___x_2500_ = lean_array_get_size(v_keys_2497_);
v___x_2501_ = lean_nat_dec_lt(v_i_2498_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_dec(v_i_2498_);
return v___x_2501_;
}
else
{
lean_object* v_k_x27_2502_; uint8_t v___x_2503_; 
v_k_x27_2502_ = lean_array_fget_borrowed(v_keys_2497_, v_i_2498_);
v___x_2503_ = lean_string_dec_eq(v_k_2499_, v_k_x27_2502_);
if (v___x_2503_ == 0)
{
lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2504_ = lean_unsigned_to_nat(1u);
v___x_2505_ = lean_nat_add(v_i_2498_, v___x_2504_);
lean_dec(v_i_2498_);
v_i_2498_ = v___x_2505_;
goto _start;
}
else
{
lean_dec(v_i_2498_);
return v___x_2503_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_keys_2507_, lean_object* v_i_2508_, lean_object* v_k_2509_){
_start:
{
uint8_t v_res_2510_; lean_object* v_r_2511_; 
v_res_2510_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2507_, v_i_2508_, v_k_2509_);
lean_dec_ref(v_k_2509_);
lean_dec_ref(v_keys_2507_);
v_r_2511_ = lean_box(v_res_2510_);
return v_r_2511_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_2512_, size_t v_x_2513_, lean_object* v_x_2514_){
_start:
{
if (lean_obj_tag(v_x_2512_) == 0)
{
lean_object* v_es_2515_; lean_object* v___x_2516_; size_t v___x_2517_; size_t v___x_2518_; lean_object* v_j_2519_; lean_object* v___x_2520_; 
v_es_2515_ = lean_ctor_get(v_x_2512_, 0);
v___x_2516_ = lean_box(2);
v___x_2517_ = ((size_t)31ULL);
v___x_2518_ = lean_usize_land(v_x_2513_, v___x_2517_);
v_j_2519_ = lean_usize_to_nat(v___x_2518_);
v___x_2520_ = lean_array_get_borrowed(v___x_2516_, v_es_2515_, v_j_2519_);
lean_dec(v_j_2519_);
switch(lean_obj_tag(v___x_2520_))
{
case 0:
{
lean_object* v_key_2521_; uint8_t v___x_2522_; 
v_key_2521_ = lean_ctor_get(v___x_2520_, 0);
v___x_2522_ = lean_string_dec_eq(v_x_2514_, v_key_2521_);
return v___x_2522_;
}
case 1:
{
lean_object* v_node_2523_; size_t v___x_2524_; size_t v___x_2525_; 
v_node_2523_ = lean_ctor_get(v___x_2520_, 0);
v___x_2524_ = ((size_t)5ULL);
v___x_2525_ = lean_usize_shift_right(v_x_2513_, v___x_2524_);
v_x_2512_ = v_node_2523_;
v_x_2513_ = v___x_2525_;
goto _start;
}
default: 
{
uint8_t v___x_2527_; 
v___x_2527_ = 0;
return v___x_2527_;
}
}
}
else
{
lean_object* v_ks_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_ks_2528_ = lean_ctor_get(v_x_2512_, 0);
v___x_2529_ = lean_unsigned_to_nat(0u);
v___x_2530_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_ks_2528_, v___x_2529_, v_x_2514_);
return v___x_2530_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_x_2531_, lean_object* v_x_2532_, lean_object* v_x_2533_){
_start:
{
size_t v_x_3342__boxed_2534_; uint8_t v_res_2535_; lean_object* v_r_2536_; 
v_x_3342__boxed_2534_ = lean_unbox_usize(v_x_2532_);
lean_dec(v_x_2532_);
v_res_2535_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2531_, v_x_3342__boxed_2534_, v_x_2533_);
lean_dec_ref(v_x_2533_);
lean_dec_ref(v_x_2531_);
v_r_2536_ = lean_box(v_res_2535_);
return v_r_2536_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
uint64_t v___x_2539_; size_t v___x_2540_; uint8_t v___x_2541_; 
v___x_2539_ = lean_string_hash(v_x_2538_);
v___x_2540_ = lean_uint64_to_usize(v___x_2539_);
v___x_2541_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2537_, v___x_2540_, v_x_2538_);
return v___x_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_2542_, lean_object* v_x_2543_){
_start:
{
uint8_t v_res_2544_; lean_object* v_r_2545_; 
v_res_2544_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2542_, v_x_2543_);
lean_dec_ref(v_x_2543_);
lean_dec_ref(v_x_2542_);
v_r_2545_ = lean_box(v_res_2544_);
return v_r_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_method_2547_, lean_object* v_completeness_2548_, lean_object* v_inst_2549_, lean_object* v_initState_2550_, lean_object* v_handler_2551_, lean_object* v_onDidChange_2552_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v___x_2554_ = l_Lean_Server_requestHandlers;
v___x_2555_ = lean_st_ref_get(v___x_2554_);
v___x_2556_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___x_2555_, v_method_2547_);
lean_dec(v___x_2555_);
if (v___x_2556_ == 0)
{
lean_object* v___x_2557_; 
v___x_2557_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2547_, v_completeness_2548_, v_inst_2549_, v_initState_2550_, v_handler_2551_, v_onDidChange_2552_);
return v___x_2557_;
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec_ref(v_onDidChange_2552_);
lean_dec_ref(v_handler_2551_);
lean_dec(v_initState_2550_);
lean_dec(v_inst_2549_);
lean_dec(v_completeness_2548_);
v___x_2558_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg___closed__4));
v___x_2559_ = lean_string_append(v___x_2558_, v_method_2547_);
lean_dec_ref(v_method_2547_);
v___x_2560_ = ((lean_object*)(l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0));
v___x_2561_ = lean_string_append(v___x_2559_, v___x_2560_);
v___x_2562_ = lean_mk_io_user_error(v___x_2561_);
v___x_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2562_);
return v___x_2563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_method_2564_, lean_object* v_completeness_2565_, lean_object* v_inst_2566_, lean_object* v_initState_2567_, lean_object* v_handler_2568_, lean_object* v_onDidChange_2569_, lean_object* v_a_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2564_, v_completeness_2565_, v_inst_2566_, v_initState_2567_, v_handler_2568_, v_onDidChange_2569_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(lean_object* v_method_2572_, lean_object* v_refreshMethod_2573_, lean_object* v_refreshIntervalMs_2574_, lean_object* v_inst_2575_, lean_object* v_initState_2576_, lean_object* v_handler_2577_, lean_object* v_onDidChange_2578_){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_refreshMethod_2573_);
lean_ctor_set(v___x_2580_, 1, v_refreshIntervalMs_2574_);
v___x_2581_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2572_, v___x_2580_, v_inst_2575_, v_initState_2576_, v_handler_2577_, v_onDidChange_2578_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_method_2582_, lean_object* v_refreshMethod_2583_, lean_object* v_refreshIntervalMs_2584_, lean_object* v_inst_2585_, lean_object* v_initState_2586_, lean_object* v_handler_2587_, lean_object* v_onDidChange_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v_res_2590_; 
v_res_2590_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2582_, v_refreshMethod_2583_, v_refreshIntervalMs_2584_, v_inst_2585_, v_initState_2586_, v_handler_2587_, v_onDidChange_2588_);
return v_res_2590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2596_ = ((lean_object*)(l_Lean_Server_FileWorker_instImpl_00___x40_Lean_Server_FileWorker_InlayHints_3310298766____hygCtx___hyg_16_));
v___x_2597_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__0_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2598_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__1_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2599_ = lean_unsigned_to_nat(500u);
v___x_2600_ = ((lean_object*)(l_Lean_Server_FileWorker_InlayHintState_init));
v___x_2601_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__2_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2602_ = ((lean_object*)(l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn___closed__3_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_));
v___x_2603_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v___x_2597_, v___x_2598_, v___x_2599_, v___x_2596_, v___x_2600_, v___x_2601_, v___x_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2____boxed(lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l___private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2_();
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(lean_object* v_method_2606_, lean_object* v_refreshMethod_2607_, lean_object* v_refreshIntervalMs_2608_, lean_object* v_stateType_2609_, lean_object* v_inst_2610_, lean_object* v_initState_2611_, lean_object* v_handler_2612_, lean_object* v_onDidChange_2613_){
_start:
{
lean_object* v___x_2615_; 
v___x_2615_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___redArg(v_method_2606_, v_refreshMethod_2607_, v_refreshIntervalMs_2608_, v_inst_2610_, v_initState_2611_, v_handler_2612_, v_onDidChange_2613_);
return v___x_2615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0___boxed(lean_object* v_method_2616_, lean_object* v_refreshMethod_2617_, lean_object* v_refreshIntervalMs_2618_, lean_object* v_stateType_2619_, lean_object* v_inst_2620_, lean_object* v_initState_2621_, lean_object* v_handler_2622_, lean_object* v_onDidChange_2623_, lean_object* v_a_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0(v_method_2616_, v_refreshMethod_2617_, v_refreshIntervalMs_2618_, v_stateType_2619_, v_inst_2620_, v_initState_2621_, v_handler_2622_, v_onDidChange_2623_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_method_2626_, lean_object* v_completeness_2627_, lean_object* v_stateType_2628_, lean_object* v_inst_2629_, lean_object* v_initState_2630_, lean_object* v_handler_2631_, lean_object* v_onDidChange_2632_){
_start:
{
lean_object* v___x_2634_; 
v___x_2634_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___redArg(v_method_2626_, v_completeness_2627_, v_inst_2629_, v_initState_2630_, v_handler_2631_, v_onDidChange_2632_);
return v___x_2634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_method_2635_, lean_object* v_completeness_2636_, lean_object* v_stateType_2637_, lean_object* v_inst_2638_, lean_object* v_initState_2639_, lean_object* v_handler_2640_, lean_object* v_onDidChange_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0(v_method_2635_, v_completeness_2636_, v_stateType_2637_, v_inst_2638_, v_initState_2639_, v_handler_2640_, v_onDidChange_2641_);
return v_res_2643_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_2644_, lean_object* v_x_2645_, lean_object* v_x_2646_){
_start:
{
uint8_t v___x_2647_; 
v___x_2647_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_2645_, v_x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_2648_, lean_object* v_x_2649_, lean_object* v_x_2650_){
_start:
{
uint8_t v_res_2651_; lean_object* v_r_2652_; 
v_res_2651_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_2648_, v_x_2649_, v_x_2650_);
lean_dec_ref(v_x_2650_);
lean_dec_ref(v_x_2649_);
v_r_2652_ = lean_box(v_res_2651_);
return v_r_2652_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b1_2653_, lean_object* v_00_u03b2_2654_, lean_object* v_mutex_2655_, lean_object* v_k_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___redArg(v_mutex_2655_, v_k_2656_, v___y_2657_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_00_u03b1_2660_, lean_object* v_00_u03b2_2661_, lean_object* v_mutex_2662_, lean_object* v_k_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Std_Mutex_atomically___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__7(v_00_u03b1_2660_, v_00_u03b2_2661_, v_mutex_2662_, v_k_2663_, v___y_2664_);
lean_dec_ref(v___y_2664_);
return v_res_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_method_2667_, lean_object* v_completeness_2668_, lean_object* v_stateType_2669_, lean_object* v_inst_2670_, lean_object* v_initState_2671_, lean_object* v_handler_2672_, lean_object* v_onDidChange_2673_){
_start:
{
lean_object* v___x_2675_; 
v___x_2675_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_method_2667_, v_completeness_2668_, v_inst_2670_, v_initState_2671_, v_handler_2672_, v_onDidChange_2673_);
return v___x_2675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2___boxed(lean_object* v_method_2676_, lean_object* v_completeness_2677_, lean_object* v_stateType_2678_, lean_object* v_inst_2679_, lean_object* v_initState_2680_, lean_object* v_handler_2681_, lean_object* v_onDidChange_2682_, lean_object* v_a_2683_){
_start:
{
lean_object* v_res_2684_; 
v_res_2684_ = l___private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2(v_method_2676_, v_completeness_2677_, v_stateType_2678_, v_inst_2679_, v_initState_2680_, v_handler_2681_, v_onDidChange_2682_);
return v_res_2684_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_2685_, lean_object* v_x_2686_, size_t v_x_2687_, lean_object* v_x_2688_){
_start:
{
uint8_t v___x_2689_; 
v___x_2689_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_x_2686_, v_x_2687_, v_x_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2690_, lean_object* v_x_2691_, lean_object* v_x_2692_, lean_object* v_x_2693_){
_start:
{
size_t v_x_3506__boxed_2694_; uint8_t v_res_2695_; lean_object* v_r_2696_; 
v_x_3506__boxed_2694_ = lean_unbox_usize(v_x_2692_);
lean_dec(v_x_2692_);
v_res_2695_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_2690_, v_x_2691_, v_x_3506__boxed_2694_, v_x_2693_);
lean_dec_ref(v_x_2693_);
lean_dec_ref(v_x_2691_);
v_r_2696_ = lean_box(v_res_2695_);
return v_r_2696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_params_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_params_2697_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_params_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_Lean_Server_RequestM_parseRequestParams___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(v_params_2701_, v_a_2702_);
lean_dec_ref(v_a_2702_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8(lean_object* v_00_u03b2_2705_, lean_object* v_x_2706_, lean_object* v_x_2707_, lean_object* v_x_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8___redArg(v_x_2706_, v_x_2707_, v_x_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_2710_, lean_object* v_keys_2711_, lean_object* v_vals_2712_, lean_object* v_heq_2713_, lean_object* v_i_2714_, lean_object* v_k_2715_){
_start:
{
uint8_t v___x_2716_; 
v___x_2716_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_keys_2711_, v_i_2714_, v_k_2715_);
return v___x_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_2717_, lean_object* v_keys_2718_, lean_object* v_vals_2719_, lean_object* v_heq_2720_, lean_object* v_i_2721_, lean_object* v_k_2722_){
_start:
{
uint8_t v_res_2723_; lean_object* v_r_2724_; 
v_res_2723_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2_spec__3(v_00_u03b2_2717_, v_keys_2718_, v_vals_2719_, v_heq_2720_, v_i_2721_, v_k_2722_);
lean_dec_ref(v_k_2722_);
lean_dec_ref(v_vals_2719_);
lean_dec_ref(v_keys_2718_);
v_r_2724_ = lean_box(v_res_2723_);
return v_r_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(lean_object* v_00_u03b2_2725_, lean_object* v_x_2726_, size_t v_x_2727_, size_t v_x_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___redArg(v_x_2726_, v_x_2727_, v_x_2728_, v_x_2729_, v_x_2730_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11___boxed(lean_object* v_00_u03b2_2732_, lean_object* v_x_2733_, lean_object* v_x_2734_, lean_object* v_x_2735_, lean_object* v_x_2736_, lean_object* v_x_2737_){
_start:
{
size_t v_x_3532__boxed_2738_; size_t v_x_3533__boxed_2739_; lean_object* v_res_2740_; 
v_x_3532__boxed_2738_ = lean_unbox_usize(v_x_2734_);
lean_dec(v_x_2734_);
v_x_3533__boxed_2739_ = lean_unbox_usize(v_x_2735_);
lean_dec(v_x_2735_);
v_res_2740_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11(v_00_u03b2_2732_, v_x_2733_, v_x_3532__boxed_2738_, v_x_3533__boxed_2739_, v_x_2736_, v_x_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12(lean_object* v_00_u03b2_2741_, lean_object* v_n_2742_, lean_object* v_k_2743_, lean_object* v_v_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12___redArg(v_n_2742_, v_k_2743_, v_v_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(lean_object* v_00_u03b2_2746_, size_t v_depth_2747_, lean_object* v_keys_2748_, lean_object* v_vals_2749_, lean_object* v_heq_2750_, lean_object* v_i_2751_, lean_object* v_entries_2752_){
_start:
{
lean_object* v___x_2753_; 
v___x_2753_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___redArg(v_depth_2747_, v_keys_2748_, v_vals_2749_, v_i_2751_, v_entries_2752_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13___boxed(lean_object* v_00_u03b2_2754_, lean_object* v_depth_2755_, lean_object* v_keys_2756_, lean_object* v_vals_2757_, lean_object* v_heq_2758_, lean_object* v_i_2759_, lean_object* v_entries_2760_){
_start:
{
size_t v_depth_boxed_2761_; lean_object* v_res_2762_; 
v_depth_boxed_2761_ = lean_unbox_usize(v_depth_2755_);
lean_dec(v_depth_2755_);
v_res_2762_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__13(v_00_u03b2_2754_, v_depth_boxed_2761_, v_keys_2756_, v_vals_2757_, v_heq_2758_, v_i_2759_, v_entries_2760_);
lean_dec_ref(v_vals_2757_);
lean_dec_ref(v_keys_2756_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13(lean_object* v_00_u03b2_2763_, lean_object* v_x_2764_, lean_object* v_x_2765_, lean_object* v_x_2766_, lean_object* v_x_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Server_Requests_0__Lean_Server_overrideStatefulLspRequestHandler___at___00__private_Lean_Server_Requests_0__Lean_Server_registerStatefulLspRequestHandler___at___00Lean_Server_registerPartialStatefulLspRequestHandler___at___00__private_Lean_Server_FileWorker_InlayHints_0__Lean_Server_FileWorker_initFn_00___x40_Lean_Server_FileWorker_InlayHints_453813542____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__8_spec__11_spec__12_spec__13___redArg(v_x_2764_, v_x_2765_, v_x_2766_, v_x_2767_);
return v___x_2768_;
}
}
lean_object* runtime_initialize_Lean_Server_GoTo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Requests(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_InlayHints(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
