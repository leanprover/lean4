// Lean compiler output
// Module: Lean.Server.FileWorker.Utils
// Imports: public import Lean.Language.Lean.Types public import Lean.Server.Snapshots public import Lean.Server.AsyncList public import Std.Sync.Mutex
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
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_io_basemutex_lock(lean_object*);
lean_object* lean_io_basemutex_unlock(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Widget_TaggedText_stripTags___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_swap(lean_object*, lean_object*);
lean_object* l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_bindCheap___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Server_ServerTask_mapCheap___redArg(lean_object*, lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* l_Lean_Server_mkPublishDiagnosticsNotification(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_ms_now();
lean_object* l_Std_Mutex_new___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_io_get_random_bytes(size_t);
uint64_t l_ByteArray_toUInt64LE_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(lean_object*);
static const lean_closure_object l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1_value;
static lean_once_cell_t l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore___private__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0;
static lean_once_cell_t l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0 = (const lean_object*)&l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs;
static lean_once_cell_t l_Lean_Server_FileWorker_RpcSession_new___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__0;
static lean_once_cell_t l_Lean_Server_FileWorker_RpcSession_new___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Server_FileWorker_RpcSession_new___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0(lean_object* v_stx_1_, lean_object* v_parserState_2_, lean_object* v_nextCmdSnap_x3f_3_, lean_object* v_result_4_){
_start:
{
lean_object* v_cmdState_5_; lean_object* v___x_7_; uint8_t v_isShared_8_; uint8_t v_isSharedCheck_28_; 
v_cmdState_5_ = lean_ctor_get(v_result_4_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v_result_4_);
if (v_isSharedCheck_28_ == 0)
{
lean_object* v_unused_29_; lean_object* v_unused_30_; 
v_unused_29_ = lean_ctor_get(v_result_4_, 2);
lean_dec(v_unused_29_);
v_unused_30_ = lean_ctor_get(v_result_4_, 0);
lean_dec(v_unused_30_);
v___x_7_ = v_result_4_;
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
else
{
lean_inc(v_cmdState_5_);
lean_dec(v_result_4_);
v___x_7_ = lean_box(0);
v_isShared_8_ = v_isSharedCheck_28_;
goto v_resetjp_6_;
}
v_resetjp_6_:
{
lean_object* v___x_10_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 2, v_cmdState_5_);
lean_ctor_set(v___x_7_, 1, v_parserState_2_);
lean_ctor_set(v___x_7_, 0, v_stx_1_);
v___x_10_ = v___x_7_;
goto v_reusejp_9_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_stx_1_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_parserState_2_);
lean_ctor_set(v_reuseFailAlloc_27_, 2, v_cmdState_5_);
v___x_10_ = v_reuseFailAlloc_27_;
goto v_reusejp_9_;
}
v_reusejp_9_:
{
lean_object* v___y_12_; 
if (lean_obj_tag(v_nextCmdSnap_x3f_3_) == 0)
{
lean_object* v___x_15_; 
v___x_15_ = lean_box(2);
v___y_12_ = v___x_15_;
goto v___jp_11_;
}
else
{
lean_object* v_val_16_; lean_object* v___x_18_; uint8_t v_isShared_19_; uint8_t v_isSharedCheck_26_; 
v_val_16_ = lean_ctor_get(v_nextCmdSnap_x3f_3_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v_nextCmdSnap_x3f_3_);
if (v_isSharedCheck_26_ == 0)
{
v___x_18_ = v_nextCmdSnap_x3f_3_;
v_isShared_19_ = v_isSharedCheck_26_;
goto v_resetjp_17_;
}
else
{
lean_inc(v_val_16_);
lean_dec(v_nextCmdSnap_x3f_3_);
v___x_18_ = lean_box(0);
v_isShared_19_ = v_isSharedCheck_26_;
goto v_resetjp_17_;
}
v_resetjp_17_:
{
lean_object* v_task_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_24_; 
v_task_20_ = lean_ctor_get(v_val_16_, 3);
lean_inc_ref(v_task_20_);
lean_dec(v_val_16_);
v___x_21_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go), 1, 0);
v___x_22_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_20_, v___x_21_);
if (v_isShared_19_ == 0)
{
lean_ctor_set(v___x_18_, 0, v___x_22_);
v___x_24_ = v___x_18_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v___x_22_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
v___y_12_ = v___x_24_;
goto v___jp_11_;
}
}
}
v___jp_11_:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_10_);
lean_ctor_set(v___x_13_, 1, v___y_12_);
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(lean_object* v_cmdParsed_31_){
_start:
{
lean_object* v_elabSnap_32_; lean_object* v_resultSnap_33_; lean_object* v_stx_34_; lean_object* v_parserState_35_; lean_object* v_nextCmdSnap_x3f_36_; lean_object* v_task_37_; lean_object* v___f_38_; lean_object* v___x_39_; 
v_elabSnap_32_ = lean_ctor_get(v_cmdParsed_31_, 3);
v_resultSnap_33_ = lean_ctor_get(v_elabSnap_32_, 2);
lean_inc_ref(v_resultSnap_33_);
v_stx_34_ = lean_ctor_get(v_cmdParsed_31_, 1);
lean_inc(v_stx_34_);
v_parserState_35_ = lean_ctor_get(v_cmdParsed_31_, 2);
lean_inc_ref(v_parserState_35_);
v_nextCmdSnap_x3f_36_ = lean_ctor_get(v_cmdParsed_31_, 4);
lean_inc(v_nextCmdSnap_x3f_36_);
lean_dec_ref(v_cmdParsed_31_);
v_task_37_ = lean_ctor_get(v_resultSnap_33_, 3);
lean_inc_ref(v_task_37_);
lean_dec_ref(v_resultSnap_33_);
v___f_38_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0), 4, 3);
lean_closure_set(v___f_38_, 0, v_stx_34_);
lean_closure_set(v___f_38_, 1, v_parserState_35_);
lean_closure_set(v___f_38_, 2, v_nextCmdSnap_x3f_36_);
v___x_39_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_38_, v_task_37_);
return v___x_39_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = ((lean_object*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1));
v___x_44_ = lean_task_pure(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0(lean_object* v_stx_45_, lean_object* v_parserState_46_, lean_object* v_headerProcessed_47_){
_start:
{
lean_object* v_result_x3f_48_; lean_object* v___x_50_; uint8_t v_isShared_51_; uint8_t v_isSharedCheck_78_; 
v_result_x3f_48_ = lean_ctor_get(v_headerProcessed_47_, 2);
v_isSharedCheck_78_ = !lean_is_exclusive(v_headerProcessed_47_);
if (v_isSharedCheck_78_ == 0)
{
lean_object* v_unused_79_; lean_object* v_unused_80_; 
v_unused_79_ = lean_ctor_get(v_headerProcessed_47_, 1);
lean_dec(v_unused_79_);
v_unused_80_ = lean_ctor_get(v_headerProcessed_47_, 0);
lean_dec(v_unused_80_);
v___x_50_ = v_headerProcessed_47_;
v_isShared_51_ = v_isSharedCheck_78_;
goto v_resetjp_49_;
}
else
{
lean_inc(v_result_x3f_48_);
lean_dec(v_headerProcessed_47_);
v___x_50_ = lean_box(0);
v_isShared_51_ = v_isSharedCheck_78_;
goto v_resetjp_49_;
}
v_resetjp_49_:
{
if (lean_obj_tag(v_result_x3f_48_) == 1)
{
lean_object* v_val_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_76_; 
v_val_52_ = lean_ctor_get(v_result_x3f_48_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v_result_x3f_48_);
if (v_isSharedCheck_76_ == 0)
{
v___x_54_ = v_result_x3f_48_;
v_isShared_55_ = v_isSharedCheck_76_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_val_52_);
lean_dec(v_result_x3f_48_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_76_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v_firstCmdSnap_56_; lean_object* v_cmdState_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_75_; 
v_firstCmdSnap_56_ = lean_ctor_get(v_val_52_, 1);
v_cmdState_57_ = lean_ctor_get(v_val_52_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v_val_52_);
if (v_isSharedCheck_75_ == 0)
{
v___x_59_ = v_val_52_;
v_isShared_60_ = v_isSharedCheck_75_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_firstCmdSnap_56_);
lean_inc(v_cmdState_57_);
lean_dec(v_val_52_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_75_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v_task_61_; lean_object* v___x_63_; 
v_task_61_ = lean_ctor_get(v_firstCmdSnap_56_, 3);
lean_inc_ref(v_task_61_);
lean_dec_ref(v_firstCmdSnap_56_);
if (v_isShared_51_ == 0)
{
lean_ctor_set(v___x_50_, 2, v_cmdState_57_);
lean_ctor_set(v___x_50_, 1, v_parserState_46_);
lean_ctor_set(v___x_50_, 0, v_stx_45_);
v___x_63_ = v___x_50_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v_stx_45_);
lean_ctor_set(v_reuseFailAlloc_74_, 1, v_parserState_46_);
lean_ctor_set(v_reuseFailAlloc_74_, 2, v_cmdState_57_);
v___x_63_ = v_reuseFailAlloc_74_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_64_ = ((lean_object*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0));
v___x_65_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_61_, v___x_64_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 0, v___x_65_);
v___x_67_ = v___x_54_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v___x_65_);
v___x_67_ = v_reuseFailAlloc_73_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_69_; 
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_67_);
lean_ctor_set(v___x_59_, 0, v___x_63_);
v___x_69_ = v___x_59_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_63_);
lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_67_);
v___x_69_ = v_reuseFailAlloc_72_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
v___x_71_ = lean_task_pure(v___x_70_);
return v___x_71_;
}
}
}
}
}
}
else
{
lean_object* v___x_77_; 
lean_del_object(v___x_50_);
lean_dec(v_result_x3f_48_);
lean_dec_ref(v_parserState_46_);
lean_dec(v_stx_45_);
v___x_77_ = lean_obj_once(&l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2, &l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2_once, _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2);
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object* v_initSnap_81_){
_start:
{
lean_object* v_result_x3f_82_; 
v_result_x3f_82_ = lean_ctor_get(v_initSnap_81_, 4);
lean_inc(v_result_x3f_82_);
if (lean_obj_tag(v_result_x3f_82_) == 1)
{
lean_object* v_val_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_96_; 
v_val_83_ = lean_ctor_get(v_result_x3f_82_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_result_x3f_82_);
if (v_isSharedCheck_96_ == 0)
{
v___x_85_ = v_result_x3f_82_;
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_val_83_);
lean_dec(v_result_x3f_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_96_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v_processedSnap_87_; lean_object* v_stx_88_; lean_object* v_parserState_89_; lean_object* v_task_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v_processedSnap_87_ = lean_ctor_get(v_val_83_, 1);
lean_inc_ref(v_processedSnap_87_);
v_stx_88_ = lean_ctor_get(v_initSnap_81_, 3);
lean_inc(v_stx_88_);
lean_dec_ref(v_initSnap_81_);
v_parserState_89_ = lean_ctor_get(v_val_83_, 0);
lean_inc_ref(v_parserState_89_);
lean_dec(v_val_83_);
v_task_90_ = lean_ctor_get(v_processedSnap_87_, 3);
lean_inc_ref(v_task_90_);
lean_dec_ref(v_processedSnap_87_);
v___f_91_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0), 3, 2);
lean_closure_set(v___f_91_, 0, v_stx_88_);
lean_closure_set(v___f_91_, 1, v_parserState_89_);
v___x_92_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_90_, v___f_91_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 0, v___x_92_);
v___x_94_ = v___x_85_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_object* v___x_97_; 
lean_dec(v_result_x3f_82_);
lean_dec_ref(v_initSnap_81_);
v___x_97_ = lean_box(2);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore___private__1(lean_object* v_initSnap_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(v_initSnap_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(lean_object* v_mutex_100_, lean_object* v_k_101_){
_start:
{
lean_object* v_ref_103_; lean_object* v_mutex_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_ref_103_ = lean_ctor_get(v_mutex_100_, 0);
lean_inc(v_ref_103_);
v_mutex_104_ = lean_ctor_get(v_mutex_100_, 1);
lean_inc(v_mutex_104_);
lean_dec_ref(v_mutex_100_);
v___x_105_ = lean_io_basemutex_lock(v_mutex_104_);
v___x_106_ = lean_apply_2(v_k_101_, v_ref_103_, lean_box(0));
v___x_107_ = lean_io_basemutex_unlock(v_mutex_104_);
lean_dec(v_mutex_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg___boxed(lean_object* v_mutex_108_, lean_object* v_k_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_mutex_108_, v_k_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(lean_object* v_00_u03b1_112_, lean_object* v_00_u03b2_113_, lean_object* v_mutex_114_, lean_object* v_k_115_){
_start:
{
lean_object* v___x_117_; 
v___x_117_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_mutex_114_, v_k_115_);
return v___x_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___boxed(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_mutex_120_, lean_object* v_k_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(v_00_u03b1_118_, v_00_u03b2_119_, v_mutex_120_, v_k_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(lean_object* v_as_124_, size_t v_i_125_, size_t v_stop_126_, lean_object* v_b_127_){
_start:
{
uint8_t v___x_128_; 
v___x_128_ = lean_usize_dec_eq(v_i_125_, v_stop_126_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; size_t v___x_131_; size_t v___x_132_; 
v___x_129_ = lean_array_uget_borrowed(v_as_124_, v_i_125_);
lean_inc(v___x_129_);
v___x_130_ = l_Lean_PersistentArray_push___redArg(v_b_127_, v___x_129_);
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_add(v_i_125_, v___x_131_);
v_i_125_ = v___x_132_;
v_b_127_ = v___x_130_;
goto _start;
}
else
{
return v_b_127_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0___boxed(lean_object* v_as_134_, lean_object* v_i_135_, lean_object* v_stop_136_, lean_object* v_b_137_){
_start:
{
size_t v_i_boxed_138_; size_t v_stop_boxed_139_; lean_object* v_res_140_; 
v_i_boxed_138_ = lean_unbox_usize(v_i_135_);
lean_dec(v_i_135_);
v_stop_boxed_139_ = lean_unbox_usize(v_stop_136_);
lean_dec(v_stop_136_);
v_res_140_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_as_134_, v_i_boxed_138_, v_stop_boxed_139_, v_b_137_);
lean_dec_ref(v_as_134_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(lean_object* v_diags_141_, lean_object* v___y_142_){
_start:
{
lean_object* v___x_144_; lean_object* v_stickyDiagsRef_145_; lean_object* v_diags_146_; uint8_t v_isIncremental_147_; lean_object* v_publishedDiagsAmount_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_169_; 
v___x_144_ = lean_st_ref_take(v___y_142_);
v_stickyDiagsRef_145_ = lean_ctor_get(v___x_144_, 0);
v_diags_146_ = lean_ctor_get(v___x_144_, 1);
v_isIncremental_147_ = lean_ctor_get_uint8(v___x_144_, sizeof(void*)*3);
v_publishedDiagsAmount_148_ = lean_ctor_get(v___x_144_, 2);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_169_ == 0)
{
v___x_150_ = v___x_144_;
v_isShared_151_ = v_isSharedCheck_169_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_publishedDiagsAmount_148_);
lean_inc(v_diags_146_);
lean_inc(v_stickyDiagsRef_145_);
lean_dec(v___x_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_169_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___y_154_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_152_ = lean_box(0);
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = lean_array_get_size(v_diags_141_);
v___x_161_ = lean_nat_dec_lt(v___x_159_, v___x_160_);
if (v___x_161_ == 0)
{
v___y_154_ = v_diags_146_;
goto v___jp_153_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_le(v___x_160_, v___x_160_);
if (v___x_162_ == 0)
{
if (v___x_161_ == 0)
{
v___y_154_ = v_diags_146_;
goto v___jp_153_;
}
else
{
size_t v___x_163_; size_t v___x_164_; lean_object* v___x_165_; 
v___x_163_ = ((size_t)0ULL);
v___x_164_ = lean_usize_of_nat(v___x_160_);
v___x_165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_diags_141_, v___x_163_, v___x_164_, v_diags_146_);
v___y_154_ = v___x_165_;
goto v___jp_153_;
}
}
else
{
size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_160_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_diags_141_, v___x_166_, v___x_167_, v_diags_146_);
v___y_154_ = v___x_168_;
goto v___jp_153_;
}
}
v___jp_153_:
{
lean_object* v___x_156_; 
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v___y_154_);
v___x_156_ = v___x_150_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v_stickyDiagsRef_145_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___y_154_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_publishedDiagsAmount_148_);
lean_ctor_set_uint8(v_reuseFailAlloc_158_, sizeof(void*)*3, v_isIncremental_147_);
v___x_156_ = v_reuseFailAlloc_158_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; 
v___x_157_ = lean_st_ref_put(v___y_142_, v___x_156_);
return v___x_152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed(lean_object* v_diags_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(v_diags_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v_diags_170_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(lean_object* v_doc_174_, lean_object* v_diags_175_){
_start:
{
lean_object* v_diagnosticsMutex_177_; lean_object* v___f_178_; lean_object* v___x_179_; 
v_diagnosticsMutex_177_ = lean_ctor_get(v_doc_174_, 3);
lean_inc_ref(v_diagnosticsMutex_177_);
lean_dec_ref(v_doc_174_);
v___f_178_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed), 3, 1);
lean_closure_set(v___f_178_, 0, v_diags_175_);
v___x_179_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_177_, v___f_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___boxed(lean_object* v_doc_180_, lean_object* v_diags_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(v_doc_180_, v_diags_181_);
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(lean_object* v_diagnostic_184_, lean_object* v_as_185_, size_t v_i_186_, size_t v_stop_187_, lean_object* v_b_188_){
_start:
{
lean_object* v___y_190_; uint8_t v___x_194_; 
v___x_194_ = lean_usize_dec_eq(v_i_186_, v_stop_187_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v_message_196_; lean_object* v_message_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_195_ = lean_array_uget_borrowed(v_as_185_, v_i_186_);
v_message_196_ = lean_ctor_get(v___x_195_, 6);
v_message_197_ = lean_ctor_get(v_diagnostic_184_, 6);
lean_inc(v_message_196_);
v___x_198_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_196_);
lean_inc(v_message_197_);
v___x_199_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_197_);
v___x_200_ = lean_string_dec_eq(v___x_198_, v___x_199_);
lean_dec_ref(v___x_199_);
lean_dec_ref(v___x_198_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
lean_inc(v___x_195_);
v___x_201_ = l_Lean_PersistentArray_push___redArg(v_b_188_, v___x_195_);
v___y_190_ = v___x_201_;
goto v___jp_189_;
}
else
{
v___y_190_ = v_b_188_;
goto v___jp_189_;
}
}
else
{
lean_dec_ref(v_diagnostic_184_);
return v_b_188_;
}
v___jp_189_:
{
size_t v___x_191_; size_t v___x_192_; 
v___x_191_ = ((size_t)1ULL);
v___x_192_ = lean_usize_add(v_i_186_, v___x_191_);
v_i_186_ = v___x_192_;
v_b_188_ = v___y_190_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1___boxed(lean_object* v_diagnostic_202_, lean_object* v_as_203_, lean_object* v_i_204_, lean_object* v_stop_205_, lean_object* v_b_206_){
_start:
{
size_t v_i_boxed_207_; size_t v_stop_boxed_208_; lean_object* v_res_209_; 
v_i_boxed_207_ = lean_unbox_usize(v_i_204_);
lean_dec(v_i_204_);
v_stop_boxed_208_ = lean_unbox_usize(v_stop_205_);
lean_dec(v_stop_205_);
v_res_209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_202_, v_as_203_, v_i_boxed_207_, v_stop_boxed_208_, v_b_206_);
lean_dec_ref(v_as_203_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(lean_object* v_diagnostic_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v_cs_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_cs_213_ = lean_ctor_get(v_x_211_, 0);
v___x_214_ = lean_unsigned_to_nat(0u);
v___x_215_ = lean_array_get_size(v_cs_213_);
v___x_216_ = lean_nat_dec_lt(v___x_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_dec_ref(v_diagnostic_210_);
return v_x_212_;
}
else
{
size_t v___x_217_; size_t v___x_218_; lean_object* v___x_219_; 
v___x_217_ = ((size_t)0ULL);
v___x_218_ = lean_usize_of_nat(v___x_215_);
v___x_219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_210_, v_cs_213_, v___x_217_, v___x_218_, v_x_212_);
return v___x_219_;
}
}
else
{
lean_object* v_vs_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_vs_220_ = lean_ctor_get(v_x_211_, 0);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_array_get_size(v_vs_220_);
v___x_223_ = lean_nat_dec_lt(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_dec_ref(v_diagnostic_210_);
return v_x_212_;
}
else
{
size_t v___x_224_; size_t v___x_225_; lean_object* v___x_226_; 
v___x_224_ = ((size_t)0ULL);
v___x_225_ = lean_usize_of_nat(v___x_222_);
v___x_226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_210_, v_vs_220_, v___x_224_, v___x_225_, v_x_212_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(lean_object* v_diagnostic_227_, lean_object* v_as_228_, size_t v_i_229_, size_t v_stop_230_, lean_object* v_b_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = lean_usize_dec_eq(v_i_229_, v_stop_230_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; size_t v___x_235_; size_t v___x_236_; 
v___x_233_ = lean_array_uget_borrowed(v_as_228_, v_i_229_);
lean_inc_ref(v_diagnostic_227_);
v___x_234_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_227_, v___x_233_, v_b_231_);
v___x_235_ = ((size_t)1ULL);
v___x_236_ = lean_usize_add(v_i_229_, v___x_235_);
v_i_229_ = v___x_236_;
v_b_231_ = v___x_234_;
goto _start;
}
else
{
lean_dec_ref(v_diagnostic_227_);
return v_b_231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1___boxed(lean_object* v_diagnostic_238_, lean_object* v_as_239_, lean_object* v_i_240_, lean_object* v_stop_241_, lean_object* v_b_242_){
_start:
{
size_t v_i_boxed_243_; size_t v_stop_boxed_244_; lean_object* v_res_245_; 
v_i_boxed_243_ = lean_unbox_usize(v_i_240_);
lean_dec(v_i_240_);
v_stop_boxed_244_ = lean_unbox_usize(v_stop_241_);
lean_dec(v_stop_241_);
v_res_245_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_238_, v_as_239_, v_i_boxed_243_, v_stop_boxed_244_, v_b_242_);
lean_dec_ref(v_as_239_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2___boxed(lean_object* v_diagnostic_246_, lean_object* v_x_247_, lean_object* v_x_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_246_, v_x_247_, v_x_248_);
lean_dec_ref(v_x_247_);
return v_res_249_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(lean_object* v_diagnostic_251_, lean_object* v_x_252_, size_t v_x_253_, size_t v_x_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v_cs_256_; lean_object* v___x_257_; size_t v___x_258_; lean_object* v_j_259_; lean_object* v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_cs_256_ = lean_ctor_get(v_x_252_, 0);
v___x_257_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
v___x_258_ = lean_usize_shift_right(v_x_253_, v_x_254_);
v_j_259_ = lean_usize_to_nat(v___x_258_);
v___x_260_ = lean_array_get_borrowed(v___x_257_, v_cs_256_, v_j_259_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_shift_left(v___x_261_, v_x_254_);
v___x_263_ = lean_usize_sub(v___x_262_, v___x_261_);
v___x_264_ = lean_usize_land(v_x_253_, v___x_263_);
v___x_265_ = ((size_t)5ULL);
v___x_266_ = lean_usize_sub(v_x_254_, v___x_265_);
lean_inc_ref(v_diagnostic_251_);
v___x_267_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_251_, v___x_260_, v___x_264_, v___x_266_, v_x_255_);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_j_259_, v___x_268_);
lean_dec(v_j_259_);
v___x_270_ = lean_array_get_size(v_cs_256_);
v___x_271_ = lean_nat_dec_lt(v___x_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v___x_269_);
lean_dec_ref(v_diagnostic_251_);
return v___x_267_;
}
else
{
size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_usize_of_nat(v___x_269_);
lean_dec(v___x_269_);
v___x_273_ = lean_usize_of_nat(v___x_270_);
v___x_274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_251_, v_cs_256_, v___x_272_, v___x_273_, v___x_267_);
return v___x_274_;
}
}
else
{
lean_object* v_vs_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_vs_275_ = lean_ctor_get(v_x_252_, 0);
v___x_276_ = lean_usize_to_nat(v_x_253_);
v___x_277_ = lean_array_get_size(v_vs_275_);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v___x_276_);
lean_dec_ref(v_diagnostic_251_);
return v_x_255_;
}
else
{
size_t v___x_279_; size_t v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_usize_of_nat(v___x_276_);
lean_dec(v___x_276_);
v___x_280_ = lean_usize_of_nat(v___x_277_);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_251_, v_vs_275_, v___x_279_, v___x_280_, v_x_255_);
return v___x_281_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___boxed(lean_object* v_diagnostic_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
size_t v_x_1592__boxed_287_; size_t v_x_1593__boxed_288_; lean_object* v_res_289_; 
v_x_1592__boxed_287_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_x_1593__boxed_288_ = lean_unbox_usize(v_x_285_);
lean_dec(v_x_285_);
v_res_289_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_282_, v_x_283_, v_x_1592__boxed_287_, v_x_1593__boxed_288_, v_x_286_);
lean_dec_ref(v_x_283_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(lean_object* v_diagnostic_290_, lean_object* v_t_291_, lean_object* v_init_292_, lean_object* v_start_293_){
_start:
{
lean_object* v___x_294_; uint8_t v___x_295_; 
v___x_294_ = lean_unsigned_to_nat(0u);
v___x_295_ = lean_nat_dec_eq(v_start_293_, v___x_294_);
if (v___x_295_ == 0)
{
lean_object* v_root_296_; lean_object* v_tail_297_; size_t v_shift_298_; lean_object* v_tailOff_299_; uint8_t v___x_300_; 
v_root_296_ = lean_ctor_get(v_t_291_, 0);
v_tail_297_ = lean_ctor_get(v_t_291_, 1);
v_shift_298_ = lean_ctor_get_usize(v_t_291_, 4);
v_tailOff_299_ = lean_ctor_get(v_t_291_, 3);
v___x_300_ = lean_nat_dec_le(v_tailOff_299_, v_start_293_);
if (v___x_300_ == 0)
{
size_t v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_301_ = lean_usize_of_nat(v_start_293_);
lean_inc_ref(v_diagnostic_290_);
v___x_302_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_290_, v_root_296_, v___x_301_, v_shift_298_, v_init_292_);
v___x_303_ = lean_array_get_size(v_tail_297_);
v___x_304_ = lean_nat_dec_lt(v___x_294_, v___x_303_);
if (v___x_304_ == 0)
{
lean_dec_ref(v_diagnostic_290_);
return v___x_302_;
}
else
{
size_t v___x_305_; size_t v___x_306_; lean_object* v___x_307_; 
v___x_305_ = ((size_t)0ULL);
v___x_306_ = lean_usize_of_nat(v___x_303_);
v___x_307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_290_, v_tail_297_, v___x_305_, v___x_306_, v___x_302_);
return v___x_307_;
}
}
else
{
lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_308_ = lean_nat_sub(v_start_293_, v_tailOff_299_);
v___x_309_ = lean_array_get_size(v_tail_297_);
v___x_310_ = lean_nat_dec_lt(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_dec(v___x_308_);
lean_dec_ref(v_diagnostic_290_);
return v_init_292_;
}
else
{
size_t v___x_311_; size_t v___x_312_; lean_object* v___x_313_; 
v___x_311_ = lean_usize_of_nat(v___x_308_);
lean_dec(v___x_308_);
v___x_312_ = lean_usize_of_nat(v___x_309_);
v___x_313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_290_, v_tail_297_, v___x_311_, v___x_312_, v_init_292_);
return v___x_313_;
}
}
}
else
{
lean_object* v_root_314_; lean_object* v_tail_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v_root_314_ = lean_ctor_get(v_t_291_, 0);
v_tail_315_ = lean_ctor_get(v_t_291_, 1);
lean_inc_ref(v_diagnostic_290_);
v___x_316_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_290_, v_root_314_, v_init_292_);
v___x_317_ = lean_array_get_size(v_tail_315_);
v___x_318_ = lean_nat_dec_lt(v___x_294_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec_ref(v_diagnostic_290_);
return v___x_316_;
}
else
{
size_t v___x_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_319_ = ((size_t)0ULL);
v___x_320_ = lean_usize_of_nat(v___x_317_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_290_, v_tail_315_, v___x_319_, v___x_320_, v___x_316_);
return v___x_321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0___boxed(lean_object* v_diagnostic_322_, lean_object* v_t_323_, lean_object* v_init_324_, lean_object* v_start_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_322_, v_t_323_, v_init_324_, v_start_325_);
lean_dec(v_start_325_);
lean_dec_ref(v_t_323_);
return v_res_326_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_unsigned_to_nat(32u);
v___x_328_ = lean_mk_empty_array_with_capacity(v___x_327_);
v___x_329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1(void){
_start:
{
size_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_330_ = ((size_t)5ULL);
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = lean_unsigned_to_nat(32u);
v___x_333_ = lean_mk_empty_array_with_capacity(v___x_332_);
v___x_334_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0);
v___x_335_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_333_);
lean_ctor_set(v___x_335_, 2, v___x_331_);
lean_ctor_set(v___x_335_, 3, v___x_331_);
lean_ctor_set_usize(v___x_335_, 4, v___x_330_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(lean_object* v_diagnostic_336_, lean_object* v___y_337_){
_start:
{
lean_object* v___x_339_; lean_object* v_stickyDiagsRef_340_; lean_object* v_diags_341_; lean_object* v_publishedDiagsAmount_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_358_; 
v___x_339_ = lean_st_ref_get(v___y_337_);
v_stickyDiagsRef_340_ = lean_ctor_get(v___x_339_, 0);
v_diags_341_ = lean_ctor_get(v___x_339_, 1);
v_publishedDiagsAmount_342_ = lean_ctor_get(v___x_339_, 2);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_358_ == 0)
{
v___x_344_ = v___x_339_;
v_isShared_345_ = v_isSharedCheck_358_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_publishedDiagsAmount_342_);
lean_inc(v_diags_341_);
lean_inc(v_stickyDiagsRef_340_);
lean_dec(v___x_339_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_358_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v_stickyDiags_349_; lean_object* v___x_350_; lean_object* v___x_351_; uint8_t v___x_352_; lean_object* v___x_354_; 
v___x_346_ = lean_st_ref_take(v_stickyDiagsRef_340_);
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
lean_inc_ref(v_diagnostic_336_);
v_stickyDiags_349_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_336_, v___x_346_, v___x_348_, v___x_347_);
lean_dec(v___x_346_);
v___x_350_ = l_Lean_PersistentArray_push___redArg(v_stickyDiags_349_, v_diagnostic_336_);
v___x_351_ = lean_st_ref_put(v_stickyDiagsRef_340_, v___x_350_);
v___x_352_ = 0;
if (v_isShared_345_ == 0)
{
v___x_354_ = v___x_344_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_stickyDiagsRef_340_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v_diags_341_);
lean_ctor_set(v_reuseFailAlloc_357_, 2, v_publishedDiagsAmount_342_);
v___x_354_ = v_reuseFailAlloc_357_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_355_; lean_object* v___x_356_; 
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*3, v___x_352_);
v___x_355_ = lean_box(0);
v___x_356_ = lean_st_ref_swap(v___y_337_, v___x_354_);
lean_dec(v___x_356_);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed(lean_object* v_diagnostic_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(v_diagnostic_359_, v___y_360_);
lean_dec(v___y_360_);
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(lean_object* v_doc_363_, lean_object* v_diagnostic_364_){
_start:
{
lean_object* v_diagnosticsMutex_366_; lean_object* v___f_367_; lean_object* v___x_368_; 
v_diagnosticsMutex_366_ = lean_ctor_get(v_doc_363_, 3);
lean_inc_ref(v_diagnosticsMutex_366_);
lean_dec_ref(v_doc_363_);
v___f_367_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed), 3, 1);
lean_closure_set(v___f_367_, 0, v_diagnostic_364_);
v___x_368_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_366_, v___f_367_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___boxed(lean_object* v_doc_369_, lean_object* v_diagnostic_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(v_doc_369_, v_diagnostic_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(lean_object* v___y_373_){
_start:
{
lean_object* v___x_375_; lean_object* v_stickyDiagsRef_376_; lean_object* v_diags_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_375_ = lean_st_ref_get(v___y_373_);
v_stickyDiagsRef_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_stickyDiagsRef_376_);
v_diags_377_ = lean_ctor_get(v___x_375_, 1);
lean_inc_ref(v_diags_377_);
lean_dec(v___x_375_);
v___x_378_ = lean_st_ref_get(v_stickyDiagsRef_376_);
lean_dec(v_stickyDiagsRef_376_);
v___x_379_ = l_Lean_PersistentArray_append___redArg(v___x_378_, v_diags_377_);
lean_dec_ref(v_diags_377_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0___boxed(lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(v___y_380_);
lean_dec(v___y_380_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(lean_object* v_doc_384_){
_start:
{
lean_object* v_diagnosticsMutex_386_; lean_object* v___f_387_; lean_object* v___x_388_; 
v_diagnosticsMutex_386_ = lean_ctor_get(v_doc_384_, 3);
lean_inc_ref(v_diagnosticsMutex_386_);
lean_dec_ref(v_doc_384_);
v___f_387_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0));
v___x_388_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_386_, v___f_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___boxed(lean_object* v_doc_389_, lean_object* v_a_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(v_doc_389_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(lean_object* v___y_392_){
_start:
{
lean_object* v___x_394_; lean_object* v_stickyDiagsRef_395_; 
v___x_394_ = lean_st_ref_get(v___y_392_);
v_stickyDiagsRef_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_stickyDiagsRef_395_);
lean_dec(v___x_394_);
return v_stickyDiagsRef_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0___boxed(lean_object* v___y_396_, lean_object* v___y_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(v___y_396_);
lean_dec(v___y_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update(lean_object* v_doc_400_, lean_object* v_newMeta_401_, lean_object* v_newInitSnap_402_){
_start:
{
lean_object* v_diagnosticsMutex_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_419_; 
v_diagnosticsMutex_404_ = lean_ctor_get(v_doc_400_, 3);
v_isSharedCheck_419_ = !lean_is_exclusive(v_doc_400_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; lean_object* v_unused_421_; lean_object* v_unused_422_; 
v_unused_420_ = lean_ctor_get(v_doc_400_, 2);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_doc_400_, 1);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v_doc_400_, 0);
lean_dec(v_unused_422_);
v___x_406_ = v_doc_400_;
v_isShared_407_ = v_isSharedCheck_419_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_diagnosticsMutex_404_);
lean_dec(v_doc_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_419_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___f_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___f_408_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0));
v___x_409_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_404_, v___f_408_);
v___x_410_ = lean_unsigned_to_nat(0u);
v___x_411_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
v___x_412_ = 0;
v___x_413_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_413_, 0, v___x_409_);
lean_ctor_set(v___x_413_, 1, v___x_411_);
lean_ctor_set(v___x_413_, 2, v___x_410_);
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*3, v___x_412_);
v___x_414_ = l_Std_Mutex_new___redArg(v___x_413_);
lean_inc_ref(v_newInitSnap_402_);
v___x_415_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(v_newInitSnap_402_);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 3, v___x_414_);
lean_ctor_set(v___x_406_, 2, v___x_415_);
lean_ctor_set(v___x_406_, 1, v_newInitSnap_402_);
lean_ctor_set(v___x_406_, 0, v_newMeta_401_);
v___x_417_ = v___x_406_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_newMeta_401_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_newInitSnap_402_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v___x_414_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___boxed(lean_object* v_doc_423_, lean_object* v_newMeta_424_, lean_object* v_newInitSnap_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Server_FileWorker_EditableDocumentCore_update(v_doc_423_, v_newMeta_424_, v_newInitSnap_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(lean_object* v_as_428_, size_t v_i_429_, size_t v_stop_430_, lean_object* v_b_431_){
_start:
{
uint8_t v___x_432_; 
v___x_432_ = lean_usize_dec_eq(v_i_429_, v_stop_430_);
if (v___x_432_ == 0)
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; size_t v___x_436_; size_t v___x_437_; 
v___x_433_ = lean_array_uget_borrowed(v_as_428_, v_i_429_);
lean_inc(v___x_433_);
v___x_434_ = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(v___x_433_);
v___x_435_ = lean_array_push(v_b_431_, v___x_434_);
v___x_436_ = ((size_t)1ULL);
v___x_437_ = lean_usize_add(v_i_429_, v___x_436_);
v_i_429_ = v___x_437_;
v_b_431_ = v___x_435_;
goto _start;
}
else
{
return v_b_431_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1___boxed(lean_object* v_as_439_, lean_object* v_i_440_, lean_object* v_stop_441_, lean_object* v_b_442_){
_start:
{
size_t v_i_boxed_443_; size_t v_stop_boxed_444_; lean_object* v_res_445_; 
v_i_boxed_443_ = lean_unbox_usize(v_i_440_);
lean_dec(v_i_440_);
v_stop_boxed_444_ = lean_unbox_usize(v_stop_441_);
lean_dec(v_stop_441_);
v_res_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_as_439_, v_i_boxed_443_, v_stop_boxed_444_, v_b_442_);
lean_dec_ref(v_as_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(lean_object* v_x_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_446_) == 0)
{
lean_object* v_cs_448_; lean_object* v___x_449_; lean_object* v___x_450_; uint8_t v___x_451_; 
v_cs_448_ = lean_ctor_get(v_x_446_, 0);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_array_get_size(v_cs_448_);
v___x_451_ = lean_nat_dec_lt(v___x_449_, v___x_450_);
if (v___x_451_ == 0)
{
return v_x_447_;
}
else
{
size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((size_t)0ULL);
v___x_453_ = lean_usize_of_nat(v___x_450_);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_448_, v___x_452_, v___x_453_, v_x_447_);
return v___x_454_;
}
}
else
{
lean_object* v_vs_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_vs_455_ = lean_ctor_get(v_x_446_, 0);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_array_get_size(v_vs_455_);
v___x_458_ = lean_nat_dec_lt(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
return v_x_447_;
}
else
{
size_t v___x_459_; size_t v___x_460_; lean_object* v___x_461_; 
v___x_459_ = ((size_t)0ULL);
v___x_460_ = lean_usize_of_nat(v___x_457_);
v___x_461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_455_, v___x_459_, v___x_460_, v_x_447_);
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(lean_object* v_as_462_, size_t v_i_463_, size_t v_stop_464_, lean_object* v_b_465_){
_start:
{
uint8_t v___x_466_; 
v___x_466_ = lean_usize_dec_eq(v_i_463_, v_stop_464_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; size_t v___x_469_; size_t v___x_470_; 
v___x_467_ = lean_array_uget_borrowed(v_as_462_, v_i_463_);
v___x_468_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v___x_467_, v_b_465_);
v___x_469_ = ((size_t)1ULL);
v___x_470_ = lean_usize_add(v_i_463_, v___x_469_);
v_i_463_ = v___x_470_;
v_b_465_ = v___x_468_;
goto _start;
}
else
{
return v_b_465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1___boxed(lean_object* v_as_472_, lean_object* v_i_473_, lean_object* v_stop_474_, lean_object* v_b_475_){
_start:
{
size_t v_i_boxed_476_; size_t v_stop_boxed_477_; lean_object* v_res_478_; 
v_i_boxed_476_ = lean_unbox_usize(v_i_473_);
lean_dec(v_i_473_);
v_stop_boxed_477_ = lean_unbox_usize(v_stop_474_);
lean_dec(v_stop_474_);
v_res_478_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_as_472_, v_i_boxed_476_, v_stop_boxed_477_, v_b_475_);
lean_dec_ref(v_as_472_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2___boxed(lean_object* v_x_479_, lean_object* v_x_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_x_479_, v_x_480_);
lean_dec_ref(v_x_479_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(lean_object* v_x_482_, size_t v_x_483_, size_t v_x_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_482_) == 0)
{
lean_object* v_cs_486_; lean_object* v___x_487_; size_t v___x_488_; lean_object* v_j_489_; lean_object* v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_cs_486_ = lean_ctor_get(v_x_482_, 0);
v___x_487_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
v___x_488_ = lean_usize_shift_right(v_x_483_, v_x_484_);
v_j_489_ = lean_usize_to_nat(v___x_488_);
v___x_490_ = lean_array_get_borrowed(v___x_487_, v_cs_486_, v_j_489_);
v___x_491_ = ((size_t)1ULL);
v___x_492_ = lean_usize_shift_left(v___x_491_, v_x_484_);
v___x_493_ = lean_usize_sub(v___x_492_, v___x_491_);
v___x_494_ = lean_usize_land(v_x_483_, v___x_493_);
v___x_495_ = ((size_t)5ULL);
v___x_496_ = lean_usize_sub(v_x_484_, v___x_495_);
v___x_497_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v___x_490_, v___x_494_, v___x_496_, v_x_485_);
v___x_498_ = lean_unsigned_to_nat(1u);
v___x_499_ = lean_nat_add(v_j_489_, v___x_498_);
lean_dec(v_j_489_);
v___x_500_ = lean_array_get_size(v_cs_486_);
v___x_501_ = lean_nat_dec_lt(v___x_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_dec(v___x_499_);
return v___x_497_;
}
else
{
size_t v___x_502_; size_t v___x_503_; lean_object* v___x_504_; 
v___x_502_ = lean_usize_of_nat(v___x_499_);
lean_dec(v___x_499_);
v___x_503_ = lean_usize_of_nat(v___x_500_);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_486_, v___x_502_, v___x_503_, v___x_497_);
return v___x_504_;
}
}
else
{
lean_object* v_vs_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_vs_505_ = lean_ctor_get(v_x_482_, 0);
v___x_506_ = lean_usize_to_nat(v_x_483_);
v___x_507_ = lean_array_get_size(v_vs_505_);
v___x_508_ = lean_nat_dec_lt(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v___x_506_);
return v_x_485_;
}
else
{
size_t v___x_509_; size_t v___x_510_; lean_object* v___x_511_; 
v___x_509_ = lean_usize_of_nat(v___x_506_);
lean_dec(v___x_506_);
v___x_510_ = lean_usize_of_nat(v___x_507_);
v___x_511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_505_, v___x_509_, v___x_510_, v_x_485_);
return v___x_511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0___boxed(lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
size_t v_x_2405__boxed_516_; size_t v_x_2406__boxed_517_; lean_object* v_res_518_; 
v_x_2405__boxed_516_ = lean_unbox_usize(v_x_513_);
lean_dec(v_x_513_);
v_x_2406__boxed_517_ = lean_unbox_usize(v_x_514_);
lean_dec(v_x_514_);
v_res_518_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_x_512_, v_x_2405__boxed_516_, v_x_2406__boxed_517_, v_x_515_);
lean_dec_ref(v_x_512_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(lean_object* v_t_519_, lean_object* v_init_520_, lean_object* v_start_521_){
_start:
{
lean_object* v___x_522_; uint8_t v___x_523_; 
v___x_522_ = lean_unsigned_to_nat(0u);
v___x_523_ = lean_nat_dec_eq(v_start_521_, v___x_522_);
if (v___x_523_ == 0)
{
lean_object* v_root_524_; lean_object* v_tail_525_; size_t v_shift_526_; lean_object* v_tailOff_527_; uint8_t v___x_528_; 
v_root_524_ = lean_ctor_get(v_t_519_, 0);
v_tail_525_ = lean_ctor_get(v_t_519_, 1);
v_shift_526_ = lean_ctor_get_usize(v_t_519_, 4);
v_tailOff_527_ = lean_ctor_get(v_t_519_, 3);
v___x_528_ = lean_nat_dec_le(v_tailOff_527_, v_start_521_);
if (v___x_528_ == 0)
{
size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v___x_529_ = lean_usize_of_nat(v_start_521_);
v___x_530_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_524_, v___x_529_, v_shift_526_, v_init_520_);
v___x_531_ = lean_array_get_size(v_tail_525_);
v___x_532_ = lean_nat_dec_lt(v___x_522_, v___x_531_);
if (v___x_532_ == 0)
{
return v___x_530_;
}
else
{
size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((size_t)0ULL);
v___x_534_ = lean_usize_of_nat(v___x_531_);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_525_, v___x_533_, v___x_534_, v___x_530_);
return v___x_535_;
}
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_nat_sub(v_start_521_, v_tailOff_527_);
v___x_537_ = lean_array_get_size(v_tail_525_);
v___x_538_ = lean_nat_dec_lt(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_dec(v___x_536_);
return v_init_520_;
}
else
{
size_t v___x_539_; size_t v___x_540_; lean_object* v___x_541_; 
v___x_539_ = lean_usize_of_nat(v___x_536_);
lean_dec(v___x_536_);
v___x_540_ = lean_usize_of_nat(v___x_537_);
v___x_541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_525_, v___x_539_, v___x_540_, v_init_520_);
return v___x_541_;
}
}
}
else
{
lean_object* v_root_542_; lean_object* v_tail_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_root_542_ = lean_ctor_get(v_t_519_, 0);
v_tail_543_ = lean_ctor_get(v_t_519_, 1);
v___x_544_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_542_, v_init_520_);
v___x_545_ = lean_array_get_size(v_tail_543_);
v___x_546_ = lean_nat_dec_lt(v___x_522_, v___x_545_);
if (v___x_546_ == 0)
{
return v___x_544_;
}
else
{
size_t v___x_547_; size_t v___x_548_; lean_object* v___x_549_; 
v___x_547_ = ((size_t)0ULL);
v___x_548_ = lean_usize_of_nat(v___x_545_);
v___x_549_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_543_, v___x_547_, v___x_548_, v___x_544_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1___boxed(lean_object* v_t_550_, lean_object* v_init_551_, lean_object* v_start_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_t_550_, v_init_551_, v_start_552_);
lean_dec(v_start_552_);
lean_dec_ref(v_t_550_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(lean_object* v_t_554_, lean_object* v_init_555_, lean_object* v_start_556_){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_nat_dec_eq(v_start_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_object* v_root_559_; lean_object* v_tail_560_; size_t v_shift_561_; lean_object* v_tailOff_562_; uint8_t v___x_563_; 
v_root_559_ = lean_ctor_get(v_t_554_, 0);
v_tail_560_ = lean_ctor_get(v_t_554_, 1);
v_shift_561_ = lean_ctor_get_usize(v_t_554_, 4);
v_tailOff_562_ = lean_ctor_get(v_t_554_, 3);
v___x_563_ = lean_nat_dec_le(v_tailOff_562_, v_start_556_);
if (v___x_563_ == 0)
{
size_t v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_564_ = lean_usize_of_nat(v_start_556_);
v___x_565_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_559_, v___x_564_, v_shift_561_, v_init_555_);
v___x_566_ = lean_array_get_size(v_tail_560_);
v___x_567_ = lean_nat_dec_lt(v___x_557_, v___x_566_);
if (v___x_567_ == 0)
{
return v___x_565_;
}
else
{
size_t v___x_568_; size_t v___x_569_; lean_object* v___x_570_; 
v___x_568_ = ((size_t)0ULL);
v___x_569_ = lean_usize_of_nat(v___x_566_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_560_, v___x_568_, v___x_569_, v___x_565_);
return v___x_570_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_nat_sub(v_start_556_, v_tailOff_562_);
v___x_572_ = lean_array_get_size(v_tail_560_);
v___x_573_ = lean_nat_dec_lt(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_dec(v___x_571_);
return v_init_555_;
}
else
{
size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_usize_of_nat(v___x_571_);
lean_dec(v___x_571_);
v___x_575_ = lean_usize_of_nat(v___x_572_);
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_560_, v___x_574_, v___x_575_, v_init_555_);
return v___x_576_;
}
}
}
else
{
lean_object* v_root_577_; lean_object* v_tail_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_root_577_ = lean_ctor_get(v_t_554_, 0);
v_tail_578_ = lean_ctor_get(v_t_554_, 1);
v___x_579_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_577_, v_init_555_);
v___x_580_ = lean_array_get_size(v_tail_578_);
v___x_581_ = lean_nat_dec_lt(v___x_557_, v___x_580_);
if (v___x_581_ == 0)
{
return v___x_579_;
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_580_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_578_, v___x_582_, v___x_583_, v___x_579_);
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0___boxed(lean_object* v_t_585_, lean_object* v_init_586_, lean_object* v_start_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_t_585_, v_init_586_, v_start_587_);
lean_dec(v_start_587_);
lean_dec_ref(v_t_585_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(lean_object* v_meta_591_, lean_object* v_writeDiagnostics_592_, uint8_t v_incrementalDiagnosticSupport_593_, lean_object* v___y_594_){
_start:
{
lean_object* v___y_597_; lean_object* v___y_598_; lean_object* v_fst_602_; uint8_t v_snd_603_; lean_object* v___x_607_; uint8_t v___y_609_; 
v___x_607_ = lean_st_ref_get(v___y_594_);
if (v_incrementalDiagnosticSupport_593_ == 0)
{
v___y_609_ = v_incrementalDiagnosticSupport_593_;
goto v___jp_608_;
}
else
{
uint8_t v_isIncremental_630_; 
v_isIncremental_630_ = lean_ctor_get_uint8(v___x_607_, sizeof(void*)*3);
v___y_609_ = v_isIncremental_630_;
goto v___jp_608_;
}
v___jp_596_:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = l_Lean_Server_mkPublishDiagnosticsNotification(v_meta_591_, v___y_597_, v___y_598_);
v___x_600_ = lean_apply_2(v_writeDiagnostics_592_, v___x_599_, lean_box(0));
return v___x_600_;
}
v___jp_601_:
{
if (v_incrementalDiagnosticSupport_593_ == 0)
{
lean_object* v___x_604_; 
v___x_604_ = lean_box(0);
v___y_597_ = v_fst_602_;
v___y_598_ = v___x_604_;
goto v___jp_596_;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_box(v_snd_603_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
v___y_597_ = v_fst_602_;
v___y_598_ = v___x_606_;
goto v___jp_596_;
}
}
v___jp_608_:
{
lean_object* v_stickyDiagsRef_610_; lean_object* v_diags_611_; lean_object* v_publishedDiagsAmount_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_629_; 
v_stickyDiagsRef_610_ = lean_ctor_get(v___x_607_, 0);
v_diags_611_ = lean_ctor_get(v___x_607_, 1);
v_publishedDiagsAmount_612_ = lean_ctor_get(v___x_607_, 2);
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_629_ == 0)
{
v___x_614_ = v___x_607_;
v_isShared_615_ = v_isSharedCheck_629_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_publishedDiagsAmount_612_);
lean_inc(v_diags_611_);
lean_inc(v_stickyDiagsRef_610_);
lean_dec(v___x_607_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_629_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v_size_617_; uint8_t v___x_618_; lean_object* v___x_620_; 
v___x_616_ = lean_st_ref_get(v_stickyDiagsRef_610_);
v_size_617_ = lean_ctor_get(v_diags_611_, 2);
v___x_618_ = 1;
lean_inc(v_size_617_);
lean_inc_ref(v_diags_611_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 2, v_size_617_);
v___x_620_ = v___x_614_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v_stickyDiagsRef_610_);
lean_ctor_set(v_reuseFailAlloc_628_, 1, v_diags_611_);
lean_ctor_set(v_reuseFailAlloc_628_, 2, v_size_617_);
v___x_620_ = v_reuseFailAlloc_628_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
lean_ctor_set_uint8(v___x_620_, sizeof(void*)*3, v___x_618_);
v___x_621_ = lean_st_ref_swap(v___y_594_, v___x_620_);
lean_dec(v___x_621_);
if (v___y_609_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec(v_publishedDiagsAmount_612_);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_624_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v___x_616_, v___x_623_, v___x_622_);
lean_dec(v___x_616_);
v___x_625_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_diags_611_, v___x_624_, v___x_622_);
lean_dec_ref(v_diags_611_);
v_fst_602_ = v___x_625_;
v_snd_603_ = v___y_609_;
goto v___jp_601_;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec(v___x_616_);
v___x_626_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_627_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_diags_611_, v___x_626_, v_publishedDiagsAmount_612_);
lean_dec(v_publishedDiagsAmount_612_);
lean_dec_ref(v_diags_611_);
v_fst_602_ = v___x_627_;
v_snd_603_ = v___x_618_;
goto v___jp_601_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed(lean_object* v_meta_631_, lean_object* v_writeDiagnostics_632_, lean_object* v_incrementalDiagnosticSupport_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_636_; lean_object* v_res_637_; 
v_incrementalDiagnosticSupport_boxed_636_ = lean_unbox(v_incrementalDiagnosticSupport_633_);
v_res_637_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(v_meta_631_, v_writeDiagnostics_632_, v_incrementalDiagnosticSupport_boxed_636_, v___y_634_);
lean_dec(v___y_634_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(lean_object* v_doc_638_, uint8_t v_incrementalDiagnosticSupport_639_, lean_object* v_writeDiagnostics_640_){
_start:
{
lean_object* v_meta_642_; lean_object* v_diagnosticsMutex_643_; lean_object* v___x_644_; lean_object* v___f_645_; lean_object* v___x_646_; 
v_meta_642_ = lean_ctor_get(v_doc_638_, 0);
lean_inc_ref(v_meta_642_);
v_diagnosticsMutex_643_ = lean_ctor_get(v_doc_638_, 3);
lean_inc_ref(v_diagnosticsMutex_643_);
lean_dec_ref(v_doc_638_);
v___x_644_ = lean_box(v_incrementalDiagnosticSupport_639_);
v___f_645_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed), 5, 3);
lean_closure_set(v___f_645_, 0, v_meta_642_);
lean_closure_set(v___f_645_, 1, v_writeDiagnostics_640_);
lean_closure_set(v___f_645_, 2, v___x_644_);
v___x_646_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_643_, v___f_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___boxed(lean_object* v_doc_647_, lean_object* v_incrementalDiagnosticSupport_648_, lean_object* v_writeDiagnostics_649_, lean_object* v_a_650_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_651_; lean_object* v_res_652_; 
v_incrementalDiagnosticSupport_boxed_651_ = lean_unbox(v_incrementalDiagnosticSupport_648_);
v_res_652_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(v_doc_647_, v_incrementalDiagnosticSupport_boxed_651_, v_writeDiagnostics_649_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object* v_ed_653_){
_start:
{
lean_object* v_toEditableDocumentCore_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_665_; 
v_toEditableDocumentCore_654_ = lean_ctor_get(v_ed_653_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_ed_653_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_ed_653_, 1);
lean_dec(v_unused_666_);
v___x_656_ = v_ed_653_;
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_toEditableDocumentCore_654_);
lean_dec(v_ed_653_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v_meta_658_; lean_object* v_uri_659_; lean_object* v_version_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v_meta_658_ = lean_ctor_get(v_toEditableDocumentCore_654_, 0);
lean_inc_ref(v_meta_658_);
lean_dec_ref(v_toEditableDocumentCore_654_);
v_uri_659_ = lean_ctor_get(v_meta_658_, 0);
lean_inc_ref(v_uri_659_);
v_version_660_ = lean_ctor_get(v_meta_658_, 2);
lean_inc(v_version_660_);
lean_dec_ref(v_meta_658_);
v___x_661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_661_, 0, v_version_660_);
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v___x_661_);
lean_ctor_set(v___x_656_, 0, v_uri_659_);
v___x_663_ = v___x_656_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v_uri_659_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
return v___x_663_;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs(void){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = lean_unsigned_to_nat(30000u);
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0(void){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_668_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1(void){
_start:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__0, &l_Lean_Server_FileWorker_RpcSession_new___closed__0_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___x_669_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new(uint8_t v_wireFormat_671_){
_start:
{
size_t v___x_673_; lean_object* v___x_674_; 
v___x_673_ = ((size_t)8ULL);
v___x_674_ = lean_io_get_random_bytes(v___x_673_);
if (lean_obj_tag(v___x_674_) == 0)
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_692_; 
v_a_675_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_692_ == 0)
{
v___x_677_ = v___x_674_;
v_isShared_678_ = v_isSharedCheck_692_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_674_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_692_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
uint64_t v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; size_t v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_679_ = l_ByteArray_toUInt64LE_x21(v_a_675_);
lean_dec(v_a_675_);
v___x_680_ = lean_io_mono_ms_now();
v___x_681_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__1, &l_Lean_Server_FileWorker_RpcSession_new___closed__1_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1);
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_683_, 0, v___x_681_);
lean_ctor_set(v___x_683_, 1, v___x_681_);
lean_ctor_set_usize(v___x_683_, 2, v___x_682_);
lean_ctor_set_uint8(v___x_683_, sizeof(void*)*3, v_wireFormat_671_);
v___x_684_ = lean_unsigned_to_nat(30000u);
v___x_685_ = lean_nat_add(v___x_680_, v___x_684_);
lean_dec(v___x_680_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_683_);
lean_ctor_set(v___x_686_, 1, v___x_685_);
v___x_687_ = lean_box_uint64(v___x_679_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___x_686_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_688_);
v___x_690_ = v___x_677_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v_a_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_700_; 
v_a_693_ = lean_ctor_get(v___x_674_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_700_ == 0)
{
v___x_695_ = v___x_674_;
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_a_693_);
lean_dec(v___x_674_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_700_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_698_; 
if (v_isShared_696_ == 0)
{
v___x_698_ = v___x_695_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v_a_693_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
return v___x_698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new___boxed(lean_object* v_wireFormat_701_, lean_object* v_a_702_){
_start:
{
uint8_t v_wireFormat_boxed_703_; lean_object* v_res_704_; 
v_wireFormat_boxed_703_ = lean_unbox(v_wireFormat_701_);
v_res_704_ = l_Lean_Server_FileWorker_RpcSession_new(v_wireFormat_boxed_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object* v_monoMsNow_705_, lean_object* v_s_706_){
_start:
{
lean_object* v_objects_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_716_; 
v_objects_707_ = lean_ctor_get(v_s_706_, 0);
v_isSharedCheck_716_ = !lean_is_exclusive(v_s_706_);
if (v_isSharedCheck_716_ == 0)
{
lean_object* v_unused_717_; 
v_unused_717_ = lean_ctor_get(v_s_706_, 1);
lean_dec(v_unused_717_);
v___x_709_ = v_s_706_;
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_objects_707_);
lean_dec(v_s_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_716_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_711_ = lean_unsigned_to_nat(30000u);
v___x_712_ = lean_nat_add(v_monoMsNow_705_, v___x_711_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 1, v___x_712_);
v___x_714_ = v___x_709_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_objects_707_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v___x_712_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object* v_monoMsNow_718_, lean_object* v_s_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Server_FileWorker_RpcSession_keptAlive(v_monoMsNow_718_, v_s_719_);
lean_dec(v_monoMsNow_718_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object* v_s_721_){
_start:
{
lean_object* v___x_723_; lean_object* v_expireTime_724_; uint8_t v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_723_ = lean_io_mono_ms_now();
v_expireTime_724_ = lean_ctor_get(v_s_721_, 1);
v___x_725_ = lean_nat_dec_le(v_expireTime_724_, v___x_723_);
lean_dec(v___x_723_);
v___x_726_ = lean_box(v___x_725_);
v___x_727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object* v_s_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Lean_Server_FileWorker_RpcSession_hasExpired(v_s_728_);
lean_dec_ref(v_s_728_);
return v_res_730_;
}
}
lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Snapshots(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_AsyncList(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Server_FileWorker_Utils(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_Snapshots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_AsyncList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs = _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs();
lean_mark_persistent(l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Server_FileWorker_Utils(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* initialize_Lean_Server_Snapshots(uint8_t builtin);
lean_object* initialize_Lean_Server_AsyncList(uint8_t builtin);
lean_object* initialize_Std_Sync_Mutex(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_Utils(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Language_Lean_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_Snapshots(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Server_AsyncList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sync_Mutex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Server_FileWorker_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Server_FileWorker_Utils(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Server_FileWorker_Utils(builtin);
}
#ifdef __cplusplus
}
#endif
