// Lean compiler output
// Module: Lean.Server.FileWorker.Utils
// Imports: public import Lean.Language.Lean.Types public import Lean.Server.Snapshots public import Lean.Server.AsyncList public import Std.Sync.Mutex import Init.Data.ByteArray.Extra
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
lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(lean_object* v_mutex_100_, lean_object* v_k_101_){
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
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_100_ = stack[0].m_obj;
lean_object* v_k_101_ = stack[1].m_obj;
lean_object* v_res_108_;
v_res_108_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_mutex_100_, v_k_101_);
stack->m_obj
 = v_res_108_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg___boxed(lean_object* v_mutex_109_, lean_object* v_k_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_mutex_109_, v_k_110_);
return v_res_112_;
}
}
lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(lean_object* v_00_u03b1_113_, lean_object* v_00_u03b2_114_, lean_object* v_mutex_115_, lean_object* v_k_116_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_mutex_115_, v_k_116_);
return v___x_118_;
}
}
LEAN_EXPORT void l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mutex_115_ = stack[2].m_obj;
lean_object* v_k_116_ = stack[3].m_obj;
lean_object* v_res_119_;
v_res_119_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(lean_box(0), lean_box(0), v_mutex_115_, v_k_116_);
stack->m_obj
 = v_res_119_;
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___boxed(lean_object* v_00_u03b1_120_, lean_object* v_00_u03b2_121_, lean_object* v_mutex_122_, lean_object* v_k_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(v_00_u03b1_120_, v_00_u03b2_121_, v_mutex_122_, v_k_123_);
return v_res_125_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(lean_object* v_as_126_, size_t v_i_127_, size_t v_stop_128_, lean_object* v_b_129_){
_start:
{
uint8_t v___x_130_; 
v___x_130_ = lean_usize_dec_eq(v_i_127_, v_stop_128_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; size_t v___x_133_; size_t v___x_134_; 
v___x_131_ = lean_array_uget_borrowed(v_as_126_, v_i_127_);
lean_inc(v___x_131_);
v___x_132_ = l_Lean_PersistentArray_push___redArg(v_b_129_, v___x_131_);
v___x_133_ = ((size_t)1ULL);
v___x_134_ = lean_usize_add(v_i_127_, v___x_133_);
v_i_127_ = v___x_134_;
v_b_129_ = v___x_132_;
goto _start;
}
else
{
return v_b_129_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_126_ = stack[0].m_obj;
size_t v_i_127_ = stack[1].m_num;
size_t v_stop_128_ = stack[2].m_num;
lean_object* v_b_129_ = stack[3].m_obj;
lean_object* v_res_136_;
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_as_126_, v_i_127_, v_stop_128_, v_b_129_);
stack->m_obj
 = v_res_136_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0___boxed(lean_object* v_as_137_, lean_object* v_i_138_, lean_object* v_stop_139_, lean_object* v_b_140_){
_start:
{
size_t v_i_boxed_141_; size_t v_stop_boxed_142_; lean_object* v_res_143_; 
v_i_boxed_141_ = lean_unbox_usize(v_i_138_);
lean_dec(v_i_138_);
v_stop_boxed_142_ = lean_unbox_usize(v_stop_139_);
lean_dec(v_stop_139_);
v_res_143_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_as_137_, v_i_boxed_141_, v_stop_boxed_142_, v_b_140_);
lean_dec_ref(v_as_137_);
return v_res_143_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(lean_object* v_diags_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_147_; lean_object* v_stickyDiagsRef_148_; lean_object* v_diags_149_; uint8_t v_isIncremental_150_; lean_object* v_publishedDiagsAmount_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_172_; 
v___x_147_ = lean_st_ref_take(v___y_145_);
v_stickyDiagsRef_148_ = lean_ctor_get(v___x_147_, 0);
v_diags_149_ = lean_ctor_get(v___x_147_, 1);
v_isIncremental_150_ = lean_ctor_get_uint8(v___x_147_, sizeof(void*)*3);
v_publishedDiagsAmount_151_ = lean_ctor_get(v___x_147_, 2);
v_isSharedCheck_172_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_172_ == 0)
{
v___x_153_ = v___x_147_;
v_isShared_154_ = v_isSharedCheck_172_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_publishedDiagsAmount_151_);
lean_inc(v_diags_149_);
lean_inc(v_stickyDiagsRef_148_);
lean_dec(v___x_147_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_172_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___y_157_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_155_ = lean_box(0);
v___x_162_ = lean_unsigned_to_nat(0u);
v___x_163_ = lean_array_get_size(v_diags_144_);
v___x_164_ = lean_nat_dec_lt(v___x_162_, v___x_163_);
if (v___x_164_ == 0)
{
v___y_157_ = v_diags_149_;
goto v___jp_156_;
}
else
{
uint8_t v___x_165_; 
v___x_165_ = lean_nat_dec_le(v___x_163_, v___x_163_);
if (v___x_165_ == 0)
{
if (v___x_164_ == 0)
{
v___y_157_ = v_diags_149_;
goto v___jp_156_;
}
else
{
size_t v___x_166_; size_t v___x_167_; lean_object* v___x_168_; 
v___x_166_ = ((size_t)0ULL);
v___x_167_ = lean_usize_of_nat(v___x_163_);
v___x_168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_diags_144_, v___x_166_, v___x_167_, v_diags_149_);
v___y_157_ = v___x_168_;
goto v___jp_156_;
}
}
else
{
size_t v___x_169_; size_t v___x_170_; lean_object* v___x_171_; 
v___x_169_ = ((size_t)0ULL);
v___x_170_ = lean_usize_of_nat(v___x_163_);
v___x_171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_diags_144_, v___x_169_, v___x_170_, v_diags_149_);
v___y_157_ = v___x_171_;
goto v___jp_156_;
}
}
v___jp_156_:
{
lean_object* v___x_159_; 
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v___y_157_);
v___x_159_ = v___x_153_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_stickyDiagsRef_148_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___y_157_);
lean_ctor_set(v_reuseFailAlloc_161_, 2, v_publishedDiagsAmount_151_);
lean_ctor_set_uint8(v_reuseFailAlloc_161_, sizeof(void*)*3, v_isIncremental_150_);
v___x_159_ = v_reuseFailAlloc_161_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
lean_object* v___x_160_; 
v___x_160_ = lean_st_ref_put(v___y_145_, v___x_159_);
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_diags_144_ = stack[0].m_obj;
lean_object* v___y_145_ = stack[1].m_obj;
lean_object* v_res_173_;
v_res_173_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(v_diags_144_, v___y_145_);
stack->m_obj
 = v_res_173_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed(lean_object* v_diags_174_, lean_object* v___y_175_, lean_object* v___y_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(v_diags_174_, v___y_175_);
lean_dec(v___y_175_);
lean_dec_ref(v_diags_174_);
return v_res_177_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(lean_object* v_doc_178_, lean_object* v_diags_179_){
_start:
{
lean_object* v_diagnosticsMutex_181_; lean_object* v___f_182_; lean_object* v___x_183_; 
v_diagnosticsMutex_181_ = lean_ctor_get(v_doc_178_, 3);
lean_inc_ref(v_diagnosticsMutex_181_);
lean_dec_ref(v_doc_178_);
v___f_182_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed), 3, 1);
lean_closure_set(v___f_182_, 0, v_diags_179_);
v___x_183_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_181_, v___f_182_);
return v___x_183_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_178_ = stack[0].m_obj;
lean_object* v_diags_179_ = stack[1].m_obj;
lean_object* v_res_184_;
v_res_184_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(v_doc_178_, v_diags_179_);
stack->m_obj
 = v_res_184_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___boxed(lean_object* v_doc_185_, lean_object* v_diags_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(v_doc_185_, v_diags_186_);
return v_res_188_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(lean_object* v_diagnostic_189_, lean_object* v_as_190_, size_t v_i_191_, size_t v_stop_192_, lean_object* v_b_193_){
_start:
{
lean_object* v___y_195_; uint8_t v___x_199_; 
v___x_199_ = lean_usize_dec_eq(v_i_191_, v_stop_192_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; lean_object* v_message_201_; lean_object* v_message_202_; lean_object* v___x_203_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_200_ = lean_array_uget_borrowed(v_as_190_, v_i_191_);
v_message_201_ = lean_ctor_get(v___x_200_, 6);
v_message_202_ = lean_ctor_get(v_diagnostic_189_, 6);
lean_inc(v_message_201_);
v___x_203_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_201_);
lean_inc(v_message_202_);
v___x_204_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_202_);
v___x_205_ = lean_string_dec_eq(v___x_203_, v___x_204_);
lean_dec_ref(v___x_204_);
lean_dec_ref(v___x_203_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
lean_inc(v___x_200_);
v___x_206_ = l_Lean_PersistentArray_push___redArg(v_b_193_, v___x_200_);
v___y_195_ = v___x_206_;
goto v___jp_194_;
}
else
{
v___y_195_ = v_b_193_;
goto v___jp_194_;
}
}
else
{
lean_dec_ref(v_diagnostic_189_);
return v_b_193_;
}
v___jp_194_:
{
size_t v___x_196_; size_t v___x_197_; 
v___x_196_ = ((size_t)1ULL);
v___x_197_ = lean_usize_add(v_i_191_, v___x_196_);
v_i_191_ = v___x_197_;
v_b_193_ = v___y_195_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_diagnostic_189_ = stack[0].m_obj;
lean_object* v_as_190_ = stack[1].m_obj;
size_t v_i_191_ = stack[2].m_num;
size_t v_stop_192_ = stack[3].m_num;
lean_object* v_b_193_ = stack[4].m_obj;
lean_object* v_res_207_;
v_res_207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_189_, v_as_190_, v_i_191_, v_stop_192_, v_b_193_);
stack->m_obj
 = v_res_207_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1___boxed(lean_object* v_diagnostic_208_, lean_object* v_as_209_, lean_object* v_i_210_, lean_object* v_stop_211_, lean_object* v_b_212_){
_start:
{
size_t v_i_boxed_213_; size_t v_stop_boxed_214_; lean_object* v_res_215_; 
v_i_boxed_213_ = lean_unbox_usize(v_i_210_);
lean_dec(v_i_210_);
v_stop_boxed_214_ = lean_unbox_usize(v_stop_211_);
lean_dec(v_stop_211_);
v_res_215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_208_, v_as_209_, v_i_boxed_213_, v_stop_boxed_214_, v_b_212_);
lean_dec_ref(v_as_209_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(lean_object* v_diagnostic_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v_cs_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_cs_219_ = lean_ctor_get(v_x_217_, 0);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_array_get_size(v_cs_219_);
v___x_222_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_diagnostic_216_);
return v_x_218_;
}
else
{
size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; 
v___x_223_ = ((size_t)0ULL);
v___x_224_ = lean_usize_of_nat(v___x_221_);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_216_, v_cs_219_, v___x_223_, v___x_224_, v_x_218_);
return v___x_225_;
}
}
else
{
lean_object* v_vs_226_; lean_object* v___x_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_vs_226_ = lean_ctor_get(v_x_217_, 0);
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = lean_array_get_size(v_vs_226_);
v___x_229_ = lean_nat_dec_lt(v___x_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_dec_ref(v_diagnostic_216_);
return v_x_218_;
}
else
{
size_t v___x_230_; size_t v___x_231_; lean_object* v___x_232_; 
v___x_230_ = ((size_t)0ULL);
v___x_231_ = lean_usize_of_nat(v___x_228_);
v___x_232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_216_, v_vs_226_, v___x_230_, v___x_231_, v_x_218_);
return v___x_232_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(lean_object* v_diagnostic_233_, lean_object* v_as_234_, size_t v_i_235_, size_t v_stop_236_, lean_object* v_b_237_){
_start:
{
uint8_t v___x_238_; 
v___x_238_ = lean_usize_dec_eq(v_i_235_, v_stop_236_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; lean_object* v___x_240_; size_t v___x_241_; size_t v___x_242_; 
v___x_239_ = lean_array_uget_borrowed(v_as_234_, v_i_235_);
lean_inc_ref(v_diagnostic_233_);
v___x_240_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_233_, v___x_239_, v_b_237_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_add(v_i_235_, v___x_241_);
v_i_235_ = v___x_242_;
v_b_237_ = v___x_240_;
goto _start;
}
else
{
lean_dec_ref(v_diagnostic_233_);
return v_b_237_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_diagnostic_233_ = stack[0].m_obj;
lean_object* v_as_234_ = stack[1].m_obj;
size_t v_i_235_ = stack[2].m_num;
size_t v_stop_236_ = stack[3].m_num;
lean_object* v_b_237_ = stack[4].m_obj;
lean_object* v_res_244_;
v_res_244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_233_, v_as_234_, v_i_235_, v_stop_236_, v_b_237_);
stack->m_obj
 = v_res_244_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1___boxed(lean_object* v_diagnostic_245_, lean_object* v_as_246_, lean_object* v_i_247_, lean_object* v_stop_248_, lean_object* v_b_249_){
_start:
{
size_t v_i_boxed_250_; size_t v_stop_boxed_251_; lean_object* v_res_252_; 
v_i_boxed_250_ = lean_unbox_usize(v_i_247_);
lean_dec(v_i_247_);
v_stop_boxed_251_ = lean_unbox_usize(v_stop_248_);
lean_dec(v_stop_248_);
v_res_252_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_245_, v_as_246_, v_i_boxed_250_, v_stop_boxed_251_, v_b_249_);
lean_dec_ref(v_as_246_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2___boxed(lean_object* v_diagnostic_253_, lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_253_, v_x_254_, v_x_255_);
lean_dec_ref(v_x_254_);
return v_res_256_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_257_; 
v___x_257_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_257_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(lean_object* v_diagnostic_258_, lean_object* v_x_259_, size_t v_x_260_, size_t v_x_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_259_) == 0)
{
lean_object* v_cs_263_; lean_object* v___x_264_; size_t v___x_265_; lean_object* v_j_266_; lean_object* v___x_267_; size_t v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v_cs_263_ = lean_ctor_get(v_x_259_, 0);
v___x_264_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
v___x_265_ = lean_usize_shift_right(v_x_260_, v_x_261_);
v_j_266_ = lean_usize_to_nat(v___x_265_);
v___x_267_ = lean_array_get_borrowed(v___x_264_, v_cs_263_, v_j_266_);
v___x_268_ = ((size_t)1ULL);
v___x_269_ = lean_usize_shift_left(v___x_268_, v_x_261_);
v___x_270_ = lean_usize_sub(v___x_269_, v___x_268_);
v___x_271_ = lean_usize_land(v_x_260_, v___x_270_);
v___x_272_ = ((size_t)5ULL);
v___x_273_ = lean_usize_sub(v_x_261_, v___x_272_);
lean_inc_ref(v_diagnostic_258_);
v___x_274_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_258_, v___x_267_, v___x_271_, v___x_273_, v_x_262_);
v___x_275_ = lean_unsigned_to_nat(1u);
v___x_276_ = lean_nat_add(v_j_266_, v___x_275_);
lean_dec(v_j_266_);
v___x_277_ = lean_array_get_size(v_cs_263_);
v___x_278_ = lean_nat_dec_lt(v___x_276_, v___x_277_);
if (v___x_278_ == 0)
{
lean_dec(v___x_276_);
lean_dec_ref(v_diagnostic_258_);
return v___x_274_;
}
else
{
size_t v___x_279_; size_t v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_usize_of_nat(v___x_276_);
lean_dec(v___x_276_);
v___x_280_ = lean_usize_of_nat(v___x_277_);
v___x_281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_258_, v_cs_263_, v___x_279_, v___x_280_, v___x_274_);
return v___x_281_;
}
}
else
{
lean_object* v_vs_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_vs_282_ = lean_ctor_get(v_x_259_, 0);
v___x_283_ = lean_usize_to_nat(v_x_260_);
v___x_284_ = lean_array_get_size(v_vs_282_);
v___x_285_ = lean_nat_dec_lt(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_dec(v___x_283_);
lean_dec_ref(v_diagnostic_258_);
return v_x_262_;
}
else
{
size_t v___x_286_; size_t v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_usize_of_nat(v___x_283_);
lean_dec(v___x_283_);
v___x_287_ = lean_usize_of_nat(v___x_284_);
v___x_288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_258_, v_vs_282_, v___x_286_, v___x_287_, v_x_262_);
return v___x_288_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_diagnostic_258_ = stack[0].m_obj;
lean_object* v_x_259_ = stack[1].m_obj;
size_t v_x_260_ = stack[2].m_num;
size_t v_x_261_ = stack[3].m_num;
lean_object* v_x_262_ = stack[4].m_obj;
lean_object* v_res_289_;
v_res_289_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_258_, v_x_259_, v_x_260_, v_x_261_, v_x_262_);
stack->m_obj
 = v_res_289_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___boxed(lean_object* v_diagnostic_290_, lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
size_t v_x_1627__boxed_295_; size_t v_x_1628__boxed_296_; lean_object* v_res_297_; 
v_x_1627__boxed_295_ = lean_unbox_usize(v_x_292_);
lean_dec(v_x_292_);
v_x_1628__boxed_296_ = lean_unbox_usize(v_x_293_);
lean_dec(v_x_293_);
v_res_297_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_290_, v_x_291_, v_x_1627__boxed_295_, v_x_1628__boxed_296_, v_x_294_);
lean_dec_ref(v_x_291_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(lean_object* v_diagnostic_298_, lean_object* v_t_299_, lean_object* v_init_300_, lean_object* v_start_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_nat_dec_eq(v_start_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v_root_304_; lean_object* v_tail_305_; size_t v_shift_306_; lean_object* v_tailOff_307_; uint8_t v___x_308_; 
v_root_304_ = lean_ctor_get(v_t_299_, 0);
v_tail_305_ = lean_ctor_get(v_t_299_, 1);
v_shift_306_ = lean_ctor_get_usize(v_t_299_, 4);
v_tailOff_307_ = lean_ctor_get(v_t_299_, 3);
v___x_308_ = lean_nat_dec_le(v_tailOff_307_, v_start_301_);
if (v___x_308_ == 0)
{
size_t v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_309_ = lean_usize_of_nat(v_start_301_);
lean_inc_ref(v_diagnostic_298_);
v___x_310_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_298_, v_root_304_, v___x_309_, v_shift_306_, v_init_300_);
v___x_311_ = lean_array_get_size(v_tail_305_);
v___x_312_ = lean_nat_dec_lt(v___x_302_, v___x_311_);
if (v___x_312_ == 0)
{
lean_dec_ref(v_diagnostic_298_);
return v___x_310_;
}
else
{
size_t v___x_313_; size_t v___x_314_; lean_object* v___x_315_; 
v___x_313_ = ((size_t)0ULL);
v___x_314_ = lean_usize_of_nat(v___x_311_);
v___x_315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_298_, v_tail_305_, v___x_313_, v___x_314_, v___x_310_);
return v___x_315_;
}
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = lean_nat_sub(v_start_301_, v_tailOff_307_);
v___x_317_ = lean_array_get_size(v_tail_305_);
v___x_318_ = lean_nat_dec_lt(v___x_316_, v___x_317_);
if (v___x_318_ == 0)
{
lean_dec(v___x_316_);
lean_dec_ref(v_diagnostic_298_);
return v_init_300_;
}
else
{
size_t v___x_319_; size_t v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_usize_of_nat(v___x_316_);
lean_dec(v___x_316_);
v___x_320_ = lean_usize_of_nat(v___x_317_);
v___x_321_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_298_, v_tail_305_, v___x_319_, v___x_320_, v_init_300_);
return v___x_321_;
}
}
}
else
{
lean_object* v_root_322_; lean_object* v_tail_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_root_322_ = lean_ctor_get(v_t_299_, 0);
v_tail_323_ = lean_ctor_get(v_t_299_, 1);
lean_inc_ref(v_diagnostic_298_);
v___x_324_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_298_, v_root_322_, v_init_300_);
v___x_325_ = lean_array_get_size(v_tail_323_);
v___x_326_ = lean_nat_dec_lt(v___x_302_, v___x_325_);
if (v___x_326_ == 0)
{
lean_dec_ref(v_diagnostic_298_);
return v___x_324_;
}
else
{
size_t v___x_327_; size_t v___x_328_; lean_object* v___x_329_; 
v___x_327_ = ((size_t)0ULL);
v___x_328_ = lean_usize_of_nat(v___x_325_);
v___x_329_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_298_, v_tail_323_, v___x_327_, v___x_328_, v___x_324_);
return v___x_329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0___boxed(lean_object* v_diagnostic_330_, lean_object* v_t_331_, lean_object* v_init_332_, lean_object* v_start_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_330_, v_t_331_, v_init_332_, v_start_333_);
lean_dec(v_start_333_);
lean_dec_ref(v_t_331_);
return v_res_334_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0(void){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_335_ = lean_unsigned_to_nat(32u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
v___x_337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1(void){
_start:
{
size_t v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_338_ = ((size_t)5ULL);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_unsigned_to_nat(32u);
v___x_341_ = lean_mk_empty_array_with_capacity(v___x_340_);
v___x_342_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0);
v___x_343_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
lean_ctor_set(v___x_343_, 2, v___x_339_);
lean_ctor_set(v___x_343_, 3, v___x_339_);
lean_ctor_set_usize(v___x_343_, 4, v___x_338_);
return v___x_343_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(lean_object* v_diagnostic_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___x_347_; lean_object* v_stickyDiagsRef_348_; lean_object* v_diags_349_; lean_object* v_publishedDiagsAmount_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_366_; 
v___x_347_ = lean_st_ref_get(v___y_345_);
v_stickyDiagsRef_348_ = lean_ctor_get(v___x_347_, 0);
v_diags_349_ = lean_ctor_get(v___x_347_, 1);
v_publishedDiagsAmount_350_ = lean_ctor_get(v___x_347_, 2);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_366_ == 0)
{
v___x_352_ = v___x_347_;
v_isShared_353_ = v_isSharedCheck_366_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_publishedDiagsAmount_350_);
lean_inc(v_diags_349_);
lean_inc(v_stickyDiagsRef_348_);
lean_dec(v___x_347_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_366_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v_stickyDiags_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; lean_object* v___x_362_; 
v___x_354_ = lean_st_ref_take(v_stickyDiagsRef_348_);
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
lean_inc_ref(v_diagnostic_344_);
v_stickyDiags_357_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_344_, v___x_354_, v___x_356_, v___x_355_);
lean_dec(v___x_354_);
v___x_358_ = l_Lean_PersistentArray_push___redArg(v_stickyDiags_357_, v_diagnostic_344_);
v___x_359_ = lean_st_ref_put(v_stickyDiagsRef_348_, v___x_358_);
v___x_360_ = 0;
if (v_isShared_353_ == 0)
{
v___x_362_ = v___x_352_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_stickyDiagsRef_348_);
lean_ctor_set(v_reuseFailAlloc_365_, 1, v_diags_349_);
lean_ctor_set(v_reuseFailAlloc_365_, 2, v_publishedDiagsAmount_350_);
v___x_362_ = v_reuseFailAlloc_365_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*3, v___x_360_);
v___x_363_ = lean_box(0);
v___x_364_ = lean_st_ref_swap(v___y_345_, v___x_362_);
lean_dec(v___x_364_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_diagnostic_344_ = stack[0].m_obj;
lean_object* v___y_345_ = stack[1].m_obj;
lean_object* v_res_367_;
v_res_367_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(v_diagnostic_344_, v___y_345_);
stack->m_obj
 = v_res_367_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed(lean_object* v_diagnostic_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(v_diagnostic_368_, v___y_369_);
lean_dec(v___y_369_);
return v_res_371_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(lean_object* v_doc_372_, lean_object* v_diagnostic_373_){
_start:
{
lean_object* v_diagnosticsMutex_375_; lean_object* v___f_376_; lean_object* v___x_377_; 
v_diagnosticsMutex_375_ = lean_ctor_get(v_doc_372_, 3);
lean_inc_ref(v_diagnosticsMutex_375_);
lean_dec_ref(v_doc_372_);
v___f_376_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed), 3, 1);
lean_closure_set(v___f_376_, 0, v_diagnostic_373_);
v___x_377_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_375_, v___f_376_);
return v___x_377_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_372_ = stack[0].m_obj;
lean_object* v_diagnostic_373_ = stack[1].m_obj;
lean_object* v_res_378_;
v_res_378_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(v_doc_372_, v_diagnostic_373_);
stack->m_obj
 = v_res_378_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___boxed(lean_object* v_doc_379_, lean_object* v_diagnostic_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(v_doc_379_, v_diagnostic_380_);
return v_res_382_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(lean_object* v___y_383_){
_start:
{
lean_object* v___x_385_; lean_object* v_stickyDiagsRef_386_; lean_object* v_diags_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_385_ = lean_st_ref_get(v___y_383_);
v_stickyDiagsRef_386_ = lean_ctor_get(v___x_385_, 0);
lean_inc(v_stickyDiagsRef_386_);
v_diags_387_ = lean_ctor_get(v___x_385_, 1);
lean_inc_ref(v_diags_387_);
lean_dec(v___x_385_);
v___x_388_ = lean_st_ref_get(v_stickyDiagsRef_386_);
lean_dec(v_stickyDiagsRef_386_);
v___x_389_ = l_Lean_PersistentArray_append___redArg(v___x_388_, v_diags_387_);
lean_dec_ref(v_diags_387_);
return v___x_389_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_383_ = stack[0].m_obj;
lean_object* v_res_390_;
v_res_390_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(v___y_383_);
stack->m_obj
 = v_res_390_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0___boxed(lean_object* v___y_391_, lean_object* v___y_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(v___y_391_);
lean_dec(v___y_391_);
return v_res_393_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(lean_object* v_doc_395_){
_start:
{
lean_object* v_diagnosticsMutex_397_; lean_object* v___f_398_; lean_object* v___x_399_; 
v_diagnosticsMutex_397_ = lean_ctor_get(v_doc_395_, 3);
lean_inc_ref(v_diagnosticsMutex_397_);
lean_dec_ref(v_doc_395_);
v___f_398_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0));
v___x_399_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_397_, v___f_398_);
return v___x_399_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_395_ = stack[0].m_obj;
lean_object* v_res_400_;
v_res_400_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(v_doc_395_);
stack->m_obj
 = v_res_400_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___boxed(lean_object* v_doc_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(v_doc_401_);
return v_res_403_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(lean_object* v___y_404_){
_start:
{
lean_object* v___x_406_; lean_object* v_stickyDiagsRef_407_; 
v___x_406_ = lean_st_ref_get(v___y_404_);
v_stickyDiagsRef_407_ = lean_ctor_get(v___x_406_, 0);
lean_inc(v_stickyDiagsRef_407_);
lean_dec(v___x_406_);
return v_stickyDiagsRef_407_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_404_ = stack[0].m_obj;
lean_object* v_res_408_;
v_res_408_ = l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(v___y_404_);
stack->m_obj
 = v_res_408_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0___boxed(lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(v___y_409_);
lean_dec(v___y_409_);
return v_res_411_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update(lean_object* v_doc_413_, lean_object* v_newMeta_414_, lean_object* v_newInitSnap_415_){
_start:
{
lean_object* v_diagnosticsMutex_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_432_; 
v_diagnosticsMutex_417_ = lean_ctor_get(v_doc_413_, 3);
v_isSharedCheck_432_ = !lean_is_exclusive(v_doc_413_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; lean_object* v_unused_434_; lean_object* v_unused_435_; 
v_unused_433_ = lean_ctor_get(v_doc_413_, 2);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_doc_413_, 1);
lean_dec(v_unused_434_);
v_unused_435_ = lean_ctor_get(v_doc_413_, 0);
lean_dec(v_unused_435_);
v___x_419_ = v_doc_413_;
v_isShared_420_ = v_isSharedCheck_432_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_diagnosticsMutex_417_);
lean_dec(v_doc_413_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_432_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___f_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___f_421_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0));
v___x_422_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_417_, v___f_421_);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
v___x_425_ = 0;
v___x_426_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_426_, 0, v___x_422_);
lean_ctor_set(v___x_426_, 1, v___x_424_);
lean_ctor_set(v___x_426_, 2, v___x_423_);
lean_ctor_set_uint8(v___x_426_, sizeof(void*)*3, v___x_425_);
v___x_427_ = l_Std_Mutex_new___redArg(v___x_426_);
lean_inc_ref(v_newInitSnap_415_);
v___x_428_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(v_newInitSnap_415_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 3, v___x_427_);
lean_ctor_set(v___x_419_, 2, v___x_428_);
lean_ctor_set(v___x_419_, 1, v_newInitSnap_415_);
lean_ctor_set(v___x_419_, 0, v_newMeta_414_);
v___x_430_ = v___x_419_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_newMeta_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_newInitSnap_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v___x_427_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_update_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_413_ = stack[0].m_obj;
lean_object* v_newMeta_414_ = stack[1].m_obj;
lean_object* v_newInitSnap_415_ = stack[2].m_obj;
lean_object* v_res_436_;
v_res_436_ = l_Lean_Server_FileWorker_EditableDocumentCore_update(v_doc_413_, v_newMeta_414_, v_newInitSnap_415_);
stack->m_obj
 = v_res_436_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___boxed(lean_object* v_doc_437_, lean_object* v_newMeta_438_, lean_object* v_newInitSnap_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Server_FileWorker_EditableDocumentCore_update(v_doc_437_, v_newMeta_438_, v_newInitSnap_439_);
return v_res_441_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(lean_object* v_as_442_, size_t v_i_443_, size_t v_stop_444_, lean_object* v_b_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_eq(v_i_443_, v_stop_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; size_t v___x_450_; size_t v___x_451_; 
v___x_447_ = lean_array_uget_borrowed(v_as_442_, v_i_443_);
lean_inc(v___x_447_);
v___x_448_ = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(v___x_447_);
v___x_449_ = lean_array_push(v_b_445_, v___x_448_);
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_443_, v___x_450_);
v_i_443_ = v___x_451_;
v_b_445_ = v___x_449_;
goto _start;
}
else
{
return v_b_445_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_442_ = stack[0].m_obj;
size_t v_i_443_ = stack[1].m_num;
size_t v_stop_444_ = stack[2].m_num;
lean_object* v_b_445_ = stack[3].m_obj;
lean_object* v_res_453_;
v_res_453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_as_442_, v_i_443_, v_stop_444_, v_b_445_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1___boxed(lean_object* v_as_454_, lean_object* v_i_455_, lean_object* v_stop_456_, lean_object* v_b_457_){
_start:
{
size_t v_i_boxed_458_; size_t v_stop_boxed_459_; lean_object* v_res_460_; 
v_i_boxed_458_ = lean_unbox_usize(v_i_455_);
lean_dec(v_i_455_);
v_stop_boxed_459_ = lean_unbox_usize(v_stop_456_);
lean_dec(v_stop_456_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_as_454_, v_i_boxed_458_, v_stop_boxed_459_, v_b_457_);
lean_dec_ref(v_as_454_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
if (lean_obj_tag(v_x_461_) == 0)
{
lean_object* v_cs_463_; lean_object* v___x_464_; lean_object* v___x_465_; uint8_t v___x_466_; 
v_cs_463_ = lean_ctor_get(v_x_461_, 0);
v___x_464_ = lean_unsigned_to_nat(0u);
v___x_465_ = lean_array_get_size(v_cs_463_);
v___x_466_ = lean_nat_dec_lt(v___x_464_, v___x_465_);
if (v___x_466_ == 0)
{
return v_x_462_;
}
else
{
size_t v___x_467_; size_t v___x_468_; lean_object* v___x_469_; 
v___x_467_ = ((size_t)0ULL);
v___x_468_ = lean_usize_of_nat(v___x_465_);
v___x_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_463_, v___x_467_, v___x_468_, v_x_462_);
return v___x_469_;
}
}
else
{
lean_object* v_vs_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_vs_470_ = lean_ctor_get(v_x_461_, 0);
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_array_get_size(v_vs_470_);
v___x_473_ = lean_nat_dec_lt(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
return v_x_462_;
}
else
{
size_t v___x_474_; size_t v___x_475_; lean_object* v___x_476_; 
v___x_474_ = ((size_t)0ULL);
v___x_475_ = lean_usize_of_nat(v___x_472_);
v___x_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_470_, v___x_474_, v___x_475_, v_x_462_);
return v___x_476_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(lean_object* v_as_477_, size_t v_i_478_, size_t v_stop_479_, lean_object* v_b_480_){
_start:
{
uint8_t v___x_481_; 
v___x_481_ = lean_usize_dec_eq(v_i_478_, v_stop_479_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; size_t v___x_484_; size_t v___x_485_; 
v___x_482_ = lean_array_uget_borrowed(v_as_477_, v_i_478_);
v___x_483_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v___x_482_, v_b_480_);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_add(v_i_478_, v___x_484_);
v_i_478_ = v___x_485_;
v_b_480_ = v___x_483_;
goto _start;
}
else
{
return v_b_480_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_477_ = stack[0].m_obj;
size_t v_i_478_ = stack[1].m_num;
size_t v_stop_479_ = stack[2].m_num;
lean_object* v_b_480_ = stack[3].m_obj;
lean_object* v_res_487_;
v_res_487_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_as_477_, v_i_478_, v_stop_479_, v_b_480_);
stack->m_obj
 = v_res_487_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1___boxed(lean_object* v_as_488_, lean_object* v_i_489_, lean_object* v_stop_490_, lean_object* v_b_491_){
_start:
{
size_t v_i_boxed_492_; size_t v_stop_boxed_493_; lean_object* v_res_494_; 
v_i_boxed_492_ = lean_unbox_usize(v_i_489_);
lean_dec(v_i_489_);
v_stop_boxed_493_ = lean_unbox_usize(v_stop_490_);
lean_dec(v_stop_490_);
v_res_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_as_488_, v_i_boxed_492_, v_stop_boxed_493_, v_b_491_);
lean_dec_ref(v_as_488_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2___boxed(lean_object* v_x_495_, lean_object* v_x_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_x_495_, v_x_496_);
lean_dec_ref(v_x_495_);
return v_res_497_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(lean_object* v_x_498_, size_t v_x_499_, size_t v_x_500_, lean_object* v_x_501_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v_cs_502_; lean_object* v___x_503_; size_t v___x_504_; lean_object* v_j_505_; lean_object* v___x_506_; size_t v___x_507_; size_t v___x_508_; size_t v___x_509_; size_t v___x_510_; size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_cs_502_ = lean_ctor_get(v_x_498_, 0);
v___x_503_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
v___x_504_ = lean_usize_shift_right(v_x_499_, v_x_500_);
v_j_505_ = lean_usize_to_nat(v___x_504_);
v___x_506_ = lean_array_get_borrowed(v___x_503_, v_cs_502_, v_j_505_);
v___x_507_ = ((size_t)1ULL);
v___x_508_ = lean_usize_shift_left(v___x_507_, v_x_500_);
v___x_509_ = lean_usize_sub(v___x_508_, v___x_507_);
v___x_510_ = lean_usize_land(v_x_499_, v___x_509_);
v___x_511_ = ((size_t)5ULL);
v___x_512_ = lean_usize_sub(v_x_500_, v___x_511_);
v___x_513_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v___x_506_, v___x_510_, v___x_512_, v_x_501_);
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_add(v_j_505_, v___x_514_);
lean_dec(v_j_505_);
v___x_516_ = lean_array_get_size(v_cs_502_);
v___x_517_ = lean_nat_dec_lt(v___x_515_, v___x_516_);
if (v___x_517_ == 0)
{
lean_dec(v___x_515_);
return v___x_513_;
}
else
{
size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_usize_of_nat(v___x_515_);
lean_dec(v___x_515_);
v___x_519_ = lean_usize_of_nat(v___x_516_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_502_, v___x_518_, v___x_519_, v___x_513_);
return v___x_520_;
}
}
else
{
lean_object* v_vs_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_vs_521_ = lean_ctor_get(v_x_498_, 0);
v___x_522_ = lean_usize_to_nat(v_x_499_);
v___x_523_ = lean_array_get_size(v_vs_521_);
v___x_524_ = lean_nat_dec_lt(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_dec(v___x_522_);
return v_x_501_;
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_usize_of_nat(v___x_522_);
lean_dec(v___x_522_);
v___x_526_ = lean_usize_of_nat(v___x_523_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_521_, v___x_525_, v___x_526_, v_x_501_);
return v___x_527_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_498_ = stack[0].m_obj;
size_t v_x_499_ = stack[1].m_num;
size_t v_x_500_ = stack[2].m_num;
lean_object* v_x_501_ = stack[3].m_obj;
lean_object* v_res_528_;
v_res_528_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_x_498_, v_x_499_, v_x_500_, v_x_501_);
stack->m_obj
 = v_res_528_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0___boxed(lean_object* v_x_529_, lean_object* v_x_530_, lean_object* v_x_531_, lean_object* v_x_532_){
_start:
{
size_t v_x_2436__boxed_533_; size_t v_x_2437__boxed_534_; lean_object* v_res_535_; 
v_x_2436__boxed_533_ = lean_unbox_usize(v_x_530_);
lean_dec(v_x_530_);
v_x_2437__boxed_534_ = lean_unbox_usize(v_x_531_);
lean_dec(v_x_531_);
v_res_535_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_x_529_, v_x_2436__boxed_533_, v_x_2437__boxed_534_, v_x_532_);
lean_dec_ref(v_x_529_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(lean_object* v_t_536_, lean_object* v_init_537_, lean_object* v_start_538_){
_start:
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_unsigned_to_nat(0u);
v___x_540_ = lean_nat_dec_eq(v_start_538_, v___x_539_);
if (v___x_540_ == 0)
{
lean_object* v_root_541_; lean_object* v_tail_542_; size_t v_shift_543_; lean_object* v_tailOff_544_; uint8_t v___x_545_; 
v_root_541_ = lean_ctor_get(v_t_536_, 0);
v_tail_542_ = lean_ctor_get(v_t_536_, 1);
v_shift_543_ = lean_ctor_get_usize(v_t_536_, 4);
v_tailOff_544_ = lean_ctor_get(v_t_536_, 3);
v___x_545_ = lean_nat_dec_le(v_tailOff_544_, v_start_538_);
if (v___x_545_ == 0)
{
size_t v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_546_ = lean_usize_of_nat(v_start_538_);
v___x_547_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_541_, v___x_546_, v_shift_543_, v_init_537_);
v___x_548_ = lean_array_get_size(v_tail_542_);
v___x_549_ = lean_nat_dec_lt(v___x_539_, v___x_548_);
if (v___x_549_ == 0)
{
return v___x_547_;
}
else
{
size_t v___x_550_; size_t v___x_551_; lean_object* v___x_552_; 
v___x_550_ = ((size_t)0ULL);
v___x_551_ = lean_usize_of_nat(v___x_548_);
v___x_552_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_542_, v___x_550_, v___x_551_, v___x_547_);
return v___x_552_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v___x_553_ = lean_nat_sub(v_start_538_, v_tailOff_544_);
v___x_554_ = lean_array_get_size(v_tail_542_);
v___x_555_ = lean_nat_dec_lt(v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_dec(v___x_553_);
return v_init_537_;
}
else
{
size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_usize_of_nat(v___x_553_);
lean_dec(v___x_553_);
v___x_557_ = lean_usize_of_nat(v___x_554_);
v___x_558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_542_, v___x_556_, v___x_557_, v_init_537_);
return v___x_558_;
}
}
}
else
{
lean_object* v_root_559_; lean_object* v_tail_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_root_559_ = lean_ctor_get(v_t_536_, 0);
v_tail_560_ = lean_ctor_get(v_t_536_, 1);
v___x_561_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_559_, v_init_537_);
v___x_562_ = lean_array_get_size(v_tail_560_);
v___x_563_ = lean_nat_dec_lt(v___x_539_, v___x_562_);
if (v___x_563_ == 0)
{
return v___x_561_;
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_562_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_560_, v___x_564_, v___x_565_, v___x_561_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1___boxed(lean_object* v_t_567_, lean_object* v_init_568_, lean_object* v_start_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_t_567_, v_init_568_, v_start_569_);
lean_dec(v_start_569_);
lean_dec_ref(v_t_567_);
return v_res_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(lean_object* v_t_571_, lean_object* v_init_572_, lean_object* v_start_573_){
_start:
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = lean_nat_dec_eq(v_start_573_, v___x_574_);
if (v___x_575_ == 0)
{
lean_object* v_root_576_; lean_object* v_tail_577_; size_t v_shift_578_; lean_object* v_tailOff_579_; uint8_t v___x_580_; 
v_root_576_ = lean_ctor_get(v_t_571_, 0);
v_tail_577_ = lean_ctor_get(v_t_571_, 1);
v_shift_578_ = lean_ctor_get_usize(v_t_571_, 4);
v_tailOff_579_ = lean_ctor_get(v_t_571_, 3);
v___x_580_ = lean_nat_dec_le(v_tailOff_579_, v_start_573_);
if (v___x_580_ == 0)
{
size_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_581_ = lean_usize_of_nat(v_start_573_);
v___x_582_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_576_, v___x_581_, v_shift_578_, v_init_572_);
v___x_583_ = lean_array_get_size(v_tail_577_);
v___x_584_ = lean_nat_dec_lt(v___x_574_, v___x_583_);
if (v___x_584_ == 0)
{
return v___x_582_;
}
else
{
size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((size_t)0ULL);
v___x_586_ = lean_usize_of_nat(v___x_583_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_577_, v___x_585_, v___x_586_, v___x_582_);
return v___x_587_;
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_nat_sub(v_start_573_, v_tailOff_579_);
v___x_589_ = lean_array_get_size(v_tail_577_);
v___x_590_ = lean_nat_dec_lt(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_dec(v___x_588_);
return v_init_572_;
}
else
{
size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
v___x_591_ = lean_usize_of_nat(v___x_588_);
lean_dec(v___x_588_);
v___x_592_ = lean_usize_of_nat(v___x_589_);
v___x_593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_577_, v___x_591_, v___x_592_, v_init_572_);
return v___x_593_;
}
}
}
else
{
lean_object* v_root_594_; lean_object* v_tail_595_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v_root_594_ = lean_ctor_get(v_t_571_, 0);
v_tail_595_ = lean_ctor_get(v_t_571_, 1);
v___x_596_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_594_, v_init_572_);
v___x_597_ = lean_array_get_size(v_tail_595_);
v___x_598_ = lean_nat_dec_lt(v___x_574_, v___x_597_);
if (v___x_598_ == 0)
{
return v___x_596_;
}
else
{
size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; 
v___x_599_ = ((size_t)0ULL);
v___x_600_ = lean_usize_of_nat(v___x_597_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_595_, v___x_599_, v___x_600_, v___x_596_);
return v___x_601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0___boxed(lean_object* v_t_602_, lean_object* v_init_603_, lean_object* v_start_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_t_602_, v_init_603_, v_start_604_);
lean_dec(v_start_604_);
lean_dec_ref(v_t_602_);
return v_res_605_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(lean_object* v_meta_608_, lean_object* v_writeDiagnostics_609_, uint8_t v_incrementalDiagnosticSupport_610_, lean_object* v___y_611_){
_start:
{
lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v_fst_619_; uint8_t v_snd_620_; lean_object* v___x_624_; uint8_t v___y_626_; 
v___x_624_ = lean_st_ref_get(v___y_611_);
if (v_incrementalDiagnosticSupport_610_ == 0)
{
v___y_626_ = v_incrementalDiagnosticSupport_610_;
goto v___jp_625_;
}
else
{
uint8_t v_isIncremental_647_; 
v_isIncremental_647_ = lean_ctor_get_uint8(v___x_624_, sizeof(void*)*3);
v___y_626_ = v_isIncremental_647_;
goto v___jp_625_;
}
v___jp_613_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = l_Lean_Server_mkPublishDiagnosticsNotification(v_meta_608_, v___y_614_, v___y_615_);
v___x_617_ = lean_apply_2(v_writeDiagnostics_609_, v___x_616_, lean_box(0));
return v___x_617_;
}
v___jp_618_:
{
if (v_incrementalDiagnosticSupport_610_ == 0)
{
lean_object* v___x_621_; 
v___x_621_ = lean_box(0);
v___y_614_ = v_fst_619_;
v___y_615_ = v___x_621_;
goto v___jp_613_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_622_ = lean_box(v_snd_620_);
v___x_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_623_, 0, v___x_622_);
v___y_614_ = v_fst_619_;
v___y_615_ = v___x_623_;
goto v___jp_613_;
}
}
v___jp_625_:
{
lean_object* v_stickyDiagsRef_627_; lean_object* v_diags_628_; lean_object* v_publishedDiagsAmount_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_646_; 
v_stickyDiagsRef_627_ = lean_ctor_get(v___x_624_, 0);
v_diags_628_ = lean_ctor_get(v___x_624_, 1);
v_publishedDiagsAmount_629_ = lean_ctor_get(v___x_624_, 2);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_624_);
if (v_isSharedCheck_646_ == 0)
{
v___x_631_ = v___x_624_;
v_isShared_632_ = v_isSharedCheck_646_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_publishedDiagsAmount_629_);
lean_inc(v_diags_628_);
lean_inc(v_stickyDiagsRef_627_);
lean_dec(v___x_624_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_646_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v___x_633_; lean_object* v_size_634_; uint8_t v___x_635_; lean_object* v___x_637_; 
v___x_633_ = lean_st_ref_get(v_stickyDiagsRef_627_);
v_size_634_ = lean_ctor_get(v_diags_628_, 2);
v___x_635_ = 1;
lean_inc(v_size_634_);
lean_inc_ref(v_diags_628_);
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 2, v_size_634_);
v___x_637_ = v___x_631_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_stickyDiagsRef_627_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_diags_628_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_size_634_);
v___x_637_ = v_reuseFailAlloc_645_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_638_; 
lean_ctor_set_uint8(v___x_637_, sizeof(void*)*3, v___x_635_);
v___x_638_ = lean_st_ref_swap(v___y_611_, v___x_637_);
lean_dec(v___x_638_);
if (v___y_626_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
lean_dec(v_publishedDiagsAmount_629_);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_641_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v___x_633_, v___x_640_, v___x_639_);
lean_dec(v___x_633_);
v___x_642_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_diags_628_, v___x_641_, v___x_639_);
lean_dec_ref(v_diags_628_);
v_fst_619_ = v___x_642_;
v_snd_620_ = v___y_626_;
goto v___jp_618_;
}
else
{
lean_object* v___x_643_; lean_object* v___x_644_; 
lean_dec(v___x_633_);
v___x_643_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_644_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_diags_628_, v___x_643_, v_publishedDiagsAmount_629_);
lean_dec(v_publishedDiagsAmount_629_);
lean_dec_ref(v_diags_628_);
v_fst_619_ = v___x_644_;
v_snd_620_ = v___x_635_;
goto v___jp_618_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_meta_608_ = stack[0].m_obj;
lean_object* v_writeDiagnostics_609_ = stack[1].m_obj;
uint8_t v_incrementalDiagnosticSupport_610_ = stack[2].m_num;
lean_object* v___y_611_ = stack[3].m_obj;
lean_object* v_res_648_;
v_res_648_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(v_meta_608_, v_writeDiagnostics_609_, v_incrementalDiagnosticSupport_610_, v___y_611_);
stack->m_obj
 = v_res_648_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed(lean_object* v_meta_649_, lean_object* v_writeDiagnostics_650_, lean_object* v_incrementalDiagnosticSupport_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_654_; lean_object* v_res_655_; 
v_incrementalDiagnosticSupport_boxed_654_ = lean_unbox(v_incrementalDiagnosticSupport_651_);
v_res_655_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(v_meta_649_, v_writeDiagnostics_650_, v_incrementalDiagnosticSupport_boxed_654_, v___y_652_);
lean_dec(v___y_652_);
return v_res_655_;
}
}
lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(lean_object* v_doc_656_, uint8_t v_incrementalDiagnosticSupport_657_, lean_object* v_writeDiagnostics_658_){
_start:
{
lean_object* v_meta_660_; lean_object* v_diagnosticsMutex_661_; lean_object* v___x_662_; lean_object* v___f_663_; lean_object* v___x_664_; 
v_meta_660_ = lean_ctor_get(v_doc_656_, 0);
lean_inc_ref(v_meta_660_);
v_diagnosticsMutex_661_ = lean_ctor_get(v_doc_656_, 3);
lean_inc_ref(v_diagnosticsMutex_661_);
lean_dec_ref(v_doc_656_);
v___x_662_ = lean_box(v_incrementalDiagnosticSupport_657_);
v___f_663_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed), 5, 3);
lean_closure_set(v___f_663_, 0, v_meta_660_);
lean_closure_set(v___f_663_, 1, v_writeDiagnostics_658_);
lean_closure_set(v___f_663_, 2, v___x_662_);
v___x_664_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_661_, v___f_663_);
return v___x_664_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_0interp(lean_interpreter_value* stack)
{
lean_object* v_doc_656_ = stack[0].m_obj;
uint8_t v_incrementalDiagnosticSupport_657_ = stack[1].m_num;
lean_object* v_writeDiagnostics_658_ = stack[2].m_obj;
lean_object* v_res_665_;
v_res_665_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(v_doc_656_, v_incrementalDiagnosticSupport_657_, v_writeDiagnostics_658_);
stack->m_obj
 = v_res_665_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___boxed(lean_object* v_doc_666_, lean_object* v_incrementalDiagnosticSupport_667_, lean_object* v_writeDiagnostics_668_, lean_object* v_a_669_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_670_; lean_object* v_res_671_; 
v_incrementalDiagnosticSupport_boxed_670_ = lean_unbox(v_incrementalDiagnosticSupport_667_);
v_res_671_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(v_doc_666_, v_incrementalDiagnosticSupport_boxed_670_, v_writeDiagnostics_668_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object* v_ed_672_){
_start:
{
lean_object* v_toEditableDocumentCore_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_684_; 
v_toEditableDocumentCore_673_ = lean_ctor_get(v_ed_672_, 0);
v_isSharedCheck_684_ = !lean_is_exclusive(v_ed_672_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_ed_672_, 1);
lean_dec(v_unused_685_);
v___x_675_ = v_ed_672_;
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_toEditableDocumentCore_673_);
lean_dec(v_ed_672_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_684_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v_meta_677_; lean_object* v_uri_678_; lean_object* v_version_679_; lean_object* v___x_680_; lean_object* v___x_682_; 
v_meta_677_ = lean_ctor_get(v_toEditableDocumentCore_673_, 0);
lean_inc_ref(v_meta_677_);
lean_dec_ref(v_toEditableDocumentCore_673_);
v_uri_678_ = lean_ctor_get(v_meta_677_, 0);
lean_inc_ref(v_uri_678_);
v_version_679_ = lean_ctor_get(v_meta_677_, 2);
lean_inc(v_version_679_);
lean_dec_ref(v_meta_677_);
v___x_680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_680_, 0, v_version_679_);
if (v_isShared_676_ == 0)
{
lean_ctor_set(v___x_675_, 1, v___x_680_);
lean_ctor_set(v___x_675_, 0, v_uri_678_);
v___x_682_ = v___x_675_;
goto v_reusejp_681_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_uri_678_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v___x_680_);
v___x_682_ = v_reuseFailAlloc_683_;
goto v_reusejp_681_;
}
v_reusejp_681_:
{
return v___x_682_;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs(void){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = lean_unsigned_to_nat(30000u);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0(void){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_687_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1(void){
_start:
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__0, &l_Lean_Server_FileWorker_RpcSession_new___closed__0_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
}
lean_object* l_Lean_Server_FileWorker_RpcSession_new(uint8_t v_wireFormat_690_){
_start:
{
size_t v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((size_t)8ULL);
v___x_693_ = lean_io_get_random_bytes(v___x_692_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_711_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_711_ == 0)
{
v___x_696_ = v___x_693_;
v_isShared_697_ = v_isSharedCheck_711_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_693_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_711_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
uint64_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; size_t v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_698_ = l_ByteArray_toUInt64LE_x21(v_a_694_);
lean_dec(v_a_694_);
v___x_699_ = lean_io_mono_ms_now();
v___x_700_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__1, &l_Lean_Server_FileWorker_RpcSession_new___closed__1_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1);
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_702_, 0, v___x_700_);
lean_ctor_set(v___x_702_, 1, v___x_700_);
lean_ctor_set_usize(v___x_702_, 2, v___x_701_);
lean_ctor_set_uint8(v___x_702_, sizeof(void*)*3, v_wireFormat_690_);
v___x_703_ = lean_unsigned_to_nat(30000u);
v___x_704_ = lean_nat_add(v___x_699_, v___x_703_);
lean_dec(v___x_699_);
v___x_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_705_, 0, v___x_702_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___x_706_ = lean_box_uint64(v___x_698_);
v___x_707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_706_);
lean_ctor_set(v___x_707_, 1, v___x_705_);
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 0, v___x_707_);
v___x_709_ = v___x_696_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v___x_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
v_a_712_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_693_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_693_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_RpcSession_new_0interp(lean_interpreter_value* stack)
{
uint8_t v_wireFormat_690_ = stack[0].m_num;
lean_object* v_res_720_;
v_res_720_ = l_Lean_Server_FileWorker_RpcSession_new(v_wireFormat_690_);
stack->m_obj
 = v_res_720_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new___boxed(lean_object* v_wireFormat_721_, lean_object* v_a_722_){
_start:
{
uint8_t v_wireFormat_boxed_723_; lean_object* v_res_724_; 
v_wireFormat_boxed_723_ = lean_unbox(v_wireFormat_721_);
v_res_724_ = l_Lean_Server_FileWorker_RpcSession_new(v_wireFormat_boxed_723_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object* v_monoMsNow_725_, lean_object* v_s_726_){
_start:
{
lean_object* v_objects_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_736_; 
v_objects_727_ = lean_ctor_get(v_s_726_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_s_726_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v_s_726_, 1);
lean_dec(v_unused_737_);
v___x_729_ = v_s_726_;
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_objects_727_);
lean_dec(v_s_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_736_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_731_ = lean_unsigned_to_nat(30000u);
v___x_732_ = lean_nat_add(v_monoMsNow_725_, v___x_731_);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_732_);
v___x_734_ = v___x_729_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_objects_727_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object* v_monoMsNow_738_, lean_object* v_s_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Lean_Server_FileWorker_RpcSession_keptAlive(v_monoMsNow_738_, v_s_739_);
lean_dec(v_monoMsNow_738_);
return v_res_740_;
}
}
lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object* v_s_741_){
_start:
{
lean_object* v___x_743_; lean_object* v_expireTime_744_; uint8_t v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_743_ = lean_io_mono_ms_now();
v_expireTime_744_ = lean_ctor_get(v_s_741_, 1);
v___x_745_ = lean_nat_dec_le(v_expireTime_744_, v___x_743_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(v___x_745_);
v___x_747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
return v___x_747_;
}
}
LEAN_EXPORT void l_Lean_Server_FileWorker_RpcSession_hasExpired_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_741_ = stack[0].m_obj;
lean_object* v_res_748_;
v_res_748_ = l_Lean_Server_FileWorker_RpcSession_hasExpired(v_s_741_);
stack->m_obj
 = v_res_748_;
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object* v_s_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Lean_Server_FileWorker_RpcSession_hasExpired(v_s_749_);
lean_dec_ref(v_s_749_);
return v_res_751_;
}
}
lean_object* runtime_initialize_Lean_Language_Lean_Types(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_Snapshots(uint8_t builtin);
lean_object* runtime_initialize_Lean_Server_AsyncList(uint8_t builtin);
lean_object* runtime_initialize_Std_Sync_Mutex(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
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
res = runtime_initialize_Init_Data_ByteArray_Extra(builtin);
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
lean_object* initialize_Init_Data_ByteArray_Extra(uint8_t builtin);
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
res = initialize_Init_Data_ByteArray_Extra(builtin);
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
