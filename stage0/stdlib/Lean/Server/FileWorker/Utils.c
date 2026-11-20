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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* v___x_144_; lean_object* v_stickyDiagsRef_145_; lean_object* v_diags_146_; uint8_t v_isIncremental_147_; lean_object* v_publishedDiagsAmount_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_165_; 
v___x_144_ = lean_st_ref_take(v___y_142_);
v_stickyDiagsRef_145_ = lean_ctor_get(v___x_144_, 0);
v_diags_146_ = lean_ctor_get(v___x_144_, 1);
v_isIncremental_147_ = lean_ctor_get_uint8(v___x_144_, sizeof(void*)*3);
v_publishedDiagsAmount_148_ = lean_ctor_get(v___x_144_, 2);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_165_ == 0)
{
v___x_150_ = v___x_144_;
v_isShared_151_ = v_isSharedCheck_165_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_publishedDiagsAmount_148_);
lean_inc(v_diags_146_);
lean_inc(v_stickyDiagsRef_145_);
lean_dec(v___x_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_165_;
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
size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; 
v___x_162_ = ((size_t)0ULL);
v___x_163_ = lean_usize_of_nat(v___x_160_);
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_diags_141_, v___x_162_, v___x_163_, v_diags_146_);
v___y_154_ = v___x_164_;
goto v___jp_153_;
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
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed(lean_object* v_diags_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(v_diags_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v_diags_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(lean_object* v_doc_170_, lean_object* v_diags_171_){
_start:
{
lean_object* v_diagnosticsMutex_173_; lean_object* v___f_174_; lean_object* v___x_175_; 
v_diagnosticsMutex_173_ = lean_ctor_get(v_doc_170_, 3);
lean_inc_ref(v_diagnosticsMutex_173_);
lean_dec_ref(v_doc_170_);
v___f_174_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed), 3, 1);
lean_closure_set(v___f_174_, 0, v_diags_171_);
v___x_175_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_173_, v___f_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___boxed(lean_object* v_doc_176_, lean_object* v_diags_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(v_doc_176_, v_diags_177_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(lean_object* v_diagnostic_180_, lean_object* v_as_181_, size_t v_i_182_, size_t v_stop_183_, lean_object* v_b_184_){
_start:
{
lean_object* v___y_186_; uint8_t v___x_190_; 
v___x_190_ = lean_usize_dec_eq(v_i_182_, v_stop_183_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v_message_192_; lean_object* v_message_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_191_ = lean_array_uget_borrowed(v_as_181_, v_i_182_);
v_message_192_ = lean_ctor_get(v___x_191_, 6);
v_message_193_ = lean_ctor_get(v_diagnostic_180_, 6);
lean_inc(v_message_192_);
v___x_194_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_192_);
lean_inc(v_message_193_);
v___x_195_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_193_);
v___x_196_ = lean_string_dec_eq(v___x_194_, v___x_195_);
lean_dec_ref(v___x_195_);
lean_dec_ref(v___x_194_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_inc(v___x_191_);
v___x_197_ = l_Lean_PersistentArray_push___redArg(v_b_184_, v___x_191_);
v___y_186_ = v___x_197_;
goto v___jp_185_;
}
else
{
v___y_186_ = v_b_184_;
goto v___jp_185_;
}
}
else
{
lean_dec_ref(v_diagnostic_180_);
return v_b_184_;
}
v___jp_185_:
{
size_t v___x_187_; size_t v___x_188_; 
v___x_187_ = ((size_t)1ULL);
v___x_188_ = lean_usize_add(v_i_182_, v___x_187_);
v_i_182_ = v___x_188_;
v_b_184_ = v___y_186_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1___boxed(lean_object* v_diagnostic_198_, lean_object* v_as_199_, lean_object* v_i_200_, lean_object* v_stop_201_, lean_object* v_b_202_){
_start:
{
size_t v_i_boxed_203_; size_t v_stop_boxed_204_; lean_object* v_res_205_; 
v_i_boxed_203_ = lean_unbox_usize(v_i_200_);
lean_dec(v_i_200_);
v_stop_boxed_204_ = lean_unbox_usize(v_stop_201_);
lean_dec(v_stop_201_);
v_res_205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_198_, v_as_199_, v_i_boxed_203_, v_stop_boxed_204_, v_b_202_);
lean_dec_ref(v_as_199_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(lean_object* v_diagnostic_206_, lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
if (lean_obj_tag(v_x_207_) == 0)
{
lean_object* v_cs_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_cs_209_ = lean_ctor_get(v_x_207_, 0);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_array_get_size(v_cs_209_);
v___x_212_ = lean_nat_dec_lt(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_dec_ref(v_diagnostic_206_);
return v_x_208_;
}
else
{
size_t v___x_213_; size_t v___x_214_; lean_object* v___x_215_; 
v___x_213_ = ((size_t)0ULL);
v___x_214_ = lean_usize_of_nat(v___x_211_);
v___x_215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_206_, v_cs_209_, v___x_213_, v___x_214_, v_x_208_);
return v___x_215_;
}
}
else
{
lean_object* v_vs_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v_vs_216_ = lean_ctor_get(v_x_207_, 0);
v___x_217_ = lean_unsigned_to_nat(0u);
v___x_218_ = lean_array_get_size(v_vs_216_);
v___x_219_ = lean_nat_dec_lt(v___x_217_, v___x_218_);
if (v___x_219_ == 0)
{
lean_dec_ref(v_diagnostic_206_);
return v_x_208_;
}
else
{
size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; 
v___x_220_ = ((size_t)0ULL);
v___x_221_ = lean_usize_of_nat(v___x_218_);
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_206_, v_vs_216_, v___x_220_, v___x_221_, v_x_208_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(lean_object* v_diagnostic_223_, lean_object* v_as_224_, size_t v_i_225_, size_t v_stop_226_, lean_object* v_b_227_){
_start:
{
uint8_t v___x_228_; 
v___x_228_ = lean_usize_dec_eq(v_i_225_, v_stop_226_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; lean_object* v___x_230_; size_t v___x_231_; size_t v___x_232_; 
v___x_229_ = lean_array_uget_borrowed(v_as_224_, v_i_225_);
lean_inc_ref(v_diagnostic_223_);
v___x_230_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_223_, v___x_229_, v_b_227_);
v___x_231_ = ((size_t)1ULL);
v___x_232_ = lean_usize_add(v_i_225_, v___x_231_);
v_i_225_ = v___x_232_;
v_b_227_ = v___x_230_;
goto _start;
}
else
{
lean_dec_ref(v_diagnostic_223_);
return v_b_227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1___boxed(lean_object* v_diagnostic_234_, lean_object* v_as_235_, lean_object* v_i_236_, lean_object* v_stop_237_, lean_object* v_b_238_){
_start:
{
size_t v_i_boxed_239_; size_t v_stop_boxed_240_; lean_object* v_res_241_; 
v_i_boxed_239_ = lean_unbox_usize(v_i_236_);
lean_dec(v_i_236_);
v_stop_boxed_240_ = lean_unbox_usize(v_stop_237_);
lean_dec(v_stop_237_);
v_res_241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_234_, v_as_235_, v_i_boxed_239_, v_stop_boxed_240_, v_b_238_);
lean_dec_ref(v_as_235_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2___boxed(lean_object* v_diagnostic_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_242_, v_x_243_, v_x_244_);
lean_dec_ref(v_x_243_);
return v_res_245_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(lean_object* v_diagnostic_247_, lean_object* v_x_248_, size_t v_x_249_, size_t v_x_250_, lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v_cs_252_; lean_object* v___x_253_; size_t v___x_254_; lean_object* v_j_255_; lean_object* v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v_cs_252_ = lean_ctor_get(v_x_248_, 0);
v___x_253_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
v___x_254_ = lean_usize_shift_right(v_x_249_, v_x_250_);
v_j_255_ = lean_usize_to_nat(v___x_254_);
v___x_256_ = lean_array_get_borrowed(v___x_253_, v_cs_252_, v_j_255_);
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_shift_left(v___x_257_, v_x_250_);
v___x_259_ = lean_usize_sub(v___x_258_, v___x_257_);
v___x_260_ = lean_usize_land(v_x_249_, v___x_259_);
v___x_261_ = ((size_t)5ULL);
v___x_262_ = lean_usize_sub(v_x_250_, v___x_261_);
lean_inc_ref(v_diagnostic_247_);
v___x_263_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_247_, v___x_256_, v___x_260_, v___x_262_, v_x_251_);
v___x_264_ = lean_unsigned_to_nat(1u);
v___x_265_ = lean_nat_add(v_j_255_, v___x_264_);
lean_dec(v_j_255_);
v___x_266_ = lean_array_get_size(v_cs_252_);
v___x_267_ = lean_nat_dec_lt(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_dec(v___x_265_);
lean_dec_ref(v_diagnostic_247_);
return v___x_263_;
}
else
{
size_t v___x_268_; size_t v___x_269_; lean_object* v___x_270_; 
v___x_268_ = lean_usize_of_nat(v___x_265_);
lean_dec(v___x_265_);
v___x_269_ = lean_usize_of_nat(v___x_266_);
v___x_270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_247_, v_cs_252_, v___x_268_, v___x_269_, v___x_263_);
return v___x_270_;
}
}
else
{
lean_object* v_vs_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_vs_271_ = lean_ctor_get(v_x_248_, 0);
v___x_272_ = lean_usize_to_nat(v_x_249_);
v___x_273_ = lean_array_get_size(v_vs_271_);
v___x_274_ = lean_nat_dec_lt(v___x_272_, v___x_273_);
if (v___x_274_ == 0)
{
lean_dec(v___x_272_);
lean_dec_ref(v_diagnostic_247_);
return v_x_251_;
}
else
{
size_t v___x_275_; size_t v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_usize_of_nat(v___x_272_);
lean_dec(v___x_272_);
v___x_276_ = lean_usize_of_nat(v___x_273_);
v___x_277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_247_, v_vs_271_, v___x_275_, v___x_276_, v_x_251_);
return v___x_277_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___boxed(lean_object* v_diagnostic_278_, lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_x_281_, lean_object* v_x_282_){
_start:
{
size_t v_x_1612__boxed_283_; size_t v_x_1613__boxed_284_; lean_object* v_res_285_; 
v_x_1612__boxed_283_ = lean_unbox_usize(v_x_280_);
lean_dec(v_x_280_);
v_x_1613__boxed_284_ = lean_unbox_usize(v_x_281_);
lean_dec(v_x_281_);
v_res_285_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_278_, v_x_279_, v_x_1612__boxed_283_, v_x_1613__boxed_284_, v_x_282_);
lean_dec_ref(v_x_279_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(lean_object* v_diagnostic_286_, lean_object* v_t_287_, lean_object* v_init_288_, lean_object* v_start_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_290_ = lean_unsigned_to_nat(0u);
v___x_291_ = lean_nat_dec_eq(v_start_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v_root_292_; lean_object* v_tail_293_; size_t v_shift_294_; lean_object* v_tailOff_295_; uint8_t v___x_296_; 
v_root_292_ = lean_ctor_get(v_t_287_, 0);
v_tail_293_ = lean_ctor_get(v_t_287_, 1);
v_shift_294_ = lean_ctor_get_usize(v_t_287_, 4);
v_tailOff_295_ = lean_ctor_get(v_t_287_, 3);
v___x_296_ = lean_nat_dec_le(v_tailOff_295_, v_start_289_);
if (v___x_296_ == 0)
{
size_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_297_ = lean_usize_of_nat(v_start_289_);
lean_inc_ref(v_diagnostic_286_);
v___x_298_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_286_, v_root_292_, v___x_297_, v_shift_294_, v_init_288_);
v___x_299_ = lean_array_get_size(v_tail_293_);
v___x_300_ = lean_nat_dec_lt(v___x_290_, v___x_299_);
if (v___x_300_ == 0)
{
lean_dec_ref(v_diagnostic_286_);
return v___x_298_;
}
else
{
size_t v___x_301_; size_t v___x_302_; lean_object* v___x_303_; 
v___x_301_ = ((size_t)0ULL);
v___x_302_ = lean_usize_of_nat(v___x_299_);
v___x_303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_286_, v_tail_293_, v___x_301_, v___x_302_, v___x_298_);
return v___x_303_;
}
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_nat_sub(v_start_289_, v_tailOff_295_);
v___x_305_ = lean_array_get_size(v_tail_293_);
v___x_306_ = lean_nat_dec_lt(v___x_304_, v___x_305_);
if (v___x_306_ == 0)
{
lean_dec(v___x_304_);
lean_dec_ref(v_diagnostic_286_);
return v_init_288_;
}
else
{
size_t v___x_307_; size_t v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_usize_of_nat(v___x_304_);
lean_dec(v___x_304_);
v___x_308_ = lean_usize_of_nat(v___x_305_);
v___x_309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_286_, v_tail_293_, v___x_307_, v___x_308_, v_init_288_);
return v___x_309_;
}
}
}
else
{
lean_object* v_root_310_; lean_object* v_tail_311_; lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v_root_310_ = lean_ctor_get(v_t_287_, 0);
v_tail_311_ = lean_ctor_get(v_t_287_, 1);
lean_inc_ref(v_diagnostic_286_);
v___x_312_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_286_, v_root_310_, v_init_288_);
v___x_313_ = lean_array_get_size(v_tail_311_);
v___x_314_ = lean_nat_dec_lt(v___x_290_, v___x_313_);
if (v___x_314_ == 0)
{
lean_dec_ref(v_diagnostic_286_);
return v___x_312_;
}
else
{
size_t v___x_315_; size_t v___x_316_; lean_object* v___x_317_; 
v___x_315_ = ((size_t)0ULL);
v___x_316_ = lean_usize_of_nat(v___x_313_);
v___x_317_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_286_, v_tail_311_, v___x_315_, v___x_316_, v___x_312_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0___boxed(lean_object* v_diagnostic_318_, lean_object* v_t_319_, lean_object* v_init_320_, lean_object* v_start_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_318_, v_t_319_, v_init_320_, v_start_321_);
lean_dec(v_start_321_);
lean_dec_ref(v_t_319_);
return v_res_322_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_unsigned_to_nat(32u);
v___x_324_ = lean_mk_empty_array_with_capacity(v___x_323_);
v___x_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1(void){
_start:
{
size_t v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_326_ = ((size_t)5ULL);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_unsigned_to_nat(32u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0);
v___x_331_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
lean_ctor_set(v___x_331_, 2, v___x_327_);
lean_ctor_set(v___x_331_, 3, v___x_327_);
lean_ctor_set_usize(v___x_331_, 4, v___x_326_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(lean_object* v_diagnostic_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; lean_object* v_stickyDiagsRef_336_; lean_object* v_diags_337_; lean_object* v_publishedDiagsAmount_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_354_; 
v___x_335_ = lean_st_ref_get(v___y_333_);
v_stickyDiagsRef_336_ = lean_ctor_get(v___x_335_, 0);
v_diags_337_ = lean_ctor_get(v___x_335_, 1);
v_publishedDiagsAmount_338_ = lean_ctor_get(v___x_335_, 2);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_335_);
if (v_isSharedCheck_354_ == 0)
{
v___x_340_ = v___x_335_;
v_isShared_341_ = v_isSharedCheck_354_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_publishedDiagsAmount_338_);
lean_inc(v_diags_337_);
lean_inc(v_stickyDiagsRef_336_);
lean_dec(v___x_335_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_354_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v_stickyDiags_345_; lean_object* v___x_346_; lean_object* v___x_347_; uint8_t v___x_348_; lean_object* v___x_350_; 
v___x_342_ = lean_st_ref_take(v_stickyDiagsRef_336_);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
lean_inc_ref(v_diagnostic_332_);
v_stickyDiags_345_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_332_, v___x_342_, v___x_344_, v___x_343_);
lean_dec(v___x_342_);
v___x_346_ = l_Lean_PersistentArray_push___redArg(v_stickyDiags_345_, v_diagnostic_332_);
v___x_347_ = lean_st_ref_put(v_stickyDiagsRef_336_, v___x_346_);
v___x_348_ = 0;
if (v_isShared_341_ == 0)
{
v___x_350_ = v___x_340_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_353_; 
v_reuseFailAlloc_353_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_353_, 0, v_stickyDiagsRef_336_);
lean_ctor_set(v_reuseFailAlloc_353_, 1, v_diags_337_);
lean_ctor_set(v_reuseFailAlloc_353_, 2, v_publishedDiagsAmount_338_);
v___x_350_ = v_reuseFailAlloc_353_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_ctor_set_uint8(v___x_350_, sizeof(void*)*3, v___x_348_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_st_ref_swap(v___y_333_, v___x_350_);
lean_dec(v___x_352_);
return v___x_351_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed(lean_object* v_diagnostic_355_, lean_object* v___y_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(v_diagnostic_355_, v___y_356_);
lean_dec(v___y_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(lean_object* v_doc_359_, lean_object* v_diagnostic_360_){
_start:
{
lean_object* v_diagnosticsMutex_362_; lean_object* v___f_363_; lean_object* v___x_364_; 
v_diagnosticsMutex_362_ = lean_ctor_get(v_doc_359_, 3);
lean_inc_ref(v_diagnosticsMutex_362_);
lean_dec_ref(v_doc_359_);
v___f_363_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed), 3, 1);
lean_closure_set(v___f_363_, 0, v_diagnostic_360_);
v___x_364_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_362_, v___f_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___boxed(lean_object* v_doc_365_, lean_object* v_diagnostic_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(v_doc_365_, v_diagnostic_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(lean_object* v___y_369_){
_start:
{
lean_object* v___x_371_; lean_object* v_stickyDiagsRef_372_; lean_object* v_diags_373_; lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_371_ = lean_st_ref_get(v___y_369_);
v_stickyDiagsRef_372_ = lean_ctor_get(v___x_371_, 0);
lean_inc(v_stickyDiagsRef_372_);
v_diags_373_ = lean_ctor_get(v___x_371_, 1);
lean_inc_ref(v_diags_373_);
lean_dec(v___x_371_);
v___x_374_ = lean_st_ref_get(v_stickyDiagsRef_372_);
lean_dec(v_stickyDiagsRef_372_);
v___x_375_ = l_Lean_PersistentArray_append___redArg(v___x_374_, v_diags_373_);
lean_dec_ref(v_diags_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0___boxed(lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(v___y_376_);
lean_dec(v___y_376_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(lean_object* v_doc_380_){
_start:
{
lean_object* v_diagnosticsMutex_382_; lean_object* v___f_383_; lean_object* v___x_384_; 
v_diagnosticsMutex_382_ = lean_ctor_get(v_doc_380_, 3);
lean_inc_ref(v_diagnosticsMutex_382_);
lean_dec_ref(v_doc_380_);
v___f_383_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0));
v___x_384_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_382_, v___f_383_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___boxed(lean_object* v_doc_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(v_doc_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_stickyDiagsRef_391_; 
v___x_390_ = lean_st_ref_get(v___y_388_);
v_stickyDiagsRef_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_stickyDiagsRef_391_);
lean_dec(v___x_390_);
return v_stickyDiagsRef_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0___boxed(lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(v___y_392_);
lean_dec(v___y_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update(lean_object* v_doc_396_, lean_object* v_newMeta_397_, lean_object* v_newInitSnap_398_){
_start:
{
lean_object* v_diagnosticsMutex_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_415_; 
v_diagnosticsMutex_400_ = lean_ctor_get(v_doc_396_, 3);
v_isSharedCheck_415_ = !lean_is_exclusive(v_doc_396_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; lean_object* v_unused_417_; lean_object* v_unused_418_; 
v_unused_416_ = lean_ctor_get(v_doc_396_, 2);
lean_dec(v_unused_416_);
v_unused_417_ = lean_ctor_get(v_doc_396_, 1);
lean_dec(v_unused_417_);
v_unused_418_ = lean_ctor_get(v_doc_396_, 0);
lean_dec(v_unused_418_);
v___x_402_ = v_doc_396_;
v_isShared_403_ = v_isSharedCheck_415_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_diagnosticsMutex_400_);
lean_dec(v_doc_396_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_415_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_413_; 
v___f_404_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0));
v___x_405_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_400_, v___f_404_);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
v___x_408_ = 0;
v___x_409_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_409_, 0, v___x_405_);
lean_ctor_set(v___x_409_, 1, v___x_407_);
lean_ctor_set(v___x_409_, 2, v___x_406_);
lean_ctor_set_uint8(v___x_409_, sizeof(void*)*3, v___x_408_);
v___x_410_ = l_Std_Mutex_new___redArg(v___x_409_);
lean_inc_ref(v_newInitSnap_398_);
v___x_411_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(v_newInitSnap_398_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 3, v___x_410_);
lean_ctor_set(v___x_402_, 2, v___x_411_);
lean_ctor_set(v___x_402_, 1, v_newInitSnap_398_);
lean_ctor_set(v___x_402_, 0, v_newMeta_397_);
v___x_413_ = v___x_402_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_newMeta_397_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_newInitSnap_398_);
lean_ctor_set(v_reuseFailAlloc_414_, 2, v___x_411_);
lean_ctor_set(v_reuseFailAlloc_414_, 3, v___x_410_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___boxed(lean_object* v_doc_419_, lean_object* v_newMeta_420_, lean_object* v_newInitSnap_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Server_FileWorker_EditableDocumentCore_update(v_doc_419_, v_newMeta_420_, v_newInitSnap_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(lean_object* v_as_424_, size_t v_i_425_, size_t v_stop_426_, lean_object* v_b_427_){
_start:
{
uint8_t v___x_428_; 
v___x_428_ = lean_usize_dec_eq(v_i_425_, v_stop_426_);
if (v___x_428_ == 0)
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; size_t v___x_432_; size_t v___x_433_; 
v___x_429_ = lean_array_uget_borrowed(v_as_424_, v_i_425_);
lean_inc(v___x_429_);
v___x_430_ = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(v___x_429_);
v___x_431_ = lean_array_push(v_b_427_, v___x_430_);
v___x_432_ = ((size_t)1ULL);
v___x_433_ = lean_usize_add(v_i_425_, v___x_432_);
v_i_425_ = v___x_433_;
v_b_427_ = v___x_431_;
goto _start;
}
else
{
return v_b_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1___boxed(lean_object* v_as_435_, lean_object* v_i_436_, lean_object* v_stop_437_, lean_object* v_b_438_){
_start:
{
size_t v_i_boxed_439_; size_t v_stop_boxed_440_; lean_object* v_res_441_; 
v_i_boxed_439_ = lean_unbox_usize(v_i_436_);
lean_dec(v_i_436_);
v_stop_boxed_440_ = lean_unbox_usize(v_stop_437_);
lean_dec(v_stop_437_);
v_res_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_as_435_, v_i_boxed_439_, v_stop_boxed_440_, v_b_438_);
lean_dec_ref(v_as_435_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
if (lean_obj_tag(v_x_442_) == 0)
{
lean_object* v_cs_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_cs_444_ = lean_ctor_get(v_x_442_, 0);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_array_get_size(v_cs_444_);
v___x_447_ = lean_nat_dec_lt(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
return v_x_443_;
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_446_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_444_, v___x_448_, v___x_449_, v_x_443_);
return v___x_450_;
}
}
else
{
lean_object* v_vs_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_vs_451_ = lean_ctor_get(v_x_442_, 0);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_array_get_size(v_vs_451_);
v___x_454_ = lean_nat_dec_lt(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
return v_x_443_;
}
else
{
size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; 
v___x_455_ = ((size_t)0ULL);
v___x_456_ = lean_usize_of_nat(v___x_453_);
v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_451_, v___x_455_, v___x_456_, v_x_443_);
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(lean_object* v_as_458_, size_t v_i_459_, size_t v_stop_460_, lean_object* v_b_461_){
_start:
{
uint8_t v___x_462_; 
v___x_462_ = lean_usize_dec_eq(v_i_459_, v_stop_460_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; size_t v___x_465_; size_t v___x_466_; 
v___x_463_ = lean_array_uget_borrowed(v_as_458_, v_i_459_);
v___x_464_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v___x_463_, v_b_461_);
v___x_465_ = ((size_t)1ULL);
v___x_466_ = lean_usize_add(v_i_459_, v___x_465_);
v_i_459_ = v___x_466_;
v_b_461_ = v___x_464_;
goto _start;
}
else
{
return v_b_461_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1___boxed(lean_object* v_as_468_, lean_object* v_i_469_, lean_object* v_stop_470_, lean_object* v_b_471_){
_start:
{
size_t v_i_boxed_472_; size_t v_stop_boxed_473_; lean_object* v_res_474_; 
v_i_boxed_472_ = lean_unbox_usize(v_i_469_);
lean_dec(v_i_469_);
v_stop_boxed_473_ = lean_unbox_usize(v_stop_470_);
lean_dec(v_stop_470_);
v_res_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_as_468_, v_i_boxed_472_, v_stop_boxed_473_, v_b_471_);
lean_dec_ref(v_as_468_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2___boxed(lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_x_475_, v_x_476_);
lean_dec_ref(v_x_475_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(lean_object* v_x_478_, size_t v_x_479_, size_t v_x_480_, lean_object* v_x_481_){
_start:
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_object* v_cs_482_; lean_object* v___x_483_; size_t v___x_484_; lean_object* v_j_485_; lean_object* v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v_cs_482_ = lean_ctor_get(v_x_478_, 0);
v___x_483_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
v___x_484_ = lean_usize_shift_right(v_x_479_, v_x_480_);
v_j_485_ = lean_usize_to_nat(v___x_484_);
v___x_486_ = lean_array_get_borrowed(v___x_483_, v_cs_482_, v_j_485_);
v___x_487_ = ((size_t)1ULL);
v___x_488_ = lean_usize_shift_left(v___x_487_, v_x_480_);
v___x_489_ = lean_usize_sub(v___x_488_, v___x_487_);
v___x_490_ = lean_usize_land(v_x_479_, v___x_489_);
v___x_491_ = ((size_t)5ULL);
v___x_492_ = lean_usize_sub(v_x_480_, v___x_491_);
v___x_493_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v___x_486_, v___x_490_, v___x_492_, v_x_481_);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_add(v_j_485_, v___x_494_);
lean_dec(v_j_485_);
v___x_496_ = lean_array_get_size(v_cs_482_);
v___x_497_ = lean_nat_dec_lt(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_dec(v___x_495_);
return v___x_493_;
}
else
{
size_t v___x_498_; size_t v___x_499_; lean_object* v___x_500_; 
v___x_498_ = lean_usize_of_nat(v___x_495_);
lean_dec(v___x_495_);
v___x_499_ = lean_usize_of_nat(v___x_496_);
v___x_500_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_482_, v___x_498_, v___x_499_, v___x_493_);
return v___x_500_;
}
}
else
{
lean_object* v_vs_501_; lean_object* v___x_502_; lean_object* v___x_503_; uint8_t v___x_504_; 
v_vs_501_ = lean_ctor_get(v_x_478_, 0);
v___x_502_ = lean_usize_to_nat(v_x_479_);
v___x_503_ = lean_array_get_size(v_vs_501_);
v___x_504_ = lean_nat_dec_lt(v___x_502_, v___x_503_);
if (v___x_504_ == 0)
{
lean_dec(v___x_502_);
return v_x_481_;
}
else
{
size_t v___x_505_; size_t v___x_506_; lean_object* v___x_507_; 
v___x_505_ = lean_usize_of_nat(v___x_502_);
lean_dec(v___x_502_);
v___x_506_ = lean_usize_of_nat(v___x_503_);
v___x_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_501_, v___x_505_, v___x_506_, v_x_481_);
return v___x_507_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0___boxed(lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
size_t v_x_2405__boxed_512_; size_t v_x_2406__boxed_513_; lean_object* v_res_514_; 
v_x_2405__boxed_512_ = lean_unbox_usize(v_x_509_);
lean_dec(v_x_509_);
v_x_2406__boxed_513_ = lean_unbox_usize(v_x_510_);
lean_dec(v_x_510_);
v_res_514_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_x_508_, v_x_2405__boxed_512_, v_x_2406__boxed_513_, v_x_511_);
lean_dec_ref(v_x_508_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(lean_object* v_t_515_, lean_object* v_init_516_, lean_object* v_start_517_){
_start:
{
lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(0u);
v___x_519_ = lean_nat_dec_eq(v_start_517_, v___x_518_);
if (v___x_519_ == 0)
{
lean_object* v_root_520_; lean_object* v_tail_521_; size_t v_shift_522_; lean_object* v_tailOff_523_; uint8_t v___x_524_; 
v_root_520_ = lean_ctor_get(v_t_515_, 0);
v_tail_521_ = lean_ctor_get(v_t_515_, 1);
v_shift_522_ = lean_ctor_get_usize(v_t_515_, 4);
v_tailOff_523_ = lean_ctor_get(v_t_515_, 3);
v___x_524_ = lean_nat_dec_le(v_tailOff_523_, v_start_517_);
if (v___x_524_ == 0)
{
size_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v___x_525_ = lean_usize_of_nat(v_start_517_);
v___x_526_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_520_, v___x_525_, v_shift_522_, v_init_516_);
v___x_527_ = lean_array_get_size(v_tail_521_);
v___x_528_ = lean_nat_dec_lt(v___x_518_, v___x_527_);
if (v___x_528_ == 0)
{
return v___x_526_;
}
else
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; 
v___x_529_ = ((size_t)0ULL);
v___x_530_ = lean_usize_of_nat(v___x_527_);
v___x_531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_521_, v___x_529_, v___x_530_, v___x_526_);
return v___x_531_;
}
}
else
{
lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_532_ = lean_nat_sub(v_start_517_, v_tailOff_523_);
v___x_533_ = lean_array_get_size(v_tail_521_);
v___x_534_ = lean_nat_dec_lt(v___x_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_dec(v___x_532_);
return v_init_516_;
}
else
{
size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_usize_of_nat(v___x_532_);
lean_dec(v___x_532_);
v___x_536_ = lean_usize_of_nat(v___x_533_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_521_, v___x_535_, v___x_536_, v_init_516_);
return v___x_537_;
}
}
}
else
{
lean_object* v_root_538_; lean_object* v_tail_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_root_538_ = lean_ctor_get(v_t_515_, 0);
v_tail_539_ = lean_ctor_get(v_t_515_, 1);
v___x_540_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_538_, v_init_516_);
v___x_541_ = lean_array_get_size(v_tail_539_);
v___x_542_ = lean_nat_dec_lt(v___x_518_, v___x_541_);
if (v___x_542_ == 0)
{
return v___x_540_;
}
else
{
size_t v___x_543_; size_t v___x_544_; lean_object* v___x_545_; 
v___x_543_ = ((size_t)0ULL);
v___x_544_ = lean_usize_of_nat(v___x_541_);
v___x_545_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_539_, v___x_543_, v___x_544_, v___x_540_);
return v___x_545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1___boxed(lean_object* v_t_546_, lean_object* v_init_547_, lean_object* v_start_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_t_546_, v_init_547_, v_start_548_);
lean_dec(v_start_548_);
lean_dec_ref(v_t_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(lean_object* v_t_550_, lean_object* v_init_551_, lean_object* v_start_552_){
_start:
{
lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_nat_dec_eq(v_start_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v_root_555_; lean_object* v_tail_556_; size_t v_shift_557_; lean_object* v_tailOff_558_; uint8_t v___x_559_; 
v_root_555_ = lean_ctor_get(v_t_550_, 0);
v_tail_556_ = lean_ctor_get(v_t_550_, 1);
v_shift_557_ = lean_ctor_get_usize(v_t_550_, 4);
v_tailOff_558_ = lean_ctor_get(v_t_550_, 3);
v___x_559_ = lean_nat_dec_le(v_tailOff_558_, v_start_552_);
if (v___x_559_ == 0)
{
size_t v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_560_ = lean_usize_of_nat(v_start_552_);
v___x_561_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_555_, v___x_560_, v_shift_557_, v_init_551_);
v___x_562_ = lean_array_get_size(v_tail_556_);
v___x_563_ = lean_nat_dec_lt(v___x_553_, v___x_562_);
if (v___x_563_ == 0)
{
return v___x_561_;
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_562_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_556_, v___x_564_, v___x_565_, v___x_561_);
return v___x_566_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_567_ = lean_nat_sub(v_start_552_, v_tailOff_558_);
v___x_568_ = lean_array_get_size(v_tail_556_);
v___x_569_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec(v___x_567_);
return v_init_551_;
}
else
{
size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_570_ = lean_usize_of_nat(v___x_567_);
lean_dec(v___x_567_);
v___x_571_ = lean_usize_of_nat(v___x_568_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_556_, v___x_570_, v___x_571_, v_init_551_);
return v___x_572_;
}
}
}
else
{
lean_object* v_root_573_; lean_object* v_tail_574_; lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_root_573_ = lean_ctor_get(v_t_550_, 0);
v_tail_574_ = lean_ctor_get(v_t_550_, 1);
v___x_575_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_573_, v_init_551_);
v___x_576_ = lean_array_get_size(v_tail_574_);
v___x_577_ = lean_nat_dec_lt(v___x_553_, v___x_576_);
if (v___x_577_ == 0)
{
return v___x_575_;
}
else
{
size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; 
v___x_578_ = ((size_t)0ULL);
v___x_579_ = lean_usize_of_nat(v___x_576_);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_574_, v___x_578_, v___x_579_, v___x_575_);
return v___x_580_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0___boxed(lean_object* v_t_581_, lean_object* v_init_582_, lean_object* v_start_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_t_581_, v_init_582_, v_start_583_);
lean_dec(v_start_583_);
lean_dec_ref(v_t_581_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(lean_object* v_meta_587_, lean_object* v_writeDiagnostics_588_, uint8_t v_incrementalDiagnosticSupport_589_, lean_object* v___y_590_){
_start:
{
lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v_fst_598_; uint8_t v_snd_599_; lean_object* v___x_603_; uint8_t v___y_605_; 
v___x_603_ = lean_st_ref_get(v___y_590_);
if (v_incrementalDiagnosticSupport_589_ == 0)
{
v___y_605_ = v_incrementalDiagnosticSupport_589_;
goto v___jp_604_;
}
else
{
uint8_t v_isIncremental_626_; 
v_isIncremental_626_ = lean_ctor_get_uint8(v___x_603_, sizeof(void*)*3);
v___y_605_ = v_isIncremental_626_;
goto v___jp_604_;
}
v___jp_592_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = l_Lean_Server_mkPublishDiagnosticsNotification(v_meta_587_, v___y_593_, v___y_594_);
v___x_596_ = lean_apply_2(v_writeDiagnostics_588_, v___x_595_, lean_box(0));
return v___x_596_;
}
v___jp_597_:
{
if (v_incrementalDiagnosticSupport_589_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_box(0);
v___y_593_ = v_fst_598_;
v___y_594_ = v___x_600_;
goto v___jp_592_;
}
else
{
lean_object* v___x_601_; lean_object* v___x_602_; 
v___x_601_ = lean_box(v_snd_599_);
v___x_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
v___y_593_ = v_fst_598_;
v___y_594_ = v___x_602_;
goto v___jp_592_;
}
}
v___jp_604_:
{
lean_object* v_stickyDiagsRef_606_; lean_object* v_diags_607_; lean_object* v_publishedDiagsAmount_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_625_; 
v_stickyDiagsRef_606_ = lean_ctor_get(v___x_603_, 0);
v_diags_607_ = lean_ctor_get(v___x_603_, 1);
v_publishedDiagsAmount_608_ = lean_ctor_get(v___x_603_, 2);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_625_ == 0)
{
v___x_610_ = v___x_603_;
v_isShared_611_ = v_isSharedCheck_625_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_publishedDiagsAmount_608_);
lean_inc(v_diags_607_);
lean_inc(v_stickyDiagsRef_606_);
lean_dec(v___x_603_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_625_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v___x_612_; lean_object* v_size_613_; uint8_t v___x_614_; lean_object* v___x_616_; 
v___x_612_ = lean_st_ref_get(v_stickyDiagsRef_606_);
v_size_613_ = lean_ctor_get(v_diags_607_, 2);
v___x_614_ = 1;
lean_inc(v_size_613_);
lean_inc_ref(v_diags_607_);
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 2, v_size_613_);
v___x_616_ = v___x_610_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_stickyDiagsRef_606_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_diags_607_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_size_613_);
v___x_616_ = v_reuseFailAlloc_624_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; 
lean_ctor_set_uint8(v___x_616_, sizeof(void*)*3, v___x_614_);
v___x_617_ = lean_st_ref_swap(v___y_590_, v___x_616_);
lean_dec(v___x_617_);
if (v___y_605_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_publishedDiagsAmount_608_);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_620_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v___x_612_, v___x_619_, v___x_618_);
lean_dec(v___x_612_);
v___x_621_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_diags_607_, v___x_620_, v___x_618_);
lean_dec_ref(v_diags_607_);
v_fst_598_ = v___x_621_;
v_snd_599_ = v___y_605_;
goto v___jp_597_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec(v___x_612_);
v___x_622_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_623_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_diags_607_, v___x_622_, v_publishedDiagsAmount_608_);
lean_dec(v_publishedDiagsAmount_608_);
lean_dec_ref(v_diags_607_);
v_fst_598_ = v___x_623_;
v_snd_599_ = v___x_614_;
goto v___jp_597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed(lean_object* v_meta_627_, lean_object* v_writeDiagnostics_628_, lean_object* v_incrementalDiagnosticSupport_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_632_; lean_object* v_res_633_; 
v_incrementalDiagnosticSupport_boxed_632_ = lean_unbox(v_incrementalDiagnosticSupport_629_);
v_res_633_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(v_meta_627_, v_writeDiagnostics_628_, v_incrementalDiagnosticSupport_boxed_632_, v___y_630_);
lean_dec(v___y_630_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(lean_object* v_doc_634_, uint8_t v_incrementalDiagnosticSupport_635_, lean_object* v_writeDiagnostics_636_){
_start:
{
lean_object* v_meta_638_; lean_object* v_diagnosticsMutex_639_; lean_object* v___x_640_; lean_object* v___f_641_; lean_object* v___x_642_; 
v_meta_638_ = lean_ctor_get(v_doc_634_, 0);
lean_inc_ref(v_meta_638_);
v_diagnosticsMutex_639_ = lean_ctor_get(v_doc_634_, 3);
lean_inc_ref(v_diagnosticsMutex_639_);
lean_dec_ref(v_doc_634_);
v___x_640_ = lean_box(v_incrementalDiagnosticSupport_635_);
v___f_641_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed), 5, 3);
lean_closure_set(v___f_641_, 0, v_meta_638_);
lean_closure_set(v___f_641_, 1, v_writeDiagnostics_636_);
lean_closure_set(v___f_641_, 2, v___x_640_);
v___x_642_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_639_, v___f_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___boxed(lean_object* v_doc_643_, lean_object* v_incrementalDiagnosticSupport_644_, lean_object* v_writeDiagnostics_645_, lean_object* v_a_646_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_647_; lean_object* v_res_648_; 
v_incrementalDiagnosticSupport_boxed_647_ = lean_unbox(v_incrementalDiagnosticSupport_644_);
v_res_648_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(v_doc_643_, v_incrementalDiagnosticSupport_boxed_647_, v_writeDiagnostics_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object* v_ed_649_){
_start:
{
lean_object* v_toEditableDocumentCore_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_661_; 
v_toEditableDocumentCore_650_ = lean_ctor_get(v_ed_649_, 0);
v_isSharedCheck_661_ = !lean_is_exclusive(v_ed_649_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_ed_649_, 1);
lean_dec(v_unused_662_);
v___x_652_ = v_ed_649_;
v_isShared_653_ = v_isSharedCheck_661_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_toEditableDocumentCore_650_);
lean_dec(v_ed_649_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_661_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_meta_654_; lean_object* v_uri_655_; lean_object* v_version_656_; lean_object* v___x_657_; lean_object* v___x_659_; 
v_meta_654_ = lean_ctor_get(v_toEditableDocumentCore_650_, 0);
lean_inc_ref(v_meta_654_);
lean_dec_ref(v_toEditableDocumentCore_650_);
v_uri_655_ = lean_ctor_get(v_meta_654_, 0);
lean_inc_ref(v_uri_655_);
v_version_656_ = lean_ctor_get(v_meta_654_, 2);
lean_inc(v_version_656_);
lean_dec_ref(v_meta_654_);
v___x_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_657_, 0, v_version_656_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_657_);
lean_ctor_set(v___x_652_, 0, v_uri_655_);
v___x_659_ = v___x_652_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_uri_655_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v___x_657_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs(void){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = lean_unsigned_to_nat(30000u);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0(void){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_664_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1(void){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__0, &l_Lean_Server_FileWorker_RpcSession_new___closed__0_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new(uint8_t v_wireFormat_667_){
_start:
{
size_t v___x_669_; lean_object* v___x_670_; 
v___x_669_ = ((size_t)8ULL);
v___x_670_ = lean_io_get_random_bytes(v___x_669_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_688_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_688_ == 0)
{
v___x_673_ = v___x_670_;
v_isShared_674_ = v_isSharedCheck_688_;
goto v_resetjp_672_;
}
else
{
lean_inc(v_a_671_);
lean_dec(v___x_670_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_688_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
uint64_t v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; size_t v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; 
v___x_675_ = l_ByteArray_toUInt64LE_x21(v_a_671_);
lean_dec(v_a_671_);
v___x_676_ = lean_io_mono_ms_now();
v___x_677_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__1, &l_Lean_Server_FileWorker_RpcSession_new___closed__1_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1);
v___x_678_ = ((size_t)0ULL);
v___x_679_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_679_, 0, v___x_677_);
lean_ctor_set(v___x_679_, 1, v___x_677_);
lean_ctor_set_usize(v___x_679_, 2, v___x_678_);
lean_ctor_set_uint8(v___x_679_, sizeof(void*)*3, v_wireFormat_667_);
v___x_680_ = lean_unsigned_to_nat(30000u);
v___x_681_ = lean_nat_add(v___x_676_, v___x_680_);
lean_dec(v___x_676_);
v___x_682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_682_, 0, v___x_679_);
lean_ctor_set(v___x_682_, 1, v___x_681_);
v___x_683_ = lean_box_uint64(v___x_675_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_684_);
v___x_686_ = v___x_673_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_684_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
else
{
lean_object* v_a_689_; lean_object* v___x_691_; uint8_t v_isShared_692_; uint8_t v_isSharedCheck_696_; 
v_a_689_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_696_ == 0)
{
v___x_691_ = v___x_670_;
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
else
{
lean_inc(v_a_689_);
lean_dec(v___x_670_);
v___x_691_ = lean_box(0);
v_isShared_692_ = v_isSharedCheck_696_;
goto v_resetjp_690_;
}
v_resetjp_690_:
{
lean_object* v___x_694_; 
if (v_isShared_692_ == 0)
{
v___x_694_ = v___x_691_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_689_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new___boxed(lean_object* v_wireFormat_697_, lean_object* v_a_698_){
_start:
{
uint8_t v_wireFormat_boxed_699_; lean_object* v_res_700_; 
v_wireFormat_boxed_699_ = lean_unbox(v_wireFormat_697_);
v_res_700_ = l_Lean_Server_FileWorker_RpcSession_new(v_wireFormat_boxed_699_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object* v_monoMsNow_701_, lean_object* v_s_702_){
_start:
{
lean_object* v_objects_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_712_; 
v_objects_703_ = lean_ctor_get(v_s_702_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v_s_702_);
if (v_isSharedCheck_712_ == 0)
{
lean_object* v_unused_713_; 
v_unused_713_ = lean_ctor_get(v_s_702_, 1);
lean_dec(v_unused_713_);
v___x_705_ = v_s_702_;
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_objects_703_);
lean_dec(v_s_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_712_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_707_ = lean_unsigned_to_nat(30000u);
v___x_708_ = lean_nat_add(v_monoMsNow_701_, v___x_707_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v___x_708_);
v___x_710_ = v___x_705_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_objects_703_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v___x_708_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object* v_monoMsNow_714_, lean_object* v_s_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Server_FileWorker_RpcSession_keptAlive(v_monoMsNow_714_, v_s_715_);
lean_dec(v_monoMsNow_714_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object* v_s_717_){
_start:
{
lean_object* v___x_719_; lean_object* v_expireTime_720_; uint8_t v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_719_ = lean_io_mono_ms_now();
v_expireTime_720_ = lean_ctor_get(v_s_717_, 1);
v___x_721_ = lean_nat_dec_le(v_expireTime_720_, v___x_719_);
lean_dec(v___x_719_);
v___x_722_ = lean_box(v___x_721_);
v___x_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_723_, 0, v___x_722_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object* v_s_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Lean_Server_FileWorker_RpcSession_hasExpired(v_s_724_);
lean_dec_ref(v_s_724_);
return v_res_726_;
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
