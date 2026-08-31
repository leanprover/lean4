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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* v_unused_29_; 
v_unused_29_ = lean_ctor_get(v_result_4_, 0);
lean_dec(v_unused_29_);
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
lean_object* v___x_9_; lean_object* v___y_11_; 
v___x_9_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_9_, 0, v_stx_1_);
lean_ctor_set(v___x_9_, 1, v_parserState_2_);
lean_ctor_set(v___x_9_, 2, v_cmdState_5_);
if (lean_obj_tag(v_nextCmdSnap_x3f_3_) == 0)
{
lean_object* v___x_16_; 
v___x_16_ = lean_box(2);
v___y_11_ = v___x_16_;
goto v___jp_10_;
}
else
{
lean_object* v_val_17_; lean_object* v___x_19_; uint8_t v_isShared_20_; uint8_t v_isSharedCheck_27_; 
v_val_17_ = lean_ctor_get(v_nextCmdSnap_x3f_3_, 0);
v_isSharedCheck_27_ = !lean_is_exclusive(v_nextCmdSnap_x3f_3_);
if (v_isSharedCheck_27_ == 0)
{
v___x_19_ = v_nextCmdSnap_x3f_3_;
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
else
{
lean_inc(v_val_17_);
lean_dec(v_nextCmdSnap_x3f_3_);
v___x_19_ = lean_box(0);
v_isShared_20_ = v_isSharedCheck_27_;
goto v_resetjp_18_;
}
v_resetjp_18_:
{
lean_object* v_task_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_25_; 
v_task_21_ = lean_ctor_get(v_val_17_, 3);
lean_inc_ref(v_task_21_);
lean_dec(v_val_17_);
v___x_22_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go), 1, 0);
v___x_23_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_21_, v___x_22_);
if (v_isShared_20_ == 0)
{
lean_ctor_set(v___x_19_, 0, v___x_23_);
v___x_25_ = v___x_19_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_26_; 
v_reuseFailAlloc_26_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_26_, 0, v___x_23_);
v___x_25_ = v_reuseFailAlloc_26_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
v___y_11_ = v___x_25_;
goto v___jp_10_;
}
}
}
v___jp_10_:
{
lean_object* v___x_13_; 
if (v_isShared_8_ == 0)
{
lean_ctor_set(v___x_7_, 1, v___y_11_);
lean_ctor_set(v___x_7_, 0, v___x_9_);
v___x_13_ = v___x_7_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v___x_9_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v___y_11_);
v___x_13_ = v_reuseFailAlloc_15_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
lean_object* v___x_14_; 
v___x_14_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
return v___x_14_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go(lean_object* v_cmdParsed_30_){
_start:
{
lean_object* v_elabSnap_31_; lean_object* v_resultSnap_32_; lean_object* v_stx_33_; lean_object* v_parserState_34_; lean_object* v_nextCmdSnap_x3f_35_; lean_object* v_task_36_; lean_object* v___f_37_; lean_object* v___x_38_; 
v_elabSnap_31_ = lean_ctor_get(v_cmdParsed_30_, 3);
v_resultSnap_32_ = lean_ctor_get(v_elabSnap_31_, 2);
lean_inc_ref(v_resultSnap_32_);
v_stx_33_ = lean_ctor_get(v_cmdParsed_30_, 1);
lean_inc(v_stx_33_);
v_parserState_34_ = lean_ctor_get(v_cmdParsed_30_, 2);
lean_inc_ref(v_parserState_34_);
v_nextCmdSnap_x3f_35_ = lean_ctor_get(v_cmdParsed_30_, 4);
lean_inc(v_nextCmdSnap_x3f_35_);
lean_dec_ref(v_cmdParsed_30_);
v_task_36_ = lean_ctor_get(v_resultSnap_32_, 3);
lean_inc_ref(v_task_36_);
lean_dec_ref(v_resultSnap_32_);
v___f_37_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps_go___lam__0), 4, 3);
lean_closure_set(v___f_37_, 0, v_stx_33_);
lean_closure_set(v___f_37_, 1, v_parserState_34_);
lean_closure_set(v___f_37_, 2, v_nextCmdSnap_x3f_35_);
v___x_38_ = l_Lean_Server_ServerTask_mapCheap___redArg(v___f_37_, v_task_36_);
return v___x_38_;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__1));
v___x_43_ = lean_task_pure(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0(lean_object* v_stx_44_, lean_object* v_parserState_45_, lean_object* v_headerProcessed_46_){
_start:
{
lean_object* v_result_x3f_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_77_; 
v_result_x3f_47_ = lean_ctor_get(v_headerProcessed_46_, 2);
v_isSharedCheck_77_ = !lean_is_exclusive(v_headerProcessed_46_);
if (v_isSharedCheck_77_ == 0)
{
lean_object* v_unused_78_; lean_object* v_unused_79_; 
v_unused_78_ = lean_ctor_get(v_headerProcessed_46_, 1);
lean_dec(v_unused_78_);
v_unused_79_ = lean_ctor_get(v_headerProcessed_46_, 0);
lean_dec(v_unused_79_);
v___x_49_ = v_headerProcessed_46_;
v_isShared_50_ = v_isSharedCheck_77_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_result_x3f_47_);
lean_dec(v_headerProcessed_46_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_77_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
if (lean_obj_tag(v_result_x3f_47_) == 1)
{
lean_object* v_val_51_; lean_object* v___x_53_; uint8_t v_isShared_54_; uint8_t v_isSharedCheck_75_; 
v_val_51_ = lean_ctor_get(v_result_x3f_47_, 0);
v_isSharedCheck_75_ = !lean_is_exclusive(v_result_x3f_47_);
if (v_isSharedCheck_75_ == 0)
{
v___x_53_ = v_result_x3f_47_;
v_isShared_54_ = v_isSharedCheck_75_;
goto v_resetjp_52_;
}
else
{
lean_inc(v_val_51_);
lean_dec(v_result_x3f_47_);
v___x_53_ = lean_box(0);
v_isShared_54_ = v_isSharedCheck_75_;
goto v_resetjp_52_;
}
v_resetjp_52_:
{
lean_object* v_firstCmdSnap_55_; lean_object* v_cmdState_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_74_; 
v_firstCmdSnap_55_ = lean_ctor_get(v_val_51_, 1);
v_cmdState_56_ = lean_ctor_get(v_val_51_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v_val_51_);
if (v_isSharedCheck_74_ == 0)
{
v___x_58_ = v_val_51_;
v_isShared_59_ = v_isSharedCheck_74_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_firstCmdSnap_55_);
lean_inc(v_cmdState_56_);
lean_dec(v_val_51_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_74_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v_task_60_; lean_object* v___x_62_; 
v_task_60_ = lean_ctor_get(v_firstCmdSnap_55_, 3);
lean_inc_ref(v_task_60_);
lean_dec_ref(v_firstCmdSnap_55_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 2, v_cmdState_56_);
lean_ctor_set(v___x_49_, 1, v_parserState_45_);
lean_ctor_set(v___x_49_, 0, v_stx_44_);
v___x_62_ = v___x_49_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_73_; 
v_reuseFailAlloc_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_73_, 0, v_stx_44_);
lean_ctor_set(v_reuseFailAlloc_73_, 1, v_parserState_45_);
lean_ctor_set(v_reuseFailAlloc_73_, 2, v_cmdState_56_);
v___x_62_ = v_reuseFailAlloc_73_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_66_; 
v___x_63_ = ((lean_object*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__0));
v___x_64_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_60_, v___x_63_);
if (v_isShared_54_ == 0)
{
lean_ctor_set(v___x_53_, 0, v___x_64_);
v___x_66_ = v___x_53_;
goto v_reusejp_65_;
}
else
{
lean_object* v_reuseFailAlloc_72_; 
v_reuseFailAlloc_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_72_, 0, v___x_64_);
v___x_66_ = v_reuseFailAlloc_72_;
goto v_reusejp_65_;
}
v_reusejp_65_:
{
lean_object* v___x_68_; 
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_66_);
lean_ctor_set(v___x_58_, 0, v___x_62_);
v___x_68_ = v___x_58_;
goto v_reusejp_67_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_62_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v___x_66_);
v___x_68_ = v_reuseFailAlloc_71_;
goto v_reusejp_67_;
}
v_reusejp_67_:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
v___x_70_ = lean_task_pure(v___x_69_);
return v___x_70_;
}
}
}
}
}
}
else
{
lean_object* v___x_76_; 
lean_del_object(v___x_49_);
lean_dec(v_result_x3f_47_);
lean_dec_ref(v_parserState_45_);
lean_dec(v_stx_44_);
v___x_76_ = lean_obj_once(&l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2, &l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2_once, _init_l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0___closed__2);
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(lean_object* v_initSnap_80_){
_start:
{
lean_object* v_result_x3f_81_; 
v_result_x3f_81_ = lean_ctor_get(v_initSnap_80_, 4);
lean_inc(v_result_x3f_81_);
if (lean_obj_tag(v_result_x3f_81_) == 1)
{
lean_object* v_val_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_95_; 
v_val_82_ = lean_ctor_get(v_result_x3f_81_, 0);
v_isSharedCheck_95_ = !lean_is_exclusive(v_result_x3f_81_);
if (v_isSharedCheck_95_ == 0)
{
v___x_84_ = v_result_x3f_81_;
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_val_82_);
lean_dec(v_result_x3f_81_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_95_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
lean_object* v_processedSnap_86_; lean_object* v_stx_87_; lean_object* v_parserState_88_; lean_object* v_task_89_; lean_object* v___f_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v_processedSnap_86_ = lean_ctor_get(v_val_82_, 1);
lean_inc_ref(v_processedSnap_86_);
v_stx_87_ = lean_ctor_get(v_initSnap_80_, 3);
lean_inc(v_stx_87_);
lean_dec_ref(v_initSnap_80_);
v_parserState_88_ = lean_ctor_get(v_val_82_, 0);
lean_inc_ref(v_parserState_88_);
lean_dec(v_val_82_);
v_task_89_ = lean_ctor_get(v_processedSnap_86_, 3);
lean_inc_ref(v_task_89_);
lean_dec_ref(v_processedSnap_86_);
v___f_90_ = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps___lam__0), 3, 2);
lean_closure_set(v___f_90_, 0, v_stx_87_);
lean_closure_set(v___f_90_, 1, v_parserState_88_);
v___x_91_ = l_Lean_Server_ServerTask_bindCheap___redArg(v_task_89_, v___f_90_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 0, v___x_91_);
v___x_93_ = v___x_84_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
else
{
lean_object* v___x_96_; 
lean_dec(v_result_x3f_81_);
lean_dec_ref(v_initSnap_80_);
v___x_96_ = lean_box(2);
return v___x_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore___private__1(lean_object* v_initSnap_97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(v_initSnap_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(lean_object* v_mutex_99_, lean_object* v_k_100_){
_start:
{
lean_object* v_ref_102_; lean_object* v_mutex_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_ref_102_ = lean_ctor_get(v_mutex_99_, 0);
lean_inc(v_ref_102_);
v_mutex_103_ = lean_ctor_get(v_mutex_99_, 1);
lean_inc(v_mutex_103_);
lean_dec_ref(v_mutex_99_);
v___x_104_ = lean_io_basemutex_lock(v_mutex_103_);
v___x_105_ = lean_apply_2(v_k_100_, v_ref_102_, lean_box(0));
v___x_106_ = lean_io_basemutex_unlock(v_mutex_103_);
lean_dec(v_mutex_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg___boxed(lean_object* v_mutex_107_, lean_object* v_k_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_mutex_107_, v_k_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(lean_object* v_00_u03b1_111_, lean_object* v_00_u03b2_112_, lean_object* v_mutex_113_, lean_object* v_k_114_){
_start:
{
lean_object* v___x_116_; 
v___x_116_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_mutex_113_, v_k_114_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___boxed(lean_object* v_00_u03b1_117_, lean_object* v_00_u03b2_118_, lean_object* v_mutex_119_, lean_object* v_k_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1(v_00_u03b1_117_, v_00_u03b2_118_, v_mutex_119_, v_k_120_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(lean_object* v_as_123_, size_t v_i_124_, size_t v_stop_125_, lean_object* v_b_126_){
_start:
{
uint8_t v___x_127_; 
v___x_127_ = lean_usize_dec_eq(v_i_124_, v_stop_125_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; size_t v___x_130_; size_t v___x_131_; 
v___x_128_ = lean_array_uget_borrowed(v_as_123_, v_i_124_);
lean_inc(v___x_128_);
v___x_129_ = l_Lean_PersistentArray_push___redArg(v_b_126_, v___x_128_);
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_add(v_i_124_, v___x_130_);
v_i_124_ = v___x_131_;
v_b_126_ = v___x_129_;
goto _start;
}
else
{
return v_b_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0___boxed(lean_object* v_as_133_, lean_object* v_i_134_, lean_object* v_stop_135_, lean_object* v_b_136_){
_start:
{
size_t v_i_boxed_137_; size_t v_stop_boxed_138_; lean_object* v_res_139_; 
v_i_boxed_137_ = lean_unbox_usize(v_i_134_);
lean_dec(v_i_134_);
v_stop_boxed_138_ = lean_unbox_usize(v_stop_135_);
lean_dec(v_stop_135_);
v_res_139_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_as_133_, v_i_boxed_137_, v_stop_boxed_138_, v_b_136_);
lean_dec_ref(v_as_133_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(lean_object* v_diags_140_, lean_object* v___y_141_){
_start:
{
lean_object* v___x_143_; lean_object* v_stickyDiagsRef_144_; lean_object* v_diags_145_; uint8_t v_isIncremental_146_; lean_object* v_publishedDiagsAmount_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_168_; 
v___x_143_ = lean_st_ref_take(v___y_141_);
v_stickyDiagsRef_144_ = lean_ctor_get(v___x_143_, 0);
v_diags_145_ = lean_ctor_get(v___x_143_, 1);
v_isIncremental_146_ = lean_ctor_get_uint8(v___x_143_, sizeof(void*)*3);
v_publishedDiagsAmount_147_ = lean_ctor_get(v___x_143_, 2);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_143_);
if (v_isSharedCheck_168_ == 0)
{
v___x_149_ = v___x_143_;
v_isShared_150_ = v_isSharedCheck_168_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_publishedDiagsAmount_147_);
lean_inc(v_diags_145_);
lean_inc(v_stickyDiagsRef_144_);
lean_dec(v___x_143_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_168_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___y_153_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_151_ = lean_box(0);
v___x_158_ = lean_unsigned_to_nat(0u);
v___x_159_ = lean_array_get_size(v_diags_140_);
v___x_160_ = lean_nat_dec_lt(v___x_158_, v___x_159_);
if (v___x_160_ == 0)
{
v___y_153_ = v_diags_145_;
goto v___jp_152_;
}
else
{
uint8_t v___x_161_; 
v___x_161_ = lean_nat_dec_le(v___x_159_, v___x_159_);
if (v___x_161_ == 0)
{
if (v___x_160_ == 0)
{
v___y_153_ = v_diags_145_;
goto v___jp_152_;
}
else
{
size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; 
v___x_162_ = ((size_t)0ULL);
v___x_163_ = lean_usize_of_nat(v___x_159_);
v___x_164_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_diags_140_, v___x_162_, v___x_163_, v_diags_145_);
v___y_153_ = v___x_164_;
goto v___jp_152_;
}
}
else
{
size_t v___x_165_; size_t v___x_166_; lean_object* v___x_167_; 
v___x_165_ = ((size_t)0ULL);
v___x_166_ = lean_usize_of_nat(v___x_159_);
v___x_167_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__0(v_diags_140_, v___x_165_, v___x_166_, v_diags_145_);
v___y_153_ = v___x_167_;
goto v___jp_152_;
}
}
v___jp_152_:
{
lean_object* v___x_155_; 
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 1, v___y_153_);
v___x_155_ = v___x_149_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_stickyDiagsRef_144_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v___y_153_);
lean_ctor_set(v_reuseFailAlloc_157_, 2, v_publishedDiagsAmount_147_);
lean_ctor_set_uint8(v_reuseFailAlloc_157_, sizeof(void*)*3, v_isIncremental_146_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = lean_st_ref_put(v___y_141_, v___x_155_);
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed(lean_object* v_diags_169_, lean_object* v___y_170_, lean_object* v___y_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0(v_diags_169_, v___y_170_);
lean_dec(v___y_170_);
lean_dec_ref(v_diags_169_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(lean_object* v_doc_173_, lean_object* v_diags_174_){
_start:
{
lean_object* v_diagnosticsMutex_176_; lean_object* v___f_177_; lean_object* v___x_178_; 
v_diagnosticsMutex_176_ = lean_ctor_get(v_doc_173_, 3);
lean_inc_ref(v_diagnosticsMutex_176_);
lean_dec_ref(v_doc_173_);
v___f_177_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___lam__0___boxed), 3, 1);
lean_closure_set(v___f_177_, 0, v_diags_174_);
v___x_178_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_176_, v___f_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics___boxed(lean_object* v_doc_179_, lean_object* v_diags_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics(v_doc_179_, v_diags_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(lean_object* v_diagnostic_183_, lean_object* v_as_184_, size_t v_i_185_, size_t v_stop_186_, lean_object* v_b_187_){
_start:
{
lean_object* v___y_189_; uint8_t v___x_193_; 
v___x_193_ = lean_usize_dec_eq(v_i_185_, v_stop_186_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; lean_object* v_message_195_; lean_object* v_message_196_; lean_object* v___x_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v___x_194_ = lean_array_uget_borrowed(v_as_184_, v_i_185_);
v_message_195_ = lean_ctor_get(v___x_194_, 6);
v_message_196_ = lean_ctor_get(v_diagnostic_183_, 6);
lean_inc(v_message_195_);
v___x_197_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_195_);
lean_inc(v_message_196_);
v___x_198_ = l_Lean_Widget_TaggedText_stripTags___redArg(v_message_196_);
v___x_199_ = lean_string_dec_eq(v___x_197_, v___x_198_);
lean_dec_ref(v___x_198_);
lean_dec_ref(v___x_197_);
if (v___x_199_ == 0)
{
lean_object* v___x_200_; 
lean_inc(v___x_194_);
v___x_200_ = l_Lean_PersistentArray_push___redArg(v_b_187_, v___x_194_);
v___y_189_ = v___x_200_;
goto v___jp_188_;
}
else
{
v___y_189_ = v_b_187_;
goto v___jp_188_;
}
}
else
{
lean_dec_ref(v_diagnostic_183_);
return v_b_187_;
}
v___jp_188_:
{
size_t v___x_190_; size_t v___x_191_; 
v___x_190_ = ((size_t)1ULL);
v___x_191_ = lean_usize_add(v_i_185_, v___x_190_);
v_i_185_ = v___x_191_;
v_b_187_ = v___y_189_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1___boxed(lean_object* v_diagnostic_201_, lean_object* v_as_202_, lean_object* v_i_203_, lean_object* v_stop_204_, lean_object* v_b_205_){
_start:
{
size_t v_i_boxed_206_; size_t v_stop_boxed_207_; lean_object* v_res_208_; 
v_i_boxed_206_ = lean_unbox_usize(v_i_203_);
lean_dec(v_i_203_);
v_stop_boxed_207_ = lean_unbox_usize(v_stop_204_);
lean_dec(v_stop_204_);
v_res_208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_201_, v_as_202_, v_i_boxed_206_, v_stop_boxed_207_, v_b_205_);
lean_dec_ref(v_as_202_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(lean_object* v_diagnostic_209_, lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
if (lean_obj_tag(v_x_210_) == 0)
{
lean_object* v_cs_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v_cs_212_ = lean_ctor_get(v_x_210_, 0);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_array_get_size(v_cs_212_);
v___x_215_ = lean_nat_dec_lt(v___x_213_, v___x_214_);
if (v___x_215_ == 0)
{
lean_dec_ref(v_diagnostic_209_);
return v_x_211_;
}
else
{
size_t v___x_216_; size_t v___x_217_; lean_object* v___x_218_; 
v___x_216_ = ((size_t)0ULL);
v___x_217_ = lean_usize_of_nat(v___x_214_);
v___x_218_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_209_, v_cs_212_, v___x_216_, v___x_217_, v_x_211_);
return v___x_218_;
}
}
else
{
lean_object* v_vs_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_vs_219_ = lean_ctor_get(v_x_210_, 0);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_array_get_size(v_vs_219_);
v___x_222_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec_ref(v_diagnostic_209_);
return v_x_211_;
}
else
{
size_t v___x_223_; size_t v___x_224_; lean_object* v___x_225_; 
v___x_223_ = ((size_t)0ULL);
v___x_224_ = lean_usize_of_nat(v___x_221_);
v___x_225_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_209_, v_vs_219_, v___x_223_, v___x_224_, v_x_211_);
return v___x_225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(lean_object* v_diagnostic_226_, lean_object* v_as_227_, size_t v_i_228_, size_t v_stop_229_, lean_object* v_b_230_){
_start:
{
uint8_t v___x_231_; 
v___x_231_ = lean_usize_dec_eq(v_i_228_, v_stop_229_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; size_t v___x_234_; size_t v___x_235_; 
v___x_232_ = lean_array_uget_borrowed(v_as_227_, v_i_228_);
lean_inc_ref(v_diagnostic_226_);
v___x_233_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_226_, v___x_232_, v_b_230_);
v___x_234_ = ((size_t)1ULL);
v___x_235_ = lean_usize_add(v_i_228_, v___x_234_);
v_i_228_ = v___x_235_;
v_b_230_ = v___x_233_;
goto _start;
}
else
{
lean_dec_ref(v_diagnostic_226_);
return v_b_230_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1___boxed(lean_object* v_diagnostic_237_, lean_object* v_as_238_, lean_object* v_i_239_, lean_object* v_stop_240_, lean_object* v_b_241_){
_start:
{
size_t v_i_boxed_242_; size_t v_stop_boxed_243_; lean_object* v_res_244_; 
v_i_boxed_242_ = lean_unbox_usize(v_i_239_);
lean_dec(v_i_239_);
v_stop_boxed_243_ = lean_unbox_usize(v_stop_240_);
lean_dec(v_stop_240_);
v_res_244_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_237_, v_as_238_, v_i_boxed_242_, v_stop_boxed_243_, v_b_241_);
lean_dec_ref(v_as_238_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2___boxed(lean_object* v_diagnostic_245_, lean_object* v_x_246_, lean_object* v_x_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_245_, v_x_246_, v_x_247_);
lean_dec_ref(v_x_246_);
return v_res_248_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(lean_object* v_diagnostic_250_, lean_object* v_x_251_, size_t v_x_252_, size_t v_x_253_, lean_object* v_x_254_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_object* v_cs_255_; lean_object* v___x_256_; size_t v___x_257_; lean_object* v_j_258_; lean_object* v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; uint8_t v___x_270_; 
v_cs_255_ = lean_ctor_get(v_x_251_, 0);
v___x_256_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
v___x_257_ = lean_usize_shift_right(v_x_252_, v_x_253_);
v_j_258_ = lean_usize_to_nat(v___x_257_);
v___x_259_ = lean_array_get_borrowed(v___x_256_, v_cs_255_, v_j_258_);
v___x_260_ = ((size_t)1ULL);
v___x_261_ = lean_usize_shift_left(v___x_260_, v_x_253_);
v___x_262_ = lean_usize_sub(v___x_261_, v___x_260_);
v___x_263_ = lean_usize_land(v_x_252_, v___x_262_);
v___x_264_ = ((size_t)5ULL);
v___x_265_ = lean_usize_sub(v_x_253_, v___x_264_);
lean_inc_ref(v_diagnostic_250_);
v___x_266_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_250_, v___x_259_, v___x_263_, v___x_265_, v_x_254_);
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_add(v_j_258_, v___x_267_);
lean_dec(v_j_258_);
v___x_269_ = lean_array_get_size(v_cs_255_);
v___x_270_ = lean_nat_dec_lt(v___x_268_, v___x_269_);
if (v___x_270_ == 0)
{
lean_dec(v___x_268_);
lean_dec_ref(v_diagnostic_250_);
return v___x_266_;
}
else
{
size_t v___x_271_; size_t v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_usize_of_nat(v___x_268_);
lean_dec(v___x_268_);
v___x_272_ = lean_usize_of_nat(v___x_269_);
v___x_273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_250_, v_cs_255_, v___x_271_, v___x_272_, v___x_266_);
return v___x_273_;
}
}
else
{
lean_object* v_vs_274_; lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
v_vs_274_ = lean_ctor_get(v_x_251_, 0);
v___x_275_ = lean_usize_to_nat(v_x_252_);
v___x_276_ = lean_array_get_size(v_vs_274_);
v___x_277_ = lean_nat_dec_lt(v___x_275_, v___x_276_);
if (v___x_277_ == 0)
{
lean_dec(v___x_275_);
lean_dec_ref(v_diagnostic_250_);
return v_x_254_;
}
else
{
size_t v___x_278_; size_t v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_usize_of_nat(v___x_275_);
lean_dec(v___x_275_);
v___x_279_ = lean_usize_of_nat(v___x_276_);
v___x_280_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_250_, v_vs_274_, v___x_278_, v___x_279_, v_x_254_);
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___boxed(lean_object* v_diagnostic_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_){
_start:
{
size_t v_x_1587__boxed_286_; size_t v_x_1588__boxed_287_; lean_object* v_res_288_; 
v_x_1587__boxed_286_ = lean_unbox_usize(v_x_283_);
lean_dec(v_x_283_);
v_x_1588__boxed_287_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_res_288_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_281_, v_x_282_, v_x_1587__boxed_286_, v_x_1588__boxed_287_, v_x_285_);
lean_dec_ref(v_x_282_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(lean_object* v_diagnostic_289_, lean_object* v_t_290_, lean_object* v_init_291_, lean_object* v_start_292_){
_start:
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(0u);
v___x_294_ = lean_nat_dec_eq(v_start_292_, v___x_293_);
if (v___x_294_ == 0)
{
lean_object* v_root_295_; lean_object* v_tail_296_; size_t v_shift_297_; lean_object* v_tailOff_298_; uint8_t v___x_299_; 
v_root_295_ = lean_ctor_get(v_t_290_, 0);
v_tail_296_ = lean_ctor_get(v_t_290_, 1);
v_shift_297_ = lean_ctor_get_usize(v_t_290_, 4);
v_tailOff_298_ = lean_ctor_get(v_t_290_, 3);
v___x_299_ = lean_nat_dec_le(v_tailOff_298_, v_start_292_);
if (v___x_299_ == 0)
{
size_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_300_ = lean_usize_of_nat(v_start_292_);
lean_inc_ref(v_diagnostic_289_);
v___x_301_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_289_, v_root_295_, v___x_300_, v_shift_297_, v_init_291_);
v___x_302_ = lean_array_get_size(v_tail_296_);
v___x_303_ = lean_nat_dec_lt(v___x_293_, v___x_302_);
if (v___x_303_ == 0)
{
lean_dec_ref(v_diagnostic_289_);
return v___x_301_;
}
else
{
size_t v___x_304_; size_t v___x_305_; lean_object* v___x_306_; 
v___x_304_ = ((size_t)0ULL);
v___x_305_ = lean_usize_of_nat(v___x_302_);
v___x_306_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_289_, v_tail_296_, v___x_304_, v___x_305_, v___x_301_);
return v___x_306_;
}
}
else
{
lean_object* v___x_307_; lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_307_ = lean_nat_sub(v_start_292_, v_tailOff_298_);
v___x_308_ = lean_array_get_size(v_tail_296_);
v___x_309_ = lean_nat_dec_lt(v___x_307_, v___x_308_);
if (v___x_309_ == 0)
{
lean_dec(v___x_307_);
lean_dec_ref(v_diagnostic_289_);
return v_init_291_;
}
else
{
size_t v___x_310_; size_t v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_usize_of_nat(v___x_307_);
lean_dec(v___x_307_);
v___x_311_ = lean_usize_of_nat(v___x_308_);
v___x_312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_289_, v_tail_296_, v___x_310_, v___x_311_, v_init_291_);
return v___x_312_;
}
}
}
else
{
lean_object* v_root_313_; lean_object* v_tail_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v_root_313_ = lean_ctor_get(v_t_290_, 0);
v_tail_314_ = lean_ctor_get(v_t_290_, 1);
lean_inc_ref(v_diagnostic_289_);
v___x_315_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_289_, v_root_313_, v_init_291_);
v___x_316_ = lean_array_get_size(v_tail_314_);
v___x_317_ = lean_nat_dec_lt(v___x_293_, v___x_316_);
if (v___x_317_ == 0)
{
lean_dec_ref(v_diagnostic_289_);
return v___x_315_;
}
else
{
size_t v___x_318_; size_t v___x_319_; lean_object* v___x_320_; 
v___x_318_ = ((size_t)0ULL);
v___x_319_ = lean_usize_of_nat(v___x_316_);
v___x_320_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_289_, v_tail_314_, v___x_318_, v___x_319_, v___x_315_);
return v___x_320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0___boxed(lean_object* v_diagnostic_321_, lean_object* v_t_322_, lean_object* v_init_323_, lean_object* v_start_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_321_, v_t_322_, v_init_323_, v_start_324_);
lean_dec(v_start_324_);
lean_dec_ref(v_t_322_);
return v_res_325_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_unsigned_to_nat(32u);
v___x_327_ = lean_mk_empty_array_with_capacity(v___x_326_);
v___x_328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1(void){
_start:
{
size_t v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_329_ = ((size_t)5ULL);
v___x_330_ = lean_unsigned_to_nat(0u);
v___x_331_ = lean_unsigned_to_nat(32u);
v___x_332_ = lean_mk_empty_array_with_capacity(v___x_331_);
v___x_333_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0);
v___x_334_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_332_);
lean_ctor_set(v___x_334_, 2, v___x_330_);
lean_ctor_set(v___x_334_, 3, v___x_330_);
lean_ctor_set_usize(v___x_334_, 4, v___x_329_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(lean_object* v_diagnostic_335_, lean_object* v___y_336_){
_start:
{
lean_object* v___x_338_; lean_object* v_stickyDiagsRef_339_; lean_object* v_diags_340_; lean_object* v_publishedDiagsAmount_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_357_; 
v___x_338_ = lean_st_ref_get(v___y_336_);
v_stickyDiagsRef_339_ = lean_ctor_get(v___x_338_, 0);
v_diags_340_ = lean_ctor_get(v___x_338_, 1);
v_publishedDiagsAmount_341_ = lean_ctor_get(v___x_338_, 2);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_357_ == 0)
{
v___x_343_ = v___x_338_;
v_isShared_344_ = v_isSharedCheck_357_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_publishedDiagsAmount_341_);
lean_inc(v_diags_340_);
lean_inc(v_stickyDiagsRef_339_);
lean_dec(v___x_338_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_357_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v_stickyDiags_348_; lean_object* v___x_349_; lean_object* v___x_350_; uint8_t v___x_351_; lean_object* v___x_353_; 
v___x_345_ = lean_st_ref_take(v_stickyDiagsRef_339_);
v___x_346_ = lean_unsigned_to_nat(0u);
v___x_347_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
lean_inc_ref(v_diagnostic_335_);
v_stickyDiags_348_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_335_, v___x_345_, v___x_347_, v___x_346_);
lean_dec(v___x_345_);
v___x_349_ = l_Lean_PersistentArray_push___redArg(v_stickyDiags_348_, v_diagnostic_335_);
v___x_350_ = lean_st_ref_put(v_stickyDiagsRef_339_, v___x_349_);
v___x_351_ = 0;
if (v_isShared_344_ == 0)
{
v___x_353_ = v___x_343_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_stickyDiagsRef_339_);
lean_ctor_set(v_reuseFailAlloc_356_, 1, v_diags_340_);
lean_ctor_set(v_reuseFailAlloc_356_, 2, v_publishedDiagsAmount_341_);
v___x_353_ = v_reuseFailAlloc_356_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_ctor_set_uint8(v___x_353_, sizeof(void*)*3, v___x_351_);
v___x_354_ = lean_st_ref_swap(v___y_336_, v___x_353_);
lean_dec(v___x_354_);
v___x_355_ = lean_box(0);
return v___x_355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed(lean_object* v_diagnostic_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(v_diagnostic_358_, v___y_359_);
lean_dec(v___y_359_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(lean_object* v_doc_362_, lean_object* v_diagnostic_363_){
_start:
{
lean_object* v_diagnosticsMutex_365_; lean_object* v___f_366_; lean_object* v___x_367_; 
v_diagnosticsMutex_365_ = lean_ctor_get(v_doc_362_, 3);
lean_inc_ref(v_diagnosticsMutex_365_);
lean_dec_ref(v_doc_362_);
v___f_366_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed), 3, 1);
lean_closure_set(v___f_366_, 0, v_diagnostic_363_);
v___x_367_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_365_, v___f_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___boxed(lean_object* v_doc_368_, lean_object* v_diagnostic_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(v_doc_368_, v_diagnostic_369_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(lean_object* v___y_372_){
_start:
{
lean_object* v___x_374_; lean_object* v_stickyDiagsRef_375_; lean_object* v_diags_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_374_ = lean_st_ref_get(v___y_372_);
v_stickyDiagsRef_375_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_stickyDiagsRef_375_);
v_diags_376_ = lean_ctor_get(v___x_374_, 1);
lean_inc_ref(v_diags_376_);
lean_dec(v___x_374_);
v___x_377_ = lean_st_ref_get(v_stickyDiagsRef_375_);
lean_dec(v_stickyDiagsRef_375_);
v___x_378_ = l_Lean_PersistentArray_append___redArg(v___x_377_, v_diags_376_);
lean_dec_ref(v_diags_376_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0___boxed(lean_object* v___y_379_, lean_object* v___y_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(v___y_379_);
lean_dec(v___y_379_);
return v_res_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(lean_object* v_doc_383_){
_start:
{
lean_object* v_diagnosticsMutex_385_; lean_object* v___f_386_; lean_object* v___x_387_; 
v_diagnosticsMutex_385_ = lean_ctor_get(v_doc_383_, 3);
lean_inc_ref(v_diagnosticsMutex_385_);
lean_dec_ref(v_doc_383_);
v___f_386_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0));
v___x_387_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_385_, v___f_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___boxed(lean_object* v_doc_388_, lean_object* v_a_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(v_doc_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(lean_object* v___y_391_){
_start:
{
lean_object* v___x_393_; lean_object* v_stickyDiagsRef_394_; 
v___x_393_ = lean_st_ref_get(v___y_391_);
v_stickyDiagsRef_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_stickyDiagsRef_394_);
lean_dec(v___x_393_);
return v_stickyDiagsRef_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0___boxed(lean_object* v___y_395_, lean_object* v___y_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(v___y_395_);
lean_dec(v___y_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update(lean_object* v_doc_399_, lean_object* v_newMeta_400_, lean_object* v_newInitSnap_401_){
_start:
{
lean_object* v_diagnosticsMutex_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_418_; 
v_diagnosticsMutex_403_ = lean_ctor_get(v_doc_399_, 3);
v_isSharedCheck_418_ = !lean_is_exclusive(v_doc_399_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; lean_object* v_unused_420_; lean_object* v_unused_421_; 
v_unused_419_ = lean_ctor_get(v_doc_399_, 2);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_doc_399_, 1);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_doc_399_, 0);
lean_dec(v_unused_421_);
v___x_405_ = v_doc_399_;
v_isShared_406_ = v_isSharedCheck_418_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_diagnosticsMutex_403_);
lean_dec(v_doc_399_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_418_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___f_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___f_407_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0));
v___x_408_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_403_, v___f_407_);
v___x_409_ = lean_unsigned_to_nat(0u);
v___x_410_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
v___x_411_ = 0;
v___x_412_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_412_, 0, v___x_408_);
lean_ctor_set(v___x_412_, 1, v___x_410_);
lean_ctor_set(v___x_412_, 2, v___x_409_);
lean_ctor_set_uint8(v___x_412_, sizeof(void*)*3, v___x_411_);
v___x_413_ = l_Std_Mutex_new___redArg(v___x_412_);
lean_inc_ref(v_newInitSnap_401_);
v___x_414_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(v_newInitSnap_401_);
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 3, v___x_413_);
lean_ctor_set(v___x_405_, 2, v___x_414_);
lean_ctor_set(v___x_405_, 1, v_newInitSnap_401_);
lean_ctor_set(v___x_405_, 0, v_newMeta_400_);
v___x_416_ = v___x_405_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_newMeta_400_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_newInitSnap_401_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v___x_413_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___boxed(lean_object* v_doc_422_, lean_object* v_newMeta_423_, lean_object* v_newInitSnap_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Lean_Server_FileWorker_EditableDocumentCore_update(v_doc_422_, v_newMeta_423_, v_newInitSnap_424_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(lean_object* v_as_427_, size_t v_i_428_, size_t v_stop_429_, lean_object* v_b_430_){
_start:
{
uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_eq(v_i_428_, v_stop_429_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; size_t v___x_435_; size_t v___x_436_; 
v___x_432_ = lean_array_uget_borrowed(v_as_427_, v_i_428_);
lean_inc(v___x_432_);
v___x_433_ = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(v___x_432_);
v___x_434_ = lean_array_push(v_b_430_, v___x_433_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_add(v_i_428_, v___x_435_);
v_i_428_ = v___x_436_;
v_b_430_ = v___x_434_;
goto _start;
}
else
{
return v_b_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1___boxed(lean_object* v_as_438_, lean_object* v_i_439_, lean_object* v_stop_440_, lean_object* v_b_441_){
_start:
{
size_t v_i_boxed_442_; size_t v_stop_boxed_443_; lean_object* v_res_444_; 
v_i_boxed_442_ = lean_unbox_usize(v_i_439_);
lean_dec(v_i_439_);
v_stop_boxed_443_ = lean_unbox_usize(v_stop_440_);
lean_dec(v_stop_440_);
v_res_444_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_as_438_, v_i_boxed_442_, v_stop_boxed_443_, v_b_441_);
lean_dec_ref(v_as_438_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_cs_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_cs_447_ = lean_ctor_get(v_x_445_, 0);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get_size(v_cs_447_);
v___x_450_ = lean_nat_dec_lt(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
return v_x_446_;
}
else
{
size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; 
v___x_451_ = ((size_t)0ULL);
v___x_452_ = lean_usize_of_nat(v___x_449_);
v___x_453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_447_, v___x_451_, v___x_452_, v_x_446_);
return v___x_453_;
}
}
else
{
lean_object* v_vs_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v_vs_454_ = lean_ctor_get(v_x_445_, 0);
v___x_455_ = lean_unsigned_to_nat(0u);
v___x_456_ = lean_array_get_size(v_vs_454_);
v___x_457_ = lean_nat_dec_lt(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
return v_x_446_;
}
else
{
size_t v___x_458_; size_t v___x_459_; lean_object* v___x_460_; 
v___x_458_ = ((size_t)0ULL);
v___x_459_ = lean_usize_of_nat(v___x_456_);
v___x_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_454_, v___x_458_, v___x_459_, v_x_446_);
return v___x_460_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(lean_object* v_as_461_, size_t v_i_462_, size_t v_stop_463_, lean_object* v_b_464_){
_start:
{
uint8_t v___x_465_; 
v___x_465_ = lean_usize_dec_eq(v_i_462_, v_stop_463_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; lean_object* v___x_467_; size_t v___x_468_; size_t v___x_469_; 
v___x_466_ = lean_array_uget_borrowed(v_as_461_, v_i_462_);
v___x_467_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v___x_466_, v_b_464_);
v___x_468_ = ((size_t)1ULL);
v___x_469_ = lean_usize_add(v_i_462_, v___x_468_);
v_i_462_ = v___x_469_;
v_b_464_ = v___x_467_;
goto _start;
}
else
{
return v_b_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1___boxed(lean_object* v_as_471_, lean_object* v_i_472_, lean_object* v_stop_473_, lean_object* v_b_474_){
_start:
{
size_t v_i_boxed_475_; size_t v_stop_boxed_476_; lean_object* v_res_477_; 
v_i_boxed_475_ = lean_unbox_usize(v_i_472_);
lean_dec(v_i_472_);
v_stop_boxed_476_ = lean_unbox_usize(v_stop_473_);
lean_dec(v_stop_473_);
v_res_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_as_471_, v_i_boxed_475_, v_stop_boxed_476_, v_b_474_);
lean_dec_ref(v_as_471_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2___boxed(lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_x_478_, v_x_479_);
lean_dec_ref(v_x_478_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(lean_object* v_x_481_, size_t v_x_482_, size_t v_x_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_object* v_cs_485_; lean_object* v___x_486_; size_t v___x_487_; lean_object* v_j_488_; lean_object* v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_cs_485_ = lean_ctor_get(v_x_481_, 0);
v___x_486_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
v___x_487_ = lean_usize_shift_right(v_x_482_, v_x_483_);
v_j_488_ = lean_usize_to_nat(v___x_487_);
v___x_489_ = lean_array_get_borrowed(v___x_486_, v_cs_485_, v_j_488_);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_shift_left(v___x_490_, v_x_483_);
v___x_492_ = lean_usize_sub(v___x_491_, v___x_490_);
v___x_493_ = lean_usize_land(v_x_482_, v___x_492_);
v___x_494_ = ((size_t)5ULL);
v___x_495_ = lean_usize_sub(v_x_483_, v___x_494_);
v___x_496_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v___x_489_, v___x_493_, v___x_495_, v_x_484_);
v___x_497_ = lean_unsigned_to_nat(1u);
v___x_498_ = lean_nat_add(v_j_488_, v___x_497_);
lean_dec(v_j_488_);
v___x_499_ = lean_array_get_size(v_cs_485_);
v___x_500_ = lean_nat_dec_lt(v___x_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec(v___x_498_);
return v___x_496_;
}
else
{
size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_usize_of_nat(v___x_498_);
lean_dec(v___x_498_);
v___x_502_ = lean_usize_of_nat(v___x_499_);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_485_, v___x_501_, v___x_502_, v___x_496_);
return v___x_503_;
}
}
else
{
lean_object* v_vs_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_vs_504_ = lean_ctor_get(v_x_481_, 0);
v___x_505_ = lean_usize_to_nat(v_x_482_);
v___x_506_ = lean_array_get_size(v_vs_504_);
v___x_507_ = lean_nat_dec_lt(v___x_505_, v___x_506_);
if (v___x_507_ == 0)
{
lean_dec(v___x_505_);
return v_x_484_;
}
else
{
size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_usize_of_nat(v___x_505_);
lean_dec(v___x_505_);
v___x_509_ = lean_usize_of_nat(v___x_506_);
v___x_510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_504_, v___x_508_, v___x_509_, v_x_484_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0___boxed(lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_x_514_){
_start:
{
size_t v_x_2403__boxed_515_; size_t v_x_2404__boxed_516_; lean_object* v_res_517_; 
v_x_2403__boxed_515_ = lean_unbox_usize(v_x_512_);
lean_dec(v_x_512_);
v_x_2404__boxed_516_ = lean_unbox_usize(v_x_513_);
lean_dec(v_x_513_);
v_res_517_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_x_511_, v_x_2403__boxed_515_, v_x_2404__boxed_516_, v_x_514_);
lean_dec_ref(v_x_511_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(lean_object* v_t_518_, lean_object* v_init_519_, lean_object* v_start_520_){
_start:
{
lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_521_ = lean_unsigned_to_nat(0u);
v___x_522_ = lean_nat_dec_eq(v_start_520_, v___x_521_);
if (v___x_522_ == 0)
{
lean_object* v_root_523_; lean_object* v_tail_524_; size_t v_shift_525_; lean_object* v_tailOff_526_; uint8_t v___x_527_; 
v_root_523_ = lean_ctor_get(v_t_518_, 0);
v_tail_524_ = lean_ctor_get(v_t_518_, 1);
v_shift_525_ = lean_ctor_get_usize(v_t_518_, 4);
v_tailOff_526_ = lean_ctor_get(v_t_518_, 3);
v___x_527_ = lean_nat_dec_le(v_tailOff_526_, v_start_520_);
if (v___x_527_ == 0)
{
size_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_528_ = lean_usize_of_nat(v_start_520_);
v___x_529_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_523_, v___x_528_, v_shift_525_, v_init_519_);
v___x_530_ = lean_array_get_size(v_tail_524_);
v___x_531_ = lean_nat_dec_lt(v___x_521_, v___x_530_);
if (v___x_531_ == 0)
{
return v___x_529_;
}
else
{
size_t v___x_532_; size_t v___x_533_; lean_object* v___x_534_; 
v___x_532_ = ((size_t)0ULL);
v___x_533_ = lean_usize_of_nat(v___x_530_);
v___x_534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_524_, v___x_532_, v___x_533_, v___x_529_);
return v___x_534_;
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_535_ = lean_nat_sub(v_start_520_, v_tailOff_526_);
v___x_536_ = lean_array_get_size(v_tail_524_);
v___x_537_ = lean_nat_dec_lt(v___x_535_, v___x_536_);
if (v___x_537_ == 0)
{
lean_dec(v___x_535_);
return v_init_519_;
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_usize_of_nat(v___x_535_);
lean_dec(v___x_535_);
v___x_539_ = lean_usize_of_nat(v___x_536_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_524_, v___x_538_, v___x_539_, v_init_519_);
return v___x_540_;
}
}
}
else
{
lean_object* v_root_541_; lean_object* v_tail_542_; lean_object* v___x_543_; lean_object* v___x_544_; uint8_t v___x_545_; 
v_root_541_ = lean_ctor_get(v_t_518_, 0);
v_tail_542_ = lean_ctor_get(v_t_518_, 1);
v___x_543_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_541_, v_init_519_);
v___x_544_ = lean_array_get_size(v_tail_542_);
v___x_545_ = lean_nat_dec_lt(v___x_521_, v___x_544_);
if (v___x_545_ == 0)
{
return v___x_543_;
}
else
{
size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
v___x_546_ = ((size_t)0ULL);
v___x_547_ = lean_usize_of_nat(v___x_544_);
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_542_, v___x_546_, v___x_547_, v___x_543_);
return v___x_548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1___boxed(lean_object* v_t_549_, lean_object* v_init_550_, lean_object* v_start_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_t_549_, v_init_550_, v_start_551_);
lean_dec(v_start_551_);
lean_dec_ref(v_t_549_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(lean_object* v_t_553_, lean_object* v_init_554_, lean_object* v_start_555_){
_start:
{
lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_nat_dec_eq(v_start_555_, v___x_556_);
if (v___x_557_ == 0)
{
lean_object* v_root_558_; lean_object* v_tail_559_; size_t v_shift_560_; lean_object* v_tailOff_561_; uint8_t v___x_562_; 
v_root_558_ = lean_ctor_get(v_t_553_, 0);
v_tail_559_ = lean_ctor_get(v_t_553_, 1);
v_shift_560_ = lean_ctor_get_usize(v_t_553_, 4);
v_tailOff_561_ = lean_ctor_get(v_t_553_, 3);
v___x_562_ = lean_nat_dec_le(v_tailOff_561_, v_start_555_);
if (v___x_562_ == 0)
{
size_t v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_563_ = lean_usize_of_nat(v_start_555_);
v___x_564_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_558_, v___x_563_, v_shift_560_, v_init_554_);
v___x_565_ = lean_array_get_size(v_tail_559_);
v___x_566_ = lean_nat_dec_lt(v___x_556_, v___x_565_);
if (v___x_566_ == 0)
{
return v___x_564_;
}
else
{
size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((size_t)0ULL);
v___x_568_ = lean_usize_of_nat(v___x_565_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_559_, v___x_567_, v___x_568_, v___x_564_);
return v___x_569_;
}
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_570_ = lean_nat_sub(v_start_555_, v_tailOff_561_);
v___x_571_ = lean_array_get_size(v_tail_559_);
v___x_572_ = lean_nat_dec_lt(v___x_570_, v___x_571_);
if (v___x_572_ == 0)
{
lean_dec(v___x_570_);
return v_init_554_;
}
else
{
size_t v___x_573_; size_t v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_usize_of_nat(v___x_570_);
lean_dec(v___x_570_);
v___x_574_ = lean_usize_of_nat(v___x_571_);
v___x_575_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_559_, v___x_573_, v___x_574_, v_init_554_);
return v___x_575_;
}
}
}
else
{
lean_object* v_root_576_; lean_object* v_tail_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_root_576_ = lean_ctor_get(v_t_553_, 0);
v_tail_577_ = lean_ctor_get(v_t_553_, 1);
v___x_578_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_576_, v_init_554_);
v___x_579_ = lean_array_get_size(v_tail_577_);
v___x_580_ = lean_nat_dec_lt(v___x_556_, v___x_579_);
if (v___x_580_ == 0)
{
return v___x_578_;
}
else
{
size_t v___x_581_; size_t v___x_582_; lean_object* v___x_583_; 
v___x_581_ = ((size_t)0ULL);
v___x_582_ = lean_usize_of_nat(v___x_579_);
v___x_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_577_, v___x_581_, v___x_582_, v___x_578_);
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0___boxed(lean_object* v_t_584_, lean_object* v_init_585_, lean_object* v_start_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_t_584_, v_init_585_, v_start_586_);
lean_dec(v_start_586_);
lean_dec_ref(v_t_584_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(lean_object* v_meta_590_, lean_object* v_writeDiagnostics_591_, uint8_t v_incrementalDiagnosticSupport_592_, lean_object* v___y_593_){
_start:
{
lean_object* v___y_596_; lean_object* v___y_597_; lean_object* v_fst_601_; uint8_t v_snd_602_; lean_object* v___x_606_; uint8_t v___y_608_; 
v___x_606_ = lean_st_ref_get(v___y_593_);
if (v_incrementalDiagnosticSupport_592_ == 0)
{
v___y_608_ = v_incrementalDiagnosticSupport_592_;
goto v___jp_607_;
}
else
{
uint8_t v_isIncremental_629_; 
v_isIncremental_629_ = lean_ctor_get_uint8(v___x_606_, sizeof(void*)*3);
v___y_608_ = v_isIncremental_629_;
goto v___jp_607_;
}
v___jp_595_:
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = l_Lean_Server_mkPublishDiagnosticsNotification(v_meta_590_, v___y_596_, v___y_597_);
v___x_599_ = lean_apply_2(v_writeDiagnostics_591_, v___x_598_, lean_box(0));
return v___x_599_;
}
v___jp_600_:
{
if (v_incrementalDiagnosticSupport_592_ == 0)
{
lean_object* v___x_603_; 
v___x_603_ = lean_box(0);
v___y_596_ = v_fst_601_;
v___y_597_ = v___x_603_;
goto v___jp_595_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = lean_box(v_snd_602_);
v___x_605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_605_, 0, v___x_604_);
v___y_596_ = v_fst_601_;
v___y_597_ = v___x_605_;
goto v___jp_595_;
}
}
v___jp_607_:
{
lean_object* v_stickyDiagsRef_609_; lean_object* v_diags_610_; lean_object* v_publishedDiagsAmount_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_628_; 
v_stickyDiagsRef_609_ = lean_ctor_get(v___x_606_, 0);
v_diags_610_ = lean_ctor_get(v___x_606_, 1);
v_publishedDiagsAmount_611_ = lean_ctor_get(v___x_606_, 2);
v_isSharedCheck_628_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_628_ == 0)
{
v___x_613_ = v___x_606_;
v_isShared_614_ = v_isSharedCheck_628_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_publishedDiagsAmount_611_);
lean_inc(v_diags_610_);
lean_inc(v_stickyDiagsRef_609_);
lean_dec(v___x_606_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_628_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_615_; lean_object* v_size_616_; uint8_t v___x_617_; lean_object* v___x_619_; 
v___x_615_ = lean_st_ref_get(v_stickyDiagsRef_609_);
v_size_616_ = lean_ctor_get(v_diags_610_, 2);
v___x_617_ = 1;
lean_inc(v_size_616_);
lean_inc_ref(v_diags_610_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 2, v_size_616_);
v___x_619_ = v___x_613_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_stickyDiagsRef_609_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_diags_610_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_size_616_);
v___x_619_ = v_reuseFailAlloc_627_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; 
lean_ctor_set_uint8(v___x_619_, sizeof(void*)*3, v___x_617_);
v___x_620_ = lean_st_ref_swap(v___y_593_, v___x_619_);
lean_dec(v___x_620_);
if (v___y_608_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; 
lean_dec(v_publishedDiagsAmount_611_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_623_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v___x_615_, v___x_622_, v___x_621_);
lean_dec(v___x_615_);
v___x_624_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_diags_610_, v___x_623_, v___x_621_);
lean_dec_ref(v_diags_610_);
v_fst_601_ = v___x_624_;
v_snd_602_ = v___y_608_;
goto v___jp_600_;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v___x_615_);
v___x_625_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_626_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_diags_610_, v___x_625_, v_publishedDiagsAmount_611_);
lean_dec(v_publishedDiagsAmount_611_);
lean_dec_ref(v_diags_610_);
v_fst_601_ = v___x_626_;
v_snd_602_ = v___x_617_;
goto v___jp_600_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed(lean_object* v_meta_630_, lean_object* v_writeDiagnostics_631_, lean_object* v_incrementalDiagnosticSupport_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_635_; lean_object* v_res_636_; 
v_incrementalDiagnosticSupport_boxed_635_ = lean_unbox(v_incrementalDiagnosticSupport_632_);
v_res_636_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(v_meta_630_, v_writeDiagnostics_631_, v_incrementalDiagnosticSupport_boxed_635_, v___y_633_);
lean_dec(v___y_633_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(lean_object* v_doc_637_, uint8_t v_incrementalDiagnosticSupport_638_, lean_object* v_writeDiagnostics_639_){
_start:
{
lean_object* v_meta_641_; lean_object* v_diagnosticsMutex_642_; lean_object* v___x_643_; lean_object* v___f_644_; lean_object* v___x_645_; 
v_meta_641_ = lean_ctor_get(v_doc_637_, 0);
lean_inc_ref(v_meta_641_);
v_diagnosticsMutex_642_ = lean_ctor_get(v_doc_637_, 3);
lean_inc_ref(v_diagnosticsMutex_642_);
lean_dec_ref(v_doc_637_);
v___x_643_ = lean_box(v_incrementalDiagnosticSupport_638_);
v___f_644_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed), 5, 3);
lean_closure_set(v___f_644_, 0, v_meta_641_);
lean_closure_set(v___f_644_, 1, v_writeDiagnostics_639_);
lean_closure_set(v___f_644_, 2, v___x_643_);
v___x_645_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_642_, v___f_644_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___boxed(lean_object* v_doc_646_, lean_object* v_incrementalDiagnosticSupport_647_, lean_object* v_writeDiagnostics_648_, lean_object* v_a_649_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_650_; lean_object* v_res_651_; 
v_incrementalDiagnosticSupport_boxed_650_ = lean_unbox(v_incrementalDiagnosticSupport_647_);
v_res_651_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(v_doc_646_, v_incrementalDiagnosticSupport_boxed_650_, v_writeDiagnostics_648_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object* v_ed_652_){
_start:
{
lean_object* v_toEditableDocumentCore_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_664_; 
v_toEditableDocumentCore_653_ = lean_ctor_get(v_ed_652_, 0);
v_isSharedCheck_664_ = !lean_is_exclusive(v_ed_652_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v_ed_652_, 1);
lean_dec(v_unused_665_);
v___x_655_ = v_ed_652_;
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_toEditableDocumentCore_653_);
lean_dec(v_ed_652_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_664_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
lean_object* v_meta_657_; lean_object* v_uri_658_; lean_object* v_version_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v_meta_657_ = lean_ctor_get(v_toEditableDocumentCore_653_, 0);
lean_inc_ref(v_meta_657_);
lean_dec_ref(v_toEditableDocumentCore_653_);
v_uri_658_ = lean_ctor_get(v_meta_657_, 0);
lean_inc_ref(v_uri_658_);
v_version_659_ = lean_ctor_get(v_meta_657_, 2);
lean_inc(v_version_659_);
lean_dec_ref(v_meta_657_);
v___x_660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_660_, 0, v_version_659_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 1, v___x_660_);
lean_ctor_set(v___x_655_, 0, v_uri_658_);
v___x_662_ = v___x_655_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_uri_658_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs(void){
_start:
{
lean_object* v___x_666_; 
v___x_666_ = lean_unsigned_to_nat(30000u);
return v___x_666_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0(void){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_667_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__0, &l_Lean_Server_FileWorker_RpcSession_new___closed__0_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new(uint8_t v_wireFormat_670_){
_start:
{
size_t v___x_672_; lean_object* v___x_673_; 
v___x_672_ = ((size_t)8ULL);
v___x_673_ = lean_io_get_random_bytes(v___x_672_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_691_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_691_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_691_ == 0)
{
v___x_676_ = v___x_673_;
v_isShared_677_ = v_isSharedCheck_691_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_a_674_);
lean_dec(v___x_673_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_691_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v___x_678_; uint64_t v___x_679_; lean_object* v___x_680_; size_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v___x_678_ = lean_io_mono_ms_now();
v___x_679_ = l_ByteArray_toUInt64LE_x21(v_a_674_);
lean_dec(v_a_674_);
v___x_680_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__1, &l_Lean_Server_FileWorker_RpcSession_new___closed__1_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1);
v___x_681_ = ((size_t)0ULL);
v___x_682_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_682_, 0, v___x_680_);
lean_ctor_set(v___x_682_, 1, v___x_680_);
lean_ctor_set_usize(v___x_682_, 2, v___x_681_);
lean_ctor_set_uint8(v___x_682_, sizeof(void*)*3, v_wireFormat_670_);
v___x_683_ = lean_unsigned_to_nat(30000u);
v___x_684_ = lean_nat_add(v___x_678_, v___x_683_);
lean_dec(v___x_678_);
v___x_685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_685_, 0, v___x_682_);
lean_ctor_set(v___x_685_, 1, v___x_684_);
v___x_686_ = lean_box_uint64(v___x_679_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___x_685_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_687_);
v___x_689_ = v___x_676_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
return v___x_689_;
}
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
v_a_692_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_673_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_673_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new___boxed(lean_object* v_wireFormat_700_, lean_object* v_a_701_){
_start:
{
uint8_t v_wireFormat_boxed_702_; lean_object* v_res_703_; 
v_wireFormat_boxed_702_ = lean_unbox(v_wireFormat_700_);
v_res_703_ = l_Lean_Server_FileWorker_RpcSession_new(v_wireFormat_boxed_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object* v_monoMsNow_704_, lean_object* v_s_705_){
_start:
{
lean_object* v_objects_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_715_; 
v_objects_706_ = lean_ctor_get(v_s_705_, 0);
v_isSharedCheck_715_ = !lean_is_exclusive(v_s_705_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v_s_705_, 1);
lean_dec(v_unused_716_);
v___x_708_ = v_s_705_;
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_objects_706_);
lean_dec(v_s_705_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_715_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_710_ = lean_unsigned_to_nat(30000u);
v___x_711_ = lean_nat_add(v_monoMsNow_704_, v___x_710_);
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 1, v___x_711_);
v___x_713_ = v___x_708_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_objects_706_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_711_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object* v_monoMsNow_717_, lean_object* v_s_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Server_FileWorker_RpcSession_keptAlive(v_monoMsNow_717_, v_s_718_);
lean_dec(v_monoMsNow_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object* v_s_720_){
_start:
{
lean_object* v___x_722_; lean_object* v_expireTime_723_; uint8_t v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_722_ = lean_io_mono_ms_now();
v_expireTime_723_ = lean_ctor_get(v_s_720_, 1);
v___x_724_ = lean_nat_dec_le(v_expireTime_723_, v___x_722_);
lean_dec(v___x_722_);
v___x_725_ = lean_box(v___x_724_);
v___x_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object* v_s_727_, lean_object* v_a_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Lean_Server_FileWorker_RpcSession_hasExpired(v_s_727_);
lean_dec_ref(v_s_727_);
return v_res_729_;
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
