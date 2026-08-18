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
uint8_t v___x_216_; 
v___x_216_ = lean_nat_dec_le(v___x_214_, v___x_214_);
if (v___x_216_ == 0)
{
if (v___x_215_ == 0)
{
lean_dec_ref(v_diagnostic_209_);
return v_x_211_;
}
else
{
size_t v___x_217_; size_t v___x_218_; lean_object* v___x_219_; 
v___x_217_ = ((size_t)0ULL);
v___x_218_ = lean_usize_of_nat(v___x_214_);
v___x_219_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_209_, v_cs_212_, v___x_217_, v___x_218_, v_x_211_);
return v___x_219_;
}
}
else
{
size_t v___x_220_; size_t v___x_221_; lean_object* v___x_222_; 
v___x_220_ = ((size_t)0ULL);
v___x_221_ = lean_usize_of_nat(v___x_214_);
v___x_222_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_209_, v_cs_212_, v___x_220_, v___x_221_, v_x_211_);
return v___x_222_;
}
}
}
else
{
lean_object* v_vs_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v_vs_223_ = lean_ctor_get(v_x_210_, 0);
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_array_get_size(v_vs_223_);
v___x_226_ = lean_nat_dec_lt(v___x_224_, v___x_225_);
if (v___x_226_ == 0)
{
lean_dec_ref(v_diagnostic_209_);
return v_x_211_;
}
else
{
uint8_t v___x_227_; 
v___x_227_ = lean_nat_dec_le(v___x_225_, v___x_225_);
if (v___x_227_ == 0)
{
if (v___x_226_ == 0)
{
lean_dec_ref(v_diagnostic_209_);
return v_x_211_;
}
else
{
size_t v___x_228_; size_t v___x_229_; lean_object* v___x_230_; 
v___x_228_ = ((size_t)0ULL);
v___x_229_ = lean_usize_of_nat(v___x_225_);
v___x_230_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_209_, v_vs_223_, v___x_228_, v___x_229_, v_x_211_);
return v___x_230_;
}
}
else
{
size_t v___x_231_; size_t v___x_232_; lean_object* v___x_233_; 
v___x_231_ = ((size_t)0ULL);
v___x_232_ = lean_usize_of_nat(v___x_225_);
v___x_233_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_209_, v_vs_223_, v___x_231_, v___x_232_, v_x_211_);
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(lean_object* v_diagnostic_234_, lean_object* v_as_235_, size_t v_i_236_, size_t v_stop_237_, lean_object* v_b_238_){
_start:
{
uint8_t v___x_239_; 
v___x_239_ = lean_usize_dec_eq(v_i_236_, v_stop_237_);
if (v___x_239_ == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; size_t v___x_242_; size_t v___x_243_; 
v___x_240_ = lean_array_uget_borrowed(v_as_235_, v_i_236_);
lean_inc_ref(v_diagnostic_234_);
v___x_241_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_234_, v___x_240_, v_b_238_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_add(v_i_236_, v___x_242_);
v_i_236_ = v___x_243_;
v_b_238_ = v___x_241_;
goto _start;
}
else
{
lean_dec_ref(v_diagnostic_234_);
return v_b_238_;
}
}
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
v___x_257_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(lean_object* v_diagnostic_258_, lean_object* v_x_259_, size_t v_x_260_, size_t v_x_261_, lean_object* v_x_262_){
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
uint8_t v___x_279_; 
v___x_279_ = lean_nat_dec_le(v___x_277_, v___x_277_);
if (v___x_279_ == 0)
{
if (v___x_278_ == 0)
{
lean_dec(v___x_276_);
lean_dec_ref(v_diagnostic_258_);
return v___x_274_;
}
else
{
size_t v___x_280_; size_t v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_usize_of_nat(v___x_276_);
lean_dec(v___x_276_);
v___x_281_ = lean_usize_of_nat(v___x_277_);
v___x_282_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_258_, v_cs_263_, v___x_280_, v___x_281_, v___x_274_);
return v___x_282_;
}
}
else
{
size_t v___x_283_; size_t v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_usize_of_nat(v___x_276_);
lean_dec(v___x_276_);
v___x_284_ = lean_usize_of_nat(v___x_277_);
v___x_285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0_spec__1(v_diagnostic_258_, v_cs_263_, v___x_283_, v___x_284_, v___x_274_);
return v___x_285_;
}
}
}
else
{
lean_object* v_vs_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_vs_286_ = lean_ctor_get(v_x_259_, 0);
v___x_287_ = lean_usize_to_nat(v_x_260_);
v___x_288_ = lean_array_get_size(v_vs_286_);
v___x_289_ = lean_nat_dec_lt(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_dec(v___x_287_);
lean_dec_ref(v_diagnostic_258_);
return v_x_262_;
}
else
{
uint8_t v___x_290_; 
v___x_290_ = lean_nat_dec_le(v___x_288_, v___x_288_);
if (v___x_290_ == 0)
{
if (v___x_289_ == 0)
{
lean_dec(v___x_287_);
lean_dec_ref(v_diagnostic_258_);
return v_x_262_;
}
else
{
size_t v___x_291_; size_t v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_usize_of_nat(v___x_287_);
lean_dec(v___x_287_);
v___x_292_ = lean_usize_of_nat(v___x_288_);
v___x_293_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_258_, v_vs_286_, v___x_291_, v___x_292_, v_x_262_);
return v___x_293_;
}
}
else
{
size_t v___x_294_; size_t v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_usize_of_nat(v___x_287_);
lean_dec(v___x_287_);
v___x_295_ = lean_usize_of_nat(v___x_288_);
v___x_296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_258_, v_vs_286_, v___x_294_, v___x_295_, v_x_262_);
return v___x_296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___boxed(lean_object* v_diagnostic_297_, lean_object* v_x_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_x_301_){
_start:
{
size_t v_x_1932__boxed_302_; size_t v_x_1933__boxed_303_; lean_object* v_res_304_; 
v_x_1932__boxed_302_ = lean_unbox_usize(v_x_299_);
lean_dec(v_x_299_);
v_x_1933__boxed_303_ = lean_unbox_usize(v_x_300_);
lean_dec(v_x_300_);
v_res_304_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_297_, v_x_298_, v_x_1932__boxed_302_, v_x_1933__boxed_303_, v_x_301_);
lean_dec_ref(v_x_298_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(lean_object* v_diagnostic_305_, lean_object* v_t_306_, lean_object* v_init_307_, lean_object* v_start_308_){
_start:
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = lean_unsigned_to_nat(0u);
v___x_310_ = lean_nat_dec_eq(v_start_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v_root_311_; lean_object* v_tail_312_; size_t v_shift_313_; lean_object* v_tailOff_314_; uint8_t v___x_315_; 
v_root_311_ = lean_ctor_get(v_t_306_, 0);
v_tail_312_ = lean_ctor_get(v_t_306_, 1);
v_shift_313_ = lean_ctor_get_usize(v_t_306_, 4);
v_tailOff_314_ = lean_ctor_get(v_t_306_, 3);
v___x_315_ = lean_nat_dec_le(v_tailOff_314_, v_start_308_);
if (v___x_315_ == 0)
{
size_t v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_316_ = lean_usize_of_nat(v_start_308_);
lean_inc_ref(v_diagnostic_305_);
v___x_317_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0(v_diagnostic_305_, v_root_311_, v___x_316_, v_shift_313_, v_init_307_);
v___x_318_ = lean_array_get_size(v_tail_312_);
v___x_319_ = lean_nat_dec_lt(v___x_309_, v___x_318_);
if (v___x_319_ == 0)
{
lean_dec_ref(v_diagnostic_305_);
return v___x_317_;
}
else
{
uint8_t v___x_320_; 
v___x_320_ = lean_nat_dec_le(v___x_318_, v___x_318_);
if (v___x_320_ == 0)
{
if (v___x_319_ == 0)
{
lean_dec_ref(v_diagnostic_305_);
return v___x_317_;
}
else
{
size_t v___x_321_; size_t v___x_322_; lean_object* v___x_323_; 
v___x_321_ = ((size_t)0ULL);
v___x_322_ = lean_usize_of_nat(v___x_318_);
v___x_323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_305_, v_tail_312_, v___x_321_, v___x_322_, v___x_317_);
return v___x_323_;
}
}
else
{
size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; 
v___x_324_ = ((size_t)0ULL);
v___x_325_ = lean_usize_of_nat(v___x_318_);
v___x_326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_305_, v_tail_312_, v___x_324_, v___x_325_, v___x_317_);
return v___x_326_;
}
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_327_ = lean_nat_sub(v_start_308_, v_tailOff_314_);
v___x_328_ = lean_array_get_size(v_tail_312_);
v___x_329_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_dec(v___x_327_);
lean_dec_ref(v_diagnostic_305_);
return v_init_307_;
}
else
{
uint8_t v___x_330_; 
v___x_330_ = lean_nat_dec_le(v___x_328_, v___x_328_);
if (v___x_330_ == 0)
{
if (v___x_329_ == 0)
{
lean_dec(v___x_327_);
lean_dec_ref(v_diagnostic_305_);
return v_init_307_;
}
else
{
size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; 
v___x_331_ = lean_usize_of_nat(v___x_327_);
lean_dec(v___x_327_);
v___x_332_ = lean_usize_of_nat(v___x_328_);
v___x_333_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_305_, v_tail_312_, v___x_331_, v___x_332_, v_init_307_);
return v___x_333_;
}
}
else
{
size_t v___x_334_; size_t v___x_335_; lean_object* v___x_336_; 
v___x_334_ = lean_usize_of_nat(v___x_327_);
lean_dec(v___x_327_);
v___x_335_ = lean_usize_of_nat(v___x_328_);
v___x_336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_305_, v_tail_312_, v___x_334_, v___x_335_, v_init_307_);
return v___x_336_;
}
}
}
}
else
{
lean_object* v_root_337_; lean_object* v_tail_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_root_337_ = lean_ctor_get(v_t_306_, 0);
v_tail_338_ = lean_ctor_get(v_t_306_, 1);
lean_inc_ref(v_diagnostic_305_);
v___x_339_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__2(v_diagnostic_305_, v_root_337_, v_init_307_);
v___x_340_ = lean_array_get_size(v_tail_338_);
v___x_341_ = lean_nat_dec_lt(v___x_309_, v___x_340_);
if (v___x_341_ == 0)
{
lean_dec_ref(v_diagnostic_305_);
return v___x_339_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = lean_nat_dec_le(v___x_340_, v___x_340_);
if (v___x_342_ == 0)
{
if (v___x_341_ == 0)
{
lean_dec_ref(v_diagnostic_305_);
return v___x_339_;
}
else
{
size_t v___x_343_; size_t v___x_344_; lean_object* v___x_345_; 
v___x_343_ = ((size_t)0ULL);
v___x_344_ = lean_usize_of_nat(v___x_340_);
v___x_345_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_305_, v_tail_338_, v___x_343_, v___x_344_, v___x_339_);
return v___x_345_;
}
}
else
{
size_t v___x_346_; size_t v___x_347_; lean_object* v___x_348_; 
v___x_346_ = ((size_t)0ULL);
v___x_347_ = lean_usize_of_nat(v___x_340_);
v___x_348_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__1(v_diagnostic_305_, v_tail_338_, v___x_346_, v___x_347_, v___x_339_);
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0___boxed(lean_object* v_diagnostic_349_, lean_object* v_t_350_, lean_object* v_init_351_, lean_object* v_start_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_349_, v_t_350_, v_init_351_, v_start_352_);
lean_dec(v_start_352_);
lean_dec_ref(v_t_350_);
return v_res_353_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_unsigned_to_nat(32u);
v___x_355_ = lean_mk_empty_array_with_capacity(v___x_354_);
v___x_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_356_, 0, v___x_355_);
return v___x_356_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1(void){
_start:
{
size_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_357_ = ((size_t)5ULL);
v___x_358_ = lean_unsigned_to_nat(0u);
v___x_359_ = lean_unsigned_to_nat(32u);
v___x_360_ = lean_mk_empty_array_with_capacity(v___x_359_);
v___x_361_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__0);
v___x_362_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set(v___x_362_, 1, v___x_360_);
lean_ctor_set(v___x_362_, 2, v___x_358_);
lean_ctor_set(v___x_362_, 3, v___x_358_);
lean_ctor_set_usize(v___x_362_, 4, v___x_357_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(lean_object* v_diagnostic_363_, lean_object* v___y_364_){
_start:
{
lean_object* v___x_366_; lean_object* v_stickyDiagsRef_367_; lean_object* v_diags_368_; lean_object* v_publishedDiagsAmount_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_385_; 
v___x_366_ = lean_st_ref_get(v___y_364_);
v_stickyDiagsRef_367_ = lean_ctor_get(v___x_366_, 0);
v_diags_368_ = lean_ctor_get(v___x_366_, 1);
v_publishedDiagsAmount_369_ = lean_ctor_get(v___x_366_, 2);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_366_);
if (v_isSharedCheck_385_ == 0)
{
v___x_371_ = v___x_366_;
v_isShared_372_ = v_isSharedCheck_385_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_publishedDiagsAmount_369_);
lean_inc(v_diags_368_);
lean_inc(v_stickyDiagsRef_367_);
lean_dec(v___x_366_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_385_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v_stickyDiags_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_381_; 
v___x_373_ = lean_st_ref_take(v_stickyDiagsRef_367_);
v___x_374_ = lean_unsigned_to_nat(0u);
v___x_375_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
lean_inc_ref(v_diagnostic_363_);
v_stickyDiags_376_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0(v_diagnostic_363_, v___x_373_, v___x_375_, v___x_374_);
lean_dec(v___x_373_);
v___x_377_ = l_Lean_PersistentArray_push___redArg(v_stickyDiags_376_, v_diagnostic_363_);
v___x_378_ = lean_st_ref_put(v_stickyDiagsRef_367_, v___x_377_);
v___x_379_ = 0;
if (v_isShared_372_ == 0)
{
v___x_381_ = v___x_371_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v_stickyDiagsRef_367_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v_diags_368_);
lean_ctor_set(v_reuseFailAlloc_384_, 2, v_publishedDiagsAmount_369_);
v___x_381_ = v_reuseFailAlloc_384_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
lean_ctor_set_uint8(v___x_381_, sizeof(void*)*3, v___x_379_);
v___x_382_ = lean_st_ref_swap(v___y_364_, v___x_381_);
lean_dec(v___x_382_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed(lean_object* v_diagnostic_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0(v_diagnostic_386_, v___y_387_);
lean_dec(v___y_387_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(lean_object* v_doc_390_, lean_object* v_diagnostic_391_){
_start:
{
lean_object* v_diagnosticsMutex_393_; lean_object* v___f_394_; lean_object* v___x_395_; 
v_diagnosticsMutex_393_ = lean_ctor_get(v_doc_390_, 3);
lean_inc_ref(v_diagnosticsMutex_393_);
lean_dec_ref(v_doc_390_);
v___f_394_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___boxed), 3, 1);
lean_closure_set(v___f_394_, 0, v_diagnostic_391_);
v___x_395_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_393_, v___f_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___boxed(lean_object* v_doc_396_, lean_object* v_diagnostic_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic(v_doc_396_, v_diagnostic_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(lean_object* v___y_400_){
_start:
{
lean_object* v___x_402_; lean_object* v_stickyDiagsRef_403_; lean_object* v_diags_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v___x_402_ = lean_st_ref_get(v___y_400_);
v_stickyDiagsRef_403_ = lean_ctor_get(v___x_402_, 0);
lean_inc(v_stickyDiagsRef_403_);
v_diags_404_ = lean_ctor_get(v___x_402_, 1);
lean_inc_ref(v_diags_404_);
lean_dec(v___x_402_);
v___x_405_ = lean_st_ref_get(v_stickyDiagsRef_403_);
lean_dec(v_stickyDiagsRef_403_);
v___x_406_ = l_Lean_PersistentArray_append___redArg(v___x_405_, v_diags_404_);
lean_dec_ref(v_diags_404_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0___boxed(lean_object* v___y_407_, lean_object* v___y_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___lam__0(v___y_407_);
lean_dec(v___y_407_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(lean_object* v_doc_411_){
_start:
{
lean_object* v_diagnosticsMutex_413_; lean_object* v___f_414_; lean_object* v___x_415_; 
v_diagnosticsMutex_413_ = lean_ctor_get(v_doc_411_, 3);
lean_inc_ref(v_diagnosticsMutex_413_);
lean_dec_ref(v_doc_411_);
v___f_414_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___closed__0));
v___x_415_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_413_, v___f_414_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics___boxed(lean_object* v_doc_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_Server_FileWorker_EditableDocumentCore_collectCurrentDiagnostics(v_doc_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(lean_object* v___y_419_){
_start:
{
lean_object* v___x_421_; lean_object* v_stickyDiagsRef_422_; 
v___x_421_ = lean_st_ref_get(v___y_419_);
v_stickyDiagsRef_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_stickyDiagsRef_422_);
lean_dec(v___x_421_);
return v_stickyDiagsRef_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0___boxed(lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Lean_Server_FileWorker_EditableDocumentCore_update___lam__0(v___y_423_);
lean_dec(v___y_423_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update(lean_object* v_doc_427_, lean_object* v_newMeta_428_, lean_object* v_newInitSnap_429_){
_start:
{
lean_object* v_diagnosticsMutex_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_446_; 
v_diagnosticsMutex_431_ = lean_ctor_get(v_doc_427_, 3);
v_isSharedCheck_446_ = !lean_is_exclusive(v_doc_427_);
if (v_isSharedCheck_446_ == 0)
{
lean_object* v_unused_447_; lean_object* v_unused_448_; lean_object* v_unused_449_; 
v_unused_447_ = lean_ctor_get(v_doc_427_, 2);
lean_dec(v_unused_447_);
v_unused_448_ = lean_ctor_get(v_doc_427_, 1);
lean_dec(v_unused_448_);
v_unused_449_ = lean_ctor_get(v_doc_427_, 0);
lean_dec(v_unused_449_);
v___x_433_ = v_doc_427_;
v_isShared_434_ = v_isSharedCheck_446_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_diagnosticsMutex_431_);
lean_dec(v_doc_427_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_446_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v___f_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_444_; 
v___f_435_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_update___closed__0));
v___x_436_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_431_, v___f_435_);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_obj_once(&l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1, &l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1_once, _init_l_Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic___lam__0___closed__1);
v___x_439_ = 0;
v___x_440_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_440_, 0, v___x_436_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_437_);
lean_ctor_set_uint8(v___x_440_, sizeof(void*)*3, v___x_439_);
v___x_441_ = l_Std_Mutex_new___redArg(v___x_440_);
lean_inc_ref(v_newInitSnap_429_);
v___x_442_ = l___private_Lean_Server_FileWorker_Utils_0__Lean_Server_FileWorker_mkCmdSnaps(v_newInitSnap_429_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 3, v___x_441_);
lean_ctor_set(v___x_433_, 2, v___x_442_);
lean_ctor_set(v___x_433_, 1, v_newInitSnap_429_);
lean_ctor_set(v___x_433_, 0, v_newMeta_428_);
v___x_444_ = v___x_433_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_newMeta_428_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_newInitSnap_429_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v___x_442_);
lean_ctor_set(v_reuseFailAlloc_445_, 3, v___x_441_);
v___x_444_ = v_reuseFailAlloc_445_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
return v___x_444_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_update___boxed(lean_object* v_doc_450_, lean_object* v_newMeta_451_, lean_object* v_newInitSnap_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_Server_FileWorker_EditableDocumentCore_update(v_doc_450_, v_newMeta_451_, v_newInitSnap_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(lean_object* v_as_455_, size_t v_i_456_, size_t v_stop_457_, lean_object* v_b_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_eq(v_i_456_, v_stop_457_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; size_t v___x_463_; size_t v___x_464_; 
v___x_460_ = lean_array_uget_borrowed(v_as_455_, v_i_456_);
lean_inc(v___x_460_);
v___x_461_ = l_Lean_Widget_InteractiveDiagnostic_toDiagnostic(v___x_460_);
v___x_462_ = lean_array_push(v_b_458_, v___x_461_);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_add(v_i_456_, v___x_463_);
v_i_456_ = v___x_464_;
v_b_458_ = v___x_462_;
goto _start;
}
else
{
return v_b_458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1___boxed(lean_object* v_as_466_, lean_object* v_i_467_, lean_object* v_stop_468_, lean_object* v_b_469_){
_start:
{
size_t v_i_boxed_470_; size_t v_stop_boxed_471_; lean_object* v_res_472_; 
v_i_boxed_470_ = lean_unbox_usize(v_i_467_);
lean_dec(v_i_467_);
v_stop_boxed_471_ = lean_unbox_usize(v_stop_468_);
lean_dec(v_stop_468_);
v_res_472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_as_466_, v_i_boxed_470_, v_stop_boxed_471_, v_b_469_);
lean_dec_ref(v_as_466_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(lean_object* v_x_473_, lean_object* v_x_474_){
_start:
{
if (lean_obj_tag(v_x_473_) == 0)
{
lean_object* v_cs_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v_cs_475_ = lean_ctor_get(v_x_473_, 0);
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_array_get_size(v_cs_475_);
v___x_478_ = lean_nat_dec_lt(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
return v_x_474_;
}
else
{
uint8_t v___x_479_; 
v___x_479_ = lean_nat_dec_le(v___x_477_, v___x_477_);
if (v___x_479_ == 0)
{
if (v___x_478_ == 0)
{
return v_x_474_;
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_477_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_475_, v___x_480_, v___x_481_, v_x_474_);
return v___x_482_;
}
}
else
{
size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((size_t)0ULL);
v___x_484_ = lean_usize_of_nat(v___x_477_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_475_, v___x_483_, v___x_484_, v_x_474_);
return v___x_485_;
}
}
}
else
{
lean_object* v_vs_486_; lean_object* v___x_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_vs_486_ = lean_ctor_get(v_x_473_, 0);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = lean_array_get_size(v_vs_486_);
v___x_489_ = lean_nat_dec_lt(v___x_487_, v___x_488_);
if (v___x_489_ == 0)
{
return v_x_474_;
}
else
{
uint8_t v___x_490_; 
v___x_490_ = lean_nat_dec_le(v___x_488_, v___x_488_);
if (v___x_490_ == 0)
{
if (v___x_489_ == 0)
{
return v_x_474_;
}
else
{
size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
v___x_491_ = ((size_t)0ULL);
v___x_492_ = lean_usize_of_nat(v___x_488_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_486_, v___x_491_, v___x_492_, v_x_474_);
return v___x_493_;
}
}
else
{
size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_494_ = ((size_t)0ULL);
v___x_495_ = lean_usize_of_nat(v___x_488_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_486_, v___x_494_, v___x_495_, v_x_474_);
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(lean_object* v_as_497_, size_t v_i_498_, size_t v_stop_499_, lean_object* v_b_500_){
_start:
{
uint8_t v___x_501_; 
v___x_501_ = lean_usize_dec_eq(v_i_498_, v_stop_499_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; size_t v___x_504_; size_t v___x_505_; 
v___x_502_ = lean_array_uget_borrowed(v_as_497_, v_i_498_);
v___x_503_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v___x_502_, v_b_500_);
v___x_504_ = ((size_t)1ULL);
v___x_505_ = lean_usize_add(v_i_498_, v___x_504_);
v_i_498_ = v___x_505_;
v_b_500_ = v___x_503_;
goto _start;
}
else
{
return v_b_500_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1___boxed(lean_object* v_as_507_, lean_object* v_i_508_, lean_object* v_stop_509_, lean_object* v_b_510_){
_start:
{
size_t v_i_boxed_511_; size_t v_stop_boxed_512_; lean_object* v_res_513_; 
v_i_boxed_511_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_stop_boxed_512_ = lean_unbox_usize(v_stop_509_);
lean_dec(v_stop_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_as_507_, v_i_boxed_511_, v_stop_boxed_512_, v_b_510_);
lean_dec_ref(v_as_507_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2___boxed(lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_x_514_, v_x_515_);
lean_dec_ref(v_x_514_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(lean_object* v_x_517_, size_t v_x_518_, size_t v_x_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_517_) == 0)
{
lean_object* v_cs_521_; lean_object* v___x_522_; size_t v___x_523_; lean_object* v_j_524_; lean_object* v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v_cs_521_ = lean_ctor_get(v_x_517_, 0);
v___x_522_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_appendStickyDiagnostic_spec__0_spec__0___closed__0);
v___x_523_ = lean_usize_shift_right(v_x_518_, v_x_519_);
v_j_524_ = lean_usize_to_nat(v___x_523_);
v___x_525_ = lean_array_get_borrowed(v___x_522_, v_cs_521_, v_j_524_);
v___x_526_ = ((size_t)1ULL);
v___x_527_ = lean_usize_shift_left(v___x_526_, v_x_519_);
v___x_528_ = lean_usize_sub(v___x_527_, v___x_526_);
v___x_529_ = lean_usize_land(v_x_518_, v___x_528_);
v___x_530_ = ((size_t)5ULL);
v___x_531_ = lean_usize_sub(v_x_519_, v___x_530_);
v___x_532_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v___x_525_, v___x_529_, v___x_531_, v_x_520_);
v___x_533_ = lean_unsigned_to_nat(1u);
v___x_534_ = lean_nat_add(v_j_524_, v___x_533_);
lean_dec(v_j_524_);
v___x_535_ = lean_array_get_size(v_cs_521_);
v___x_536_ = lean_nat_dec_lt(v___x_534_, v___x_535_);
if (v___x_536_ == 0)
{
lean_dec(v___x_534_);
return v___x_532_;
}
else
{
uint8_t v___x_537_; 
v___x_537_ = lean_nat_dec_le(v___x_535_, v___x_535_);
if (v___x_537_ == 0)
{
if (v___x_536_ == 0)
{
lean_dec(v___x_534_);
return v___x_532_;
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_usize_of_nat(v___x_534_);
lean_dec(v___x_534_);
v___x_539_ = lean_usize_of_nat(v___x_535_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_521_, v___x_538_, v___x_539_, v___x_532_);
return v___x_540_;
}
}
else
{
size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_usize_of_nat(v___x_534_);
lean_dec(v___x_534_);
v___x_542_ = lean_usize_of_nat(v___x_535_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0_spec__1(v_cs_521_, v___x_541_, v___x_542_, v___x_532_);
return v___x_543_;
}
}
}
else
{
lean_object* v_vs_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v_vs_544_ = lean_ctor_get(v_x_517_, 0);
v___x_545_ = lean_usize_to_nat(v_x_518_);
v___x_546_ = lean_array_get_size(v_vs_544_);
v___x_547_ = lean_nat_dec_lt(v___x_545_, v___x_546_);
if (v___x_547_ == 0)
{
lean_dec(v___x_545_);
return v_x_520_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = lean_nat_dec_le(v___x_546_, v___x_546_);
if (v___x_548_ == 0)
{
if (v___x_547_ == 0)
{
lean_dec(v___x_545_);
return v_x_520_;
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_usize_of_nat(v___x_545_);
lean_dec(v___x_545_);
v___x_550_ = lean_usize_of_nat(v___x_546_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_544_, v___x_549_, v___x_550_, v_x_520_);
return v___x_551_;
}
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_usize_of_nat(v___x_545_);
lean_dec(v___x_545_);
v___x_553_ = lean_usize_of_nat(v___x_546_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_vs_544_, v___x_552_, v___x_553_, v_x_520_);
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0___boxed(lean_object* v_x_555_, lean_object* v_x_556_, lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
size_t v_x_3080__boxed_559_; size_t v_x_3081__boxed_560_; lean_object* v_res_561_; 
v_x_3080__boxed_559_ = lean_unbox_usize(v_x_556_);
lean_dec(v_x_556_);
v_x_3081__boxed_560_ = lean_unbox_usize(v_x_557_);
lean_dec(v_x_557_);
v_res_561_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_x_555_, v_x_3080__boxed_559_, v_x_3081__boxed_560_, v_x_558_);
lean_dec_ref(v_x_555_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(lean_object* v_t_562_, lean_object* v_init_563_, lean_object* v_start_564_){
_start:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_nat_dec_eq(v_start_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_object* v_root_567_; lean_object* v_tail_568_; size_t v_shift_569_; lean_object* v_tailOff_570_; uint8_t v___x_571_; 
v_root_567_ = lean_ctor_get(v_t_562_, 0);
v_tail_568_ = lean_ctor_get(v_t_562_, 1);
v_shift_569_ = lean_ctor_get_usize(v_t_562_, 4);
v_tailOff_570_ = lean_ctor_get(v_t_562_, 3);
v___x_571_ = lean_nat_dec_le(v_tailOff_570_, v_start_564_);
if (v___x_571_ == 0)
{
size_t v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_572_ = lean_usize_of_nat(v_start_564_);
v___x_573_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_567_, v___x_572_, v_shift_569_, v_init_563_);
v___x_574_ = lean_array_get_size(v_tail_568_);
v___x_575_ = lean_nat_dec_lt(v___x_565_, v___x_574_);
if (v___x_575_ == 0)
{
return v___x_573_;
}
else
{
uint8_t v___x_576_; 
v___x_576_ = lean_nat_dec_le(v___x_574_, v___x_574_);
if (v___x_576_ == 0)
{
if (v___x_575_ == 0)
{
return v___x_573_;
}
else
{
size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; 
v___x_577_ = ((size_t)0ULL);
v___x_578_ = lean_usize_of_nat(v___x_574_);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_568_, v___x_577_, v___x_578_, v___x_573_);
return v___x_579_;
}
}
else
{
size_t v___x_580_; size_t v___x_581_; lean_object* v___x_582_; 
v___x_580_ = ((size_t)0ULL);
v___x_581_ = lean_usize_of_nat(v___x_574_);
v___x_582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_568_, v___x_580_, v___x_581_, v___x_573_);
return v___x_582_;
}
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_583_ = lean_nat_sub(v_start_564_, v_tailOff_570_);
v___x_584_ = lean_array_get_size(v_tail_568_);
v___x_585_ = lean_nat_dec_lt(v___x_583_, v___x_584_);
if (v___x_585_ == 0)
{
lean_dec(v___x_583_);
return v_init_563_;
}
else
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_le(v___x_584_, v___x_584_);
if (v___x_586_ == 0)
{
if (v___x_585_ == 0)
{
lean_dec(v___x_583_);
return v_init_563_;
}
else
{
size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; 
v___x_587_ = lean_usize_of_nat(v___x_583_);
lean_dec(v___x_583_);
v___x_588_ = lean_usize_of_nat(v___x_584_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_568_, v___x_587_, v___x_588_, v_init_563_);
return v___x_589_;
}
}
else
{
size_t v___x_590_; size_t v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_usize_of_nat(v___x_583_);
lean_dec(v___x_583_);
v___x_591_ = lean_usize_of_nat(v___x_584_);
v___x_592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_568_, v___x_590_, v___x_591_, v_init_563_);
return v___x_592_;
}
}
}
}
else
{
lean_object* v_root_593_; lean_object* v_tail_594_; lean_object* v___x_595_; lean_object* v___x_596_; uint8_t v___x_597_; 
v_root_593_ = lean_ctor_get(v_t_562_, 0);
v_tail_594_ = lean_ctor_get(v_t_562_, 1);
v___x_595_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_593_, v_init_563_);
v___x_596_ = lean_array_get_size(v_tail_594_);
v___x_597_ = lean_nat_dec_lt(v___x_565_, v___x_596_);
if (v___x_597_ == 0)
{
return v___x_595_;
}
else
{
uint8_t v___x_598_; 
v___x_598_ = lean_nat_dec_le(v___x_596_, v___x_596_);
if (v___x_598_ == 0)
{
if (v___x_597_ == 0)
{
return v___x_595_;
}
else
{
size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; 
v___x_599_ = ((size_t)0ULL);
v___x_600_ = lean_usize_of_nat(v___x_596_);
v___x_601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_594_, v___x_599_, v___x_600_, v___x_595_);
return v___x_601_;
}
}
else
{
size_t v___x_602_; size_t v___x_603_; lean_object* v___x_604_; 
v___x_602_ = ((size_t)0ULL);
v___x_603_ = lean_usize_of_nat(v___x_596_);
v___x_604_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_594_, v___x_602_, v___x_603_, v___x_595_);
return v___x_604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1___boxed(lean_object* v_t_605_, lean_object* v_init_606_, lean_object* v_start_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_t_605_, v_init_606_, v_start_607_);
lean_dec(v_start_607_);
lean_dec_ref(v_t_605_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(lean_object* v_t_609_, lean_object* v_init_610_, lean_object* v_start_611_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_eq(v_start_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v_root_614_; lean_object* v_tail_615_; size_t v_shift_616_; lean_object* v_tailOff_617_; uint8_t v___x_618_; 
v_root_614_ = lean_ctor_get(v_t_609_, 0);
v_tail_615_ = lean_ctor_get(v_t_609_, 1);
v_shift_616_ = lean_ctor_get_usize(v_t_609_, 4);
v_tailOff_617_ = lean_ctor_get(v_t_609_, 3);
v___x_618_ = lean_nat_dec_le(v_tailOff_617_, v_start_611_);
if (v___x_618_ == 0)
{
size_t v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_619_ = lean_usize_of_nat(v_start_611_);
v___x_620_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__0(v_root_614_, v___x_619_, v_shift_616_, v_init_610_);
v___x_621_ = lean_array_get_size(v_tail_615_);
v___x_622_ = lean_nat_dec_lt(v___x_612_, v___x_621_);
if (v___x_622_ == 0)
{
return v___x_620_;
}
else
{
uint8_t v___x_623_; 
v___x_623_ = lean_nat_dec_le(v___x_621_, v___x_621_);
if (v___x_623_ == 0)
{
if (v___x_622_ == 0)
{
return v___x_620_;
}
else
{
size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
v___x_624_ = ((size_t)0ULL);
v___x_625_ = lean_usize_of_nat(v___x_621_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_615_, v___x_624_, v___x_625_, v___x_620_);
return v___x_626_;
}
}
else
{
size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; 
v___x_627_ = ((size_t)0ULL);
v___x_628_ = lean_usize_of_nat(v___x_621_);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_615_, v___x_627_, v___x_628_, v___x_620_);
return v___x_629_;
}
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_630_ = lean_nat_sub(v_start_611_, v_tailOff_617_);
v___x_631_ = lean_array_get_size(v_tail_615_);
v___x_632_ = lean_nat_dec_lt(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
lean_dec(v___x_630_);
return v_init_610_;
}
else
{
uint8_t v___x_633_; 
v___x_633_ = lean_nat_dec_le(v___x_631_, v___x_631_);
if (v___x_633_ == 0)
{
if (v___x_632_ == 0)
{
lean_dec(v___x_630_);
return v_init_610_;
}
else
{
size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_usize_of_nat(v___x_630_);
lean_dec(v___x_630_);
v___x_635_ = lean_usize_of_nat(v___x_631_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_615_, v___x_634_, v___x_635_, v_init_610_);
return v___x_636_;
}
}
else
{
size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___x_637_ = lean_usize_of_nat(v___x_630_);
lean_dec(v___x_630_);
v___x_638_ = lean_usize_of_nat(v___x_631_);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_615_, v___x_637_, v___x_638_, v_init_610_);
return v___x_639_;
}
}
}
}
else
{
lean_object* v_root_640_; lean_object* v_tail_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_root_640_ = lean_ctor_get(v_t_609_, 0);
v_tail_641_ = lean_ctor_get(v_t_609_, 1);
v___x_642_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__2(v_root_640_, v_init_610_);
v___x_643_ = lean_array_get_size(v_tail_641_);
v___x_644_ = lean_nat_dec_lt(v___x_612_, v___x_643_);
if (v___x_644_ == 0)
{
return v___x_642_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = lean_nat_dec_le(v___x_643_, v___x_643_);
if (v___x_645_ == 0)
{
if (v___x_644_ == 0)
{
return v___x_642_;
}
else
{
size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((size_t)0ULL);
v___x_647_ = lean_usize_of_nat(v___x_643_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_641_, v___x_646_, v___x_647_, v___x_642_);
return v___x_648_;
}
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
v___x_649_ = ((size_t)0ULL);
v___x_650_ = lean_usize_of_nat(v___x_643_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0_spec__1(v_tail_641_, v___x_649_, v___x_650_, v___x_642_);
return v___x_651_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0___boxed(lean_object* v_t_652_, lean_object* v_init_653_, lean_object* v_start_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_t_652_, v_init_653_, v_start_654_);
lean_dec(v_start_654_);
lean_dec_ref(v_t_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(lean_object* v_meta_658_, lean_object* v_writeDiagnostics_659_, uint8_t v_incrementalDiagnosticSupport_660_, lean_object* v___y_661_){
_start:
{
lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v_fst_669_; uint8_t v_snd_670_; lean_object* v___x_674_; uint8_t v___y_676_; 
v___x_674_ = lean_st_ref_get(v___y_661_);
if (v_incrementalDiagnosticSupport_660_ == 0)
{
v___y_676_ = v_incrementalDiagnosticSupport_660_;
goto v___jp_675_;
}
else
{
uint8_t v_isIncremental_697_; 
v_isIncremental_697_ = lean_ctor_get_uint8(v___x_674_, sizeof(void*)*3);
v___y_676_ = v_isIncremental_697_;
goto v___jp_675_;
}
v___jp_663_:
{
lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_666_ = l_Lean_Server_mkPublishDiagnosticsNotification(v_meta_658_, v___y_664_, v___y_665_);
v___x_667_ = lean_apply_2(v_writeDiagnostics_659_, v___x_666_, lean_box(0));
return v___x_667_;
}
v___jp_668_:
{
if (v_incrementalDiagnosticSupport_660_ == 0)
{
lean_object* v___x_671_; 
v___x_671_ = lean_box(0);
v___y_664_ = v_fst_669_;
v___y_665_ = v___x_671_;
goto v___jp_663_;
}
else
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_box(v_snd_670_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
v___y_664_ = v_fst_669_;
v___y_665_ = v___x_673_;
goto v___jp_663_;
}
}
v___jp_675_:
{
lean_object* v_stickyDiagsRef_677_; lean_object* v_diags_678_; lean_object* v_publishedDiagsAmount_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_696_; 
v_stickyDiagsRef_677_ = lean_ctor_get(v___x_674_, 0);
v_diags_678_ = lean_ctor_get(v___x_674_, 1);
v_publishedDiagsAmount_679_ = lean_ctor_get(v___x_674_, 2);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_674_);
if (v_isSharedCheck_696_ == 0)
{
v___x_681_ = v___x_674_;
v_isShared_682_ = v_isSharedCheck_696_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_publishedDiagsAmount_679_);
lean_inc(v_diags_678_);
lean_inc(v_stickyDiagsRef_677_);
lean_dec(v___x_674_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_696_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v_size_684_; uint8_t v___x_685_; lean_object* v___x_687_; 
v___x_683_ = lean_st_ref_get(v_stickyDiagsRef_677_);
v_size_684_ = lean_ctor_get(v_diags_678_, 2);
v___x_685_ = 1;
lean_inc(v_size_684_);
lean_inc_ref(v_diags_678_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 2, v_size_684_);
v___x_687_ = v___x_681_;
goto v_reusejp_686_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_stickyDiagsRef_677_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_diags_678_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_size_684_);
v___x_687_ = v_reuseFailAlloc_695_;
goto v_reusejp_686_;
}
v_reusejp_686_:
{
lean_object* v___x_688_; 
lean_ctor_set_uint8(v___x_687_, sizeof(void*)*3, v___x_685_);
v___x_688_ = lean_st_ref_swap(v___y_661_, v___x_687_);
lean_dec(v___x_688_);
if (v___y_676_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
lean_dec(v_publishedDiagsAmount_679_);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_691_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v___x_683_, v___x_690_, v___x_689_);
lean_dec(v___x_683_);
v___x_692_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__0(v_diags_678_, v___x_691_, v___x_689_);
lean_dec_ref(v_diags_678_);
v_fst_669_ = v___x_692_;
v_snd_670_ = v___y_676_;
goto v___jp_668_;
}
else
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_dec(v___x_683_);
v___x_693_ = ((lean_object*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___closed__0));
v___x_694_ = l_Lean_PersistentArray_foldlM___at___00Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics_spec__1(v_diags_678_, v___x_693_, v_publishedDiagsAmount_679_);
lean_dec(v_publishedDiagsAmount_679_);
lean_dec_ref(v_diags_678_);
v_fst_669_ = v___x_694_;
v_snd_670_ = v___x_685_;
goto v___jp_668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed(lean_object* v_meta_698_, lean_object* v_writeDiagnostics_699_, lean_object* v_incrementalDiagnosticSupport_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_703_; lean_object* v_res_704_; 
v_incrementalDiagnosticSupport_boxed_703_ = lean_unbox(v_incrementalDiagnosticSupport_700_);
v_res_704_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0(v_meta_698_, v_writeDiagnostics_699_, v_incrementalDiagnosticSupport_boxed_703_, v___y_701_);
lean_dec(v___y_701_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(lean_object* v_doc_705_, uint8_t v_incrementalDiagnosticSupport_706_, lean_object* v_writeDiagnostics_707_){
_start:
{
lean_object* v_meta_709_; lean_object* v_diagnosticsMutex_710_; lean_object* v___x_711_; lean_object* v___f_712_; lean_object* v___x_713_; 
v_meta_709_ = lean_ctor_get(v_doc_705_, 0);
lean_inc_ref(v_meta_709_);
v_diagnosticsMutex_710_ = lean_ctor_get(v_doc_705_, 3);
lean_inc_ref(v_diagnosticsMutex_710_);
lean_dec_ref(v_doc_705_);
v___x_711_ = lean_box(v_incrementalDiagnosticSupport_706_);
v___f_712_ = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___lam__0___boxed), 5, 3);
lean_closure_set(v___f_712_, 0, v_meta_709_);
lean_closure_set(v___f_712_, 1, v_writeDiagnostics_707_);
lean_closure_set(v___f_712_, 2, v___x_711_);
v___x_713_ = l_Std_Mutex_atomically___at___00Lean_Server_FileWorker_EditableDocumentCore_appendDiagnostics_spec__1___redArg(v_diagnosticsMutex_710_, v___f_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics___boxed(lean_object* v_doc_714_, lean_object* v_incrementalDiagnosticSupport_715_, lean_object* v_writeDiagnostics_716_, lean_object* v_a_717_){
_start:
{
uint8_t v_incrementalDiagnosticSupport_boxed_718_; lean_object* v_res_719_; 
v_incrementalDiagnosticSupport_boxed_718_ = lean_unbox(v_incrementalDiagnosticSupport_715_);
v_res_719_ = l_Lean_Server_FileWorker_EditableDocumentCore_publishDiagnostics(v_doc_714_, v_incrementalDiagnosticSupport_boxed_718_, v_writeDiagnostics_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_EditableDocument_versionedIdentifier(lean_object* v_ed_720_){
_start:
{
lean_object* v_toEditableDocumentCore_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_732_; 
v_toEditableDocumentCore_721_ = lean_ctor_get(v_ed_720_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_ed_720_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_ed_720_, 1);
lean_dec(v_unused_733_);
v___x_723_ = v_ed_720_;
v_isShared_724_ = v_isSharedCheck_732_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_toEditableDocumentCore_721_);
lean_dec(v_ed_720_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_732_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v_meta_725_; lean_object* v_uri_726_; lean_object* v_version_727_; lean_object* v___x_728_; lean_object* v___x_730_; 
v_meta_725_ = lean_ctor_get(v_toEditableDocumentCore_721_, 0);
lean_inc_ref(v_meta_725_);
lean_dec_ref(v_toEditableDocumentCore_721_);
v_uri_726_ = lean_ctor_get(v_meta_725_, 0);
lean_inc_ref(v_uri_726_);
v_version_727_ = lean_ctor_get(v_meta_725_, 2);
lean_inc(v_version_727_);
lean_dec_ref(v_meta_725_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_version_727_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_728_);
lean_ctor_set(v___x_723_, 0, v_uri_726_);
v___x_730_ = v___x_723_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_uri_726_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v___x_728_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_keepAliveTimeMs(void){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_unsigned_to_nat(30000u);
return v___x_734_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0(void){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_735_;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__0, &l_Lean_Server_FileWorker_RpcSession_new___closed__0_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__0);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new(uint8_t v_wireFormat_738_){
_start:
{
size_t v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((size_t)8ULL);
v___x_741_ = lean_io_get_random_bytes(v___x_740_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_759_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_759_ == 0)
{
v___x_744_ = v___x_741_;
v_isShared_745_ = v_isSharedCheck_759_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_a_742_);
lean_dec(v___x_741_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_759_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; uint64_t v___x_747_; lean_object* v___x_748_; size_t v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_746_ = lean_io_mono_ms_now();
v___x_747_ = l_ByteArray_toUInt64LE_x21(v_a_742_);
lean_dec(v_a_742_);
v___x_748_ = lean_obj_once(&l_Lean_Server_FileWorker_RpcSession_new___closed__1, &l_Lean_Server_FileWorker_RpcSession_new___closed__1_once, _init_l_Lean_Server_FileWorker_RpcSession_new___closed__1);
v___x_749_ = ((size_t)0ULL);
v___x_750_ = lean_alloc_ctor(0, 2, sizeof(size_t)*1 + 1);
lean_ctor_set(v___x_750_, 0, v___x_748_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
lean_ctor_set_usize(v___x_750_, 2, v___x_749_);
lean_ctor_set_uint8(v___x_750_, sizeof(void*)*3, v_wireFormat_738_);
v___x_751_ = lean_unsigned_to_nat(30000u);
v___x_752_ = lean_nat_add(v___x_746_, v___x_751_);
lean_dec(v___x_746_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_750_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = lean_box_uint64(v___x_747_);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_754_);
lean_ctor_set(v___x_755_, 1, v___x_753_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 0, v___x_755_);
v___x_757_ = v___x_744_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
v_a_760_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_741_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_741_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_new___boxed(lean_object* v_wireFormat_768_, lean_object* v_a_769_){
_start:
{
uint8_t v_wireFormat_boxed_770_; lean_object* v_res_771_; 
v_wireFormat_boxed_770_ = lean_unbox(v_wireFormat_768_);
v_res_771_ = l_Lean_Server_FileWorker_RpcSession_new(v_wireFormat_boxed_770_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive(lean_object* v_monoMsNow_772_, lean_object* v_s_773_){
_start:
{
lean_object* v_objects_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_783_; 
v_objects_774_ = lean_ctor_get(v_s_773_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v_s_773_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_s_773_, 1);
lean_dec(v_unused_784_);
v___x_776_ = v_s_773_;
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_objects_774_);
lean_dec(v_s_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_783_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_781_; 
v___x_778_ = lean_unsigned_to_nat(30000u);
v___x_779_ = lean_nat_add(v_monoMsNow_772_, v___x_778_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v___x_779_);
v___x_781_ = v___x_776_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_objects_774_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v___x_779_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_keptAlive___boxed(lean_object* v_monoMsNow_785_, lean_object* v_s_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Server_FileWorker_RpcSession_keptAlive(v_monoMsNow_785_, v_s_786_);
lean_dec(v_monoMsNow_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired(lean_object* v_s_788_){
_start:
{
lean_object* v___x_790_; lean_object* v_expireTime_791_; uint8_t v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_790_ = lean_io_mono_ms_now();
v_expireTime_791_ = lean_ctor_get(v_s_788_, 1);
v___x_792_ = lean_nat_dec_le(v_expireTime_791_, v___x_790_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(v___x_792_);
v___x_794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_794_, 0, v___x_793_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_RpcSession_hasExpired___boxed(lean_object* v_s_795_, lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_Lean_Server_FileWorker_RpcSession_hasExpired(v_s_795_);
lean_dec_ref(v_s_795_);
return v_res_797_;
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
