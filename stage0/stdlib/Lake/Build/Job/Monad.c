// Lean compiler output
// Module: Lake.Build.Job.Monad
// Imports: public import Lake.Build.Fetch
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lake_BuildTrace_nil(lean_object*);
lean_object* lean_task_pure(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
extern lean_object* l_Lake_instDataKindUnit;
lean_object* l_Lake_JobState_merge(lean_object*, lean_object*);
lean_object* lean_task_map(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_task_bind(lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_IO_FS_Stream_ofBuffer(lean_object*);
lean_object* lean_get_set_stdout(lean_object*);
lean_object* lean_get_set_stderr(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_Slice_trimAscii(lean_object*);
lean_object* l_String_Slice_toString(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_string_validate_utf8(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
uint8_t l_IO_CancelToken_isSet(lean_object*);
extern lean_object* l_Lake_cancelMessage;
lean_object* lean_io_bind_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_pushLogEntry(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EquipT_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lake_JobAction_merge(uint8_t, uint8_t);
lean_object* lean_io_as_task(lean_object*, lean_object*);
lean_object* l_instMonadBaseIO___aux__5___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonadStateOfOfPure___redArg(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_io_wait(lean_object*);
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadStateOfOfMonadLift___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_instMonadBaseIO;
lean_object* l_Lake_EStateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_EStateT_instFunctor___redArg(lean_object*);
lean_object* l_Lake_EStateT_instPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lake_EquipT_instMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_toFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_toFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_toFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_toFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadStateOfJobStateJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadBaseIO___aux__5___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__0 = (const lean_object*)&l_Lake_instMonadStateOfJobStateJobM___closed__0_value;
static lean_once_cell_t l_Lake_instMonadStateOfJobStateJobM___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__1;
static const lean_closure_object l_Lake_instMonadStateOfJobStateJobM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_EquipT_lift___boxed, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__2 = (const lean_object*)&l_Lake_instMonadStateOfJobStateJobM___closed__2_value;
static const lean_closure_object l_Lake_instMonadStateOfJobStateJobM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__3 = (const lean_object*)&l_Lake_instMonadStateOfJobStateJobM___closed__3_value;
static const lean_closure_object l_Lake_instMonadStateOfJobStateJobM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__4 = (const lean_object*)&l_Lake_instMonadStateOfJobStateJobM___closed__4_value;
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfJobStateJobM;
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadStateOfLogJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadStateOfLogJobM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadStateOfLogJobM___closed__0 = (const lean_object*)&l_Lake_instMonadStateOfLogJobM___closed__0_value;
static const lean_closure_object l_Lake_instMonadStateOfLogJobM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadStateOfLogJobM___lam__1___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadStateOfLogJobM___closed__1 = (const lean_object*)&l_Lake_instMonadStateOfLogJobM___closed__1_value;
static const lean_closure_object l_Lake_instMonadStateOfLogJobM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadStateOfLogJobM___lam__2___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadStateOfLogJobM___closed__2 = (const lean_object*)&l_Lake_instMonadStateOfLogJobM___closed__2_value;
static const lean_ctor_object l_Lake_instMonadStateOfLogJobM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lake_instMonadStateOfLogJobM___closed__0_value),((lean_object*)&l_Lake_instMonadStateOfLogJobM___closed__1_value),((lean_object*)&l_Lake_instMonadStateOfLogJobM___closed__2_value)}};
static const lean_object* l_Lake_instMonadStateOfLogJobM___closed__3 = (const lean_object*)&l_Lake_instMonadStateOfLogJobM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadStateOfLogJobM = (const lean_object*)&l_Lake_instMonadStateOfLogJobM___closed__3_value;
static const lean_closure_object l_Lake_instMonadLogJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_pushLogEntry, .m_arity = 3, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lake_instMonadStateOfLogJobM___closed__3_value)} };
static const lean_object* l_Lake_instMonadLogJobM___closed__0 = (const lean_object*)&l_Lake_instMonadLogJobM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadLogJobM = (const lean_object*)&l_Lake_instMonadLogJobM___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadErrorJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadErrorJobM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadErrorJobM___closed__0 = (const lean_object*)&l_Lake_instMonadErrorJobM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadErrorJobM = (const lean_object*)&l_Lake_instMonadErrorJobM___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instAlternativeJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instAlternativeJobM___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instAlternativeJobM___closed__0 = (const lean_object*)&l_Lake_instAlternativeJobM___closed__0_value;
static const lean_closure_object l_Lake_instAlternativeJobM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instAlternativeJobM___lam__1___boxed, .m_arity = 10, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instAlternativeJobM___closed__1 = (const lean_object*)&l_Lake_instAlternativeJobM___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM;
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadLiftLogIOJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_instMonadLiftLogIOJobM___lam__0___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadLiftLogIOJobM___closed__0 = (const lean_object*)&l_Lake_instMonadLiftLogIOJobM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadLiftLogIOJobM = (const lean_object*)&l_Lake_instMonadLiftLogIOJobM___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateAction(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_updateAction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_newTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_newTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_modifyTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_modifyTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTraceCaption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_takeTrace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "<nil>"};
static const lean_object* l_Lake_takeTrace___redArg___closed__0 = (const lean_object*)&l_Lake_takeTrace___redArg___closed__0_value;
static lean_once_cell_t l_Lake_takeTrace___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_takeTrace___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_swapTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_swapTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addSubTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_addSubTrace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadLiftSpawnMJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_JobM_runSpawnM___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadLiftSpawnMJobM___closed__0 = (const lean_object*)&l_Lake_instMonadLiftSpawnMJobM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadLiftSpawnMJobM = (const lean_object*)&l_Lake_instMonadLiftSpawnMJobM___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadLiftJobMFetchM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_FetchM_runJobM___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadLiftJobMFetchM___closed__0 = (const lean_object*)&l_Lake_instMonadLiftJobMFetchM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadLiftJobMFetchM = (const lean_object*)&l_Lake_instMonadLiftJobMFetchM___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_instMonadLiftFetchMJobM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_JobM_runFetchM___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadLiftFetchMJobM___closed__0 = (const lean_object*)&l_Lake_instMonadLiftFetchMJobM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lake_instMonadLiftFetchMJobM = (const lean_object*)&l_Lake_instMonadLiftFetchMJobM___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindTask(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_panic___at___00Lake_Job_sync_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_panic___at___00Lake_Job_sync_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lake_Job_sync_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lake_Job_sync_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Job_sync___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Job_sync___redArg___closed__0;
static const lean_array_object l_Lake_Job_sync___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lake_Job_sync___redArg___closed__1 = (const lean_object*)&l_Lake_Job_sync___redArg___closed__1_value;
static lean_once_cell_t l_Lake_Job_sync___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Job_sync___redArg___closed__2;
static const lean_string_object l_Lake_Job_sync___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "stdout/stderr:\n"};
static const lean_object* l_Lake_Job_sync___redArg___closed__3 = (const lean_object*)&l_Lake_Job_sync___redArg___closed__3_value;
static const lean_string_object l_Lake_Job_sync___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Basic"};
static const lean_object* l_Lake_Job_sync___redArg___closed__4 = (const lean_object*)&l_Lake_Job_sync___redArg___closed__4_value;
static const lean_string_object l_Lake_Job_sync___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "String.fromUTF8!"};
static const lean_object* l_Lake_Job_sync___redArg___closed__5 = (const lean_object*)&l_Lake_Job_sync___redArg___closed__5_value;
static const lean_string_object l_Lake_Job_sync___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid UTF-8 string"};
static const lean_object* l_Lake_Job_sync___redArg___closed__6 = (const lean_object*)&l_Lake_Job_sync___redArg___closed__6_value;
static lean_once_cell_t l_Lake_Job_sync___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Job_sync___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_sync(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_sync___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_async___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_await(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_await___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_collectVector(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___redArg(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
_start:
{
lean_object* v___x_9_; 
lean_inc_ref(v_a_6_);
lean_inc(v_a_5_);
lean_inc(v_a_4_);
lean_inc(v_a_3_);
v___x_9_ = lean_apply_7(v_f_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_, lean_box(0));
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___redArg___boxed(lean_object* v_f_10_, lean_object* v_a_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lake_JobM_ofFn___redArg(v_f_10_, v_a_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_);
lean_dec_ref(v_a_15_);
lean_dec(v_a_14_);
lean_dec(v_a_13_);
lean_dec(v_a_12_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn(lean_object* v_00_u03b1_19_, lean_object* v_f_20_, lean_object* v_a_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_){
_start:
{
lean_object* v___x_28_; 
lean_inc_ref(v_a_25_);
lean_inc(v_a_24_);
lean_inc(v_a_23_);
lean_inc(v_a_22_);
v___x_28_ = lean_apply_7(v_f_20_, v_a_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, lean_box(0));
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___boxed(lean_object* v_00_u03b1_29_, lean_object* v_f_30_, lean_object* v_a_31_, lean_object* v_a_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lake_JobM_ofFn(v_00_u03b1_29_, v_f_30_, v_a_31_, v_a_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_);
lean_dec_ref(v_a_35_);
lean_dec(v_a_34_);
lean_dec(v_a_33_);
lean_dec(v_a_32_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_toFn___redArg(lean_object* v_self_39_, lean_object* v_fetch_40_, lean_object* v_pkg_x3f_41_, lean_object* v_stack_42_, lean_object* v_store_43_, lean_object* v_ctx_44_, lean_object* v_s_45_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lean_apply_7(v_self_39_, v_fetch_40_, v_pkg_x3f_41_, v_stack_42_, v_store_43_, v_ctx_44_, v_s_45_, lean_box(0));
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_toFn___redArg___boxed(lean_object* v_self_48_, lean_object* v_fetch_49_, lean_object* v_pkg_x3f_50_, lean_object* v_stack_51_, lean_object* v_store_52_, lean_object* v_ctx_53_, lean_object* v_s_54_, lean_object* v_a_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lake_JobM_toFn___redArg(v_self_48_, v_fetch_49_, v_pkg_x3f_50_, v_stack_51_, v_store_52_, v_ctx_53_, v_s_54_);
return v_res_56_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_toFn(lean_object* v_00_u03b1_57_, lean_object* v_self_58_, lean_object* v_fetch_59_, lean_object* v_pkg_x3f_60_, lean_object* v_stack_61_, lean_object* v_store_62_, lean_object* v_ctx_63_, lean_object* v_s_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_apply_7(v_self_58_, v_fetch_59_, v_pkg_x3f_60_, v_stack_61_, v_store_62_, v_ctx_63_, v_s_64_, lean_box(0));
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_toFn___boxed(lean_object* v_00_u03b1_67_, lean_object* v_self_68_, lean_object* v_fetch_69_, lean_object* v_pkg_x3f_70_, lean_object* v_stack_71_, lean_object* v_store_72_, lean_object* v_ctx_73_, lean_object* v_s_74_, lean_object* v_a_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lake_JobM_toFn(v_00_u03b1_67_, v_self_68_, v_fetch_69_, v_pkg_x3f_70_, v_stack_71_, v_store_72_, v_ctx_73_, v_s_74_);
return v_res_76_;
}
}
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM___closed__1(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__0));
v___x_79_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM(void){
_start:
{
lean_object* v___x_83_; lean_object* v_get_84_; lean_object* v_set_85_; lean_object* v_modifyGet_86_; lean_object* v___x_87_; lean_object* v___f_88_; lean_object* v___x_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___f_96_; lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_83_ = lean_obj_once(&l_Lake_instMonadStateOfJobStateJobM___closed__1, &l_Lake_instMonadStateOfJobStateJobM___closed__1_once, _init_l_Lake_instMonadStateOfJobStateJobM___closed__1);
v_get_84_ = lean_ctor_get(v___x_83_, 0);
v_set_85_ = lean_ctor_get(v___x_83_, 1);
v_modifyGet_86_ = lean_ctor_get(v___x_83_, 2);
v___x_87_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__2));
v___f_88_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__3));
v___x_89_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__4));
lean_inc(v_set_85_);
v___f_90_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_90_, 0, v_set_85_);
lean_closure_set(v___f_90_, 1, v___f_88_);
lean_inc(v_modifyGet_86_);
v___f_91_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_91_, 0, v_modifyGet_86_);
lean_closure_set(v___f_91_, 1, v___f_88_);
lean_inc(v_get_84_);
v___x_92_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_92_, 0, lean_box(0));
lean_closure_set(v___x_92_, 1, v_get_84_);
v___f_93_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_93_, 0, v___f_90_);
lean_closure_set(v___f_93_, 1, v___x_89_);
v___f_94_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_94_, 0, v___f_91_);
lean_closure_set(v___f_94_, 1, v___x_89_);
v___x_95_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_95_, 0, lean_box(0));
lean_closure_set(v___x_95_, 1, lean_box(0));
lean_closure_set(v___x_95_, 2, lean_box(0));
lean_closure_set(v___x_95_, 3, lean_box(0));
lean_closure_set(v___x_95_, 4, v___x_92_);
v___f_96_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_96_, 0, v___f_93_);
lean_closure_set(v___f_96_, 1, v___f_88_);
v___f_97_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_97_, 0, v___f_94_);
lean_closure_set(v___f_97_, 1, v___f_88_);
v___x_98_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_98_, 0, lean_box(0));
lean_closure_set(v___x_98_, 1, v___x_95_);
v___f_99_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_99_, 0, v___f_96_);
lean_closure_set(v___f_99_, 1, v___f_88_);
v___f_100_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_100_, 0, v___f_97_);
lean_closure_set(v___f_100_, 1, v___f_88_);
v___x_101_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_101_, 0, lean_box(0));
lean_closure_set(v___x_101_, 1, v___x_98_);
v___f_102_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_102_, 0, v___f_99_);
lean_closure_set(v___f_102_, 1, v___x_87_);
v___f_103_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_103_, 0, v___f_100_);
lean_closure_set(v___f_103_, 1, v___x_87_);
v___x_104_ = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(v___x_104_, 0, lean_box(0));
lean_closure_set(v___x_104_, 1, lean_box(0));
lean_closure_set(v___x_104_, 2, lean_box(0));
lean_closure_set(v___x_104_, 3, v___x_101_);
v___x_105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v___f_102_);
lean_ctor_set(v___x_105_, 2, v___f_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0(lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_){
_start:
{
lean_object* v_log_113_; lean_object* v___x_114_; 
v_log_113_ = lean_ctor_get(v___y_111_, 0);
lean_inc_ref(v_log_113_);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v_log_113_);
lean_ctor_set(v___x_114_, 1, v___y_111_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0___boxed(lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lake_instMonadStateOfLogJobM___lam__0(v___y_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1(lean_object* v_log_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
uint8_t v_action_131_; uint8_t v_wantsRebuild_132_; lean_object* v_trace_133_; lean_object* v_buildTime_134_; lean_object* v___x_136_; uint8_t v_isShared_137_; uint8_t v_isSharedCheck_143_; 
v_action_131_ = lean_ctor_get_uint8(v___y_129_, sizeof(void*)*3);
v_wantsRebuild_132_ = lean_ctor_get_uint8(v___y_129_, sizeof(void*)*3 + 1);
v_trace_133_ = lean_ctor_get(v___y_129_, 1);
v_buildTime_134_ = lean_ctor_get(v___y_129_, 2);
v_isSharedCheck_143_ = !lean_is_exclusive(v___y_129_);
if (v_isSharedCheck_143_ == 0)
{
lean_object* v_unused_144_; 
v_unused_144_ = lean_ctor_get(v___y_129_, 0);
lean_dec(v_unused_144_);
v___x_136_ = v___y_129_;
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
else
{
lean_inc(v_buildTime_134_);
lean_inc(v_trace_133_);
lean_dec(v___y_129_);
v___x_136_ = lean_box(0);
v_isShared_137_ = v_isSharedCheck_143_;
goto v_resetjp_135_;
}
v_resetjp_135_:
{
lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_138_ = lean_box(0);
if (v_isShared_137_ == 0)
{
lean_ctor_set(v___x_136_, 0, v_log_123_);
v___x_140_ = v___x_136_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_log_123_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_trace_133_);
lean_ctor_set(v_reuseFailAlloc_142_, 2, v_buildTime_134_);
lean_ctor_set_uint8(v_reuseFailAlloc_142_, sizeof(void*)*3, v_action_131_);
lean_ctor_set_uint8(v_reuseFailAlloc_142_, sizeof(void*)*3 + 1, v_wantsRebuild_132_);
v___x_140_ = v_reuseFailAlloc_142_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
lean_object* v___x_141_; 
v___x_141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_138_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
return v___x_141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1___boxed(lean_object* v_log_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lake_instMonadStateOfLogJobM___lam__1(v_log_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec(v___y_148_);
lean_dec(v___y_147_);
lean_dec_ref(v___y_146_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2(lean_object* v_00_u03b1_154_, lean_object* v_f_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_){
_start:
{
lean_object* v_log_163_; uint8_t v_action_164_; uint8_t v_wantsRebuild_165_; lean_object* v_trace_166_; lean_object* v_buildTime_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_184_; 
v_log_163_ = lean_ctor_get(v___y_161_, 0);
v_action_164_ = lean_ctor_get_uint8(v___y_161_, sizeof(void*)*3);
v_wantsRebuild_165_ = lean_ctor_get_uint8(v___y_161_, sizeof(void*)*3 + 1);
v_trace_166_ = lean_ctor_get(v___y_161_, 1);
v_buildTime_167_ = lean_ctor_get(v___y_161_, 2);
v_isSharedCheck_184_ = !lean_is_exclusive(v___y_161_);
if (v_isSharedCheck_184_ == 0)
{
v___x_169_ = v___y_161_;
v_isShared_170_ = v_isSharedCheck_184_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_buildTime_167_);
lean_inc(v_trace_166_);
lean_inc(v_log_163_);
lean_dec(v___y_161_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_184_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_183_; 
v___x_171_ = lean_apply_1(v_f_155_, v_log_163_);
v_fst_172_ = lean_ctor_get(v___x_171_, 0);
v_snd_173_ = lean_ctor_get(v___x_171_, 1);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_183_ == 0)
{
v___x_175_ = v___x_171_;
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_snd_173_);
lean_inc(v_fst_172_);
lean_dec(v___x_171_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_183_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 0, v_snd_173_);
v___x_178_ = v___x_169_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_snd_173_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_trace_166_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_buildTime_167_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*3, v_action_164_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*3 + 1, v_wantsRebuild_165_);
v___x_178_ = v_reuseFailAlloc_182_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
lean_object* v___x_180_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 1, v___x_178_);
v___x_180_ = v___x_175_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_fst_172_);
lean_ctor_set(v_reuseFailAlloc_181_, 1, v___x_178_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2___boxed(lean_object* v_00_u03b1_185_, lean_object* v_f_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_res_194_; 
v_res_194_ = l_Lake_instMonadStateOfLogJobM___lam__2(v_00_u03b1_185_, v_f_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_);
lean_dec_ref(v___y_191_);
lean_dec(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0(lean_object* v_00_u03b1_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_log_215_; uint8_t v_action_216_; uint8_t v_wantsRebuild_217_; lean_object* v_trace_218_; lean_object* v_buildTime_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_231_; 
v_log_215_ = lean_ctor_get(v___y_213_, 0);
v_action_216_ = lean_ctor_get_uint8(v___y_213_, sizeof(void*)*3);
v_wantsRebuild_217_ = lean_ctor_get_uint8(v___y_213_, sizeof(void*)*3 + 1);
v_trace_218_ = lean_ctor_get(v___y_213_, 1);
v_buildTime_219_ = lean_ctor_get(v___y_213_, 2);
v_isSharedCheck_231_ = !lean_is_exclusive(v___y_213_);
if (v_isSharedCheck_231_ == 0)
{
v___x_221_ = v___y_213_;
v_isShared_222_ = v_isSharedCheck_231_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_buildTime_219_);
lean_inc(v_trace_218_);
lean_inc(v_log_215_);
lean_dec(v___y_213_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_231_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
uint8_t v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_223_ = 3;
v___x_224_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_224_, 0, v___y_207_);
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_223_);
v___x_225_ = lean_array_get_size(v_log_215_);
v___x_226_ = lean_array_push(v_log_215_, v___x_224_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_226_);
v___x_228_ = v___x_221_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v_trace_218_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_buildTime_219_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*3, v_action_216_);
lean_ctor_set_uint8(v_reuseFailAlloc_230_, sizeof(void*)*3 + 1, v_wantsRebuild_217_);
v___x_228_ = v_reuseFailAlloc_230_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
lean_object* v___x_229_; 
v___x_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_225_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0___boxed(lean_object* v_00_u03b1_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lake_instMonadErrorJobM___lam__0(v_00_u03b1_232_, v___y_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec(v___y_236_);
lean_dec(v___y_235_);
lean_dec_ref(v___y_234_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0(lean_object* v_00_u03b1_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
lean_object* v_log_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v_log_252_ = lean_ctor_get(v___y_250_, 0);
v___x_253_ = lean_array_get_size(v_log_252_);
v___x_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_253_);
lean_ctor_set(v___x_254_, 1, v___y_250_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0___boxed(lean_object* v_00_u03b1_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = l_Lake_instAlternativeJobM___lam__0(v_00_u03b1_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1(lean_object* v_00_u03b1_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v___x_274_; 
lean_inc_ref(v___y_271_);
lean_inc(v___y_270_);
lean_inc(v___y_269_);
lean_inc(v___y_268_);
lean_inc_ref(v___y_267_);
v___x_274_ = lean_apply_7(v___y_265_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, lean_box(0));
if (lean_obj_tag(v___x_274_) == 0)
{
lean_dec_ref(v___y_267_);
lean_dec_ref(v___y_266_);
return v___x_274_;
}
else
{
lean_object* v_a_275_; lean_object* v_a_276_; lean_object* v_log_277_; uint8_t v_action_278_; uint8_t v_wantsRebuild_279_; lean_object* v_trace_280_; lean_object* v_buildTime_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_291_; 
v_a_275_ = lean_ctor_get(v___x_274_, 1);
lean_inc(v_a_275_);
v_a_276_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_a_276_);
lean_dec_ref_known(v___x_274_, 2);
v_log_277_ = lean_ctor_get(v_a_275_, 0);
v_action_278_ = lean_ctor_get_uint8(v_a_275_, sizeof(void*)*3);
v_wantsRebuild_279_ = lean_ctor_get_uint8(v_a_275_, sizeof(void*)*3 + 1);
v_trace_280_ = lean_ctor_get(v_a_275_, 1);
v_buildTime_281_ = lean_ctor_get(v_a_275_, 2);
v_isSharedCheck_291_ = !lean_is_exclusive(v_a_275_);
if (v_isSharedCheck_291_ == 0)
{
v___x_283_ = v_a_275_;
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_buildTime_281_);
lean_inc(v_trace_280_);
lean_inc(v_log_277_);
lean_dec(v_a_275_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_291_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_287_; 
v___x_285_ = l_Array_shrink___redArg(v_log_277_, v_a_276_);
lean_dec(v_a_276_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_285_);
v___x_287_ = v___x_283_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_285_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_trace_280_);
lean_ctor_set(v_reuseFailAlloc_290_, 2, v_buildTime_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_290_, sizeof(void*)*3, v_action_278_);
lean_ctor_set_uint8(v_reuseFailAlloc_290_, sizeof(void*)*3 + 1, v_wantsRebuild_279_);
v___x_287_ = v_reuseFailAlloc_290_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_box(0);
lean_inc_ref(v___y_271_);
lean_inc(v___y_270_);
lean_inc(v___y_269_);
lean_inc(v___y_268_);
v___x_289_ = lean_apply_8(v___y_266_, v___x_288_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___x_287_, lean_box(0));
return v___x_289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1___boxed(lean_object* v_00_u03b1_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lake_instAlternativeJobM___lam__1(v_00_u03b1_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec(v___y_297_);
lean_dec(v___y_296_);
return v_res_302_;
}
}
static lean_object* _init_l_Lake_instAlternativeJobM(void){
_start:
{
lean_object* v___x_305_; lean_object* v_toApplicative_306_; lean_object* v_toBind_307_; lean_object* v_toFunctor_308_; lean_object* v_toPure_309_; lean_object* v___f_310_; lean_object* v___f_311_; lean_object* v___f_312_; lean_object* v___f_313_; lean_object* v___x_314_; lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_toApplicative_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___x_326_; 
v___x_305_ = l_instMonadBaseIO;
v_toApplicative_306_ = lean_ctor_get(v___x_305_, 0);
v_toBind_307_ = lean_ctor_get(v___x_305_, 1);
v_toFunctor_308_ = lean_ctor_get(v_toApplicative_306_, 0);
v_toPure_309_ = lean_ctor_get(v_toApplicative_306_, 1);
lean_inc_n(v_toBind_307_, 3);
lean_inc_n(v_toPure_309_, 5);
v___f_310_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_310_, 0, v_toPure_309_);
lean_closure_set(v___f_310_, 1, v_toBind_307_);
v___f_311_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_311_, 0, v_toPure_309_);
lean_closure_set(v___f_311_, 1, v_toBind_307_);
lean_inc_ref(v___f_310_);
v___f_312_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_312_, 0, v_toPure_309_);
lean_closure_set(v___f_312_, 1, v___f_310_);
lean_inc_ref_n(v_toFunctor_308_, 2);
v___f_313_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_313_, 0, v_toFunctor_308_);
lean_closure_set(v___f_313_, 1, v_toPure_309_);
lean_closure_set(v___f_313_, 2, v_toBind_307_);
v___x_314_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_308_);
v___f_315_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_315_, 0, v_toPure_309_);
v___x_316_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___f_315_);
lean_ctor_set(v___x_316_, 2, v___f_313_);
lean_ctor_set(v___x_316_, 3, v___f_312_);
lean_ctor_set(v___x_316_, 4, v___f_311_);
v___x_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v___f_310_);
v___x_318_ = l_ReaderT_instMonad___redArg(v___x_317_);
v___x_319_ = l_StateRefT_x27_instMonad___redArg(v___x_318_);
v___x_320_ = l_ReaderT_instMonad___redArg(v___x_319_);
v___x_321_ = l_ReaderT_instMonad___redArg(v___x_320_);
v___x_322_ = l_Lake_EquipT_instMonad___redArg(v___x_321_);
v_toApplicative_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc_ref(v_toApplicative_323_);
lean_dec_ref(v___x_322_);
v___f_324_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__0));
v___f_325_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__1));
v___x_326_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_326_, 0, v_toApplicative_323_);
lean_ctor_set(v___x_326_, 1, v___f_324_);
lean_ctor_set(v___x_326_, 2, v___f_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0(lean_object* v_00_u03b1_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_){
_start:
{
lean_object* v_log_336_; uint8_t v_action_337_; uint8_t v_wantsRebuild_338_; lean_object* v_trace_339_; lean_object* v_buildTime_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_369_; 
v_log_336_ = lean_ctor_get(v___y_334_, 0);
v_action_337_ = lean_ctor_get_uint8(v___y_334_, sizeof(void*)*3);
v_wantsRebuild_338_ = lean_ctor_get_uint8(v___y_334_, sizeof(void*)*3 + 1);
v_trace_339_ = lean_ctor_get(v___y_334_, 1);
v_buildTime_340_ = lean_ctor_get(v___y_334_, 2);
v_isSharedCheck_369_ = !lean_is_exclusive(v___y_334_);
if (v_isSharedCheck_369_ == 0)
{
v___x_342_ = v___y_334_;
v_isShared_343_ = v_isSharedCheck_369_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_buildTime_340_);
lean_inc(v_trace_339_);
lean_inc(v_log_336_);
lean_dec(v___y_334_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_369_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_344_; 
v___x_344_ = lean_apply_2(v___y_328_, v_log_336_, lean_box(0));
if (lean_obj_tag(v___x_344_) == 0)
{
lean_object* v_a_345_; lean_object* v_a_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_356_; 
v_a_345_ = lean_ctor_get(v___x_344_, 0);
v_a_346_ = lean_ctor_get(v___x_344_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_356_ == 0)
{
v___x_348_ = v___x_344_;
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_a_346_);
lean_inc(v_a_345_);
lean_dec(v___x_344_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_356_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_351_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v_a_346_);
v___x_351_ = v___x_342_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_346_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v_trace_339_);
lean_ctor_set(v_reuseFailAlloc_355_, 2, v_buildTime_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*3, v_action_337_);
lean_ctor_set_uint8(v_reuseFailAlloc_355_, sizeof(void*)*3 + 1, v_wantsRebuild_338_);
v___x_351_ = v_reuseFailAlloc_355_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
lean_object* v___x_353_; 
if (v_isShared_349_ == 0)
{
lean_ctor_set(v___x_348_, 1, v___x_351_);
v___x_353_ = v___x_348_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_345_);
lean_ctor_set(v_reuseFailAlloc_354_, 1, v___x_351_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
else
{
lean_object* v_a_357_; lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_368_; 
v_a_357_ = lean_ctor_get(v___x_344_, 0);
v_a_358_ = lean_ctor_get(v___x_344_, 1);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_344_);
if (v_isSharedCheck_368_ == 0)
{
v___x_360_ = v___x_344_;
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_inc(v_a_357_);
lean_dec(v___x_344_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_368_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v_a_358_);
v___x_363_ = v___x_342_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_358_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_trace_339_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_buildTime_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_367_, sizeof(void*)*3, v_action_337_);
lean_ctor_set_uint8(v_reuseFailAlloc_367_, sizeof(void*)*3 + 1, v_wantsRebuild_338_);
v___x_363_ = v_reuseFailAlloc_367_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_365_; 
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v___x_363_);
v___x_365_ = v___x_360_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_a_357_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_363_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(lean_object* v_00_u03b1_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lake_instMonadLiftLogIOJobM___lam__0(v_00_u03b1_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg(uint8_t v_action_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_log_385_; uint8_t v_action_386_; uint8_t v_wantsRebuild_387_; lean_object* v_trace_388_; lean_object* v_buildTime_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_399_; 
v_log_385_ = lean_ctor_get(v_a_383_, 0);
v_action_386_ = lean_ctor_get_uint8(v_a_383_, sizeof(void*)*3);
v_wantsRebuild_387_ = lean_ctor_get_uint8(v_a_383_, sizeof(void*)*3 + 1);
v_trace_388_ = lean_ctor_get(v_a_383_, 1);
v_buildTime_389_ = lean_ctor_get(v_a_383_, 2);
v_isSharedCheck_399_ = !lean_is_exclusive(v_a_383_);
if (v_isSharedCheck_399_ == 0)
{
v___x_391_ = v_a_383_;
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_buildTime_389_);
lean_inc(v_trace_388_);
lean_inc(v_log_385_);
lean_dec(v_a_383_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_399_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_393_; uint8_t v___x_394_; lean_object* v___x_396_; 
v___x_393_ = lean_box(0);
v___x_394_ = l_Lake_JobAction_merge(v_action_386_, v_action_382_);
if (v_isShared_392_ == 0)
{
v___x_396_ = v___x_391_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_log_385_);
lean_ctor_set(v_reuseFailAlloc_398_, 1, v_trace_388_);
lean_ctor_set(v_reuseFailAlloc_398_, 2, v_buildTime_389_);
lean_ctor_set_uint8(v_reuseFailAlloc_398_, sizeof(void*)*3 + 1, v_wantsRebuild_387_);
v___x_396_ = v_reuseFailAlloc_398_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; 
lean_ctor_set_uint8(v___x_396_, sizeof(void*)*3, v___x_394_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v___x_393_);
lean_ctor_set(v___x_397_, 1, v___x_396_);
return v___x_397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg___boxed(lean_object* v_action_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
uint8_t v_action_boxed_403_; lean_object* v_res_404_; 
v_action_boxed_403_ = lean_unbox(v_action_400_);
v_res_404_ = l_Lake_updateAction___redArg(v_action_boxed_403_, v_a_401_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction(uint8_t v_action_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_log_413_; uint8_t v_action_414_; uint8_t v_wantsRebuild_415_; lean_object* v_trace_416_; lean_object* v_buildTime_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_427_; 
v_log_413_ = lean_ctor_get(v_a_411_, 0);
v_action_414_ = lean_ctor_get_uint8(v_a_411_, sizeof(void*)*3);
v_wantsRebuild_415_ = lean_ctor_get_uint8(v_a_411_, sizeof(void*)*3 + 1);
v_trace_416_ = lean_ctor_get(v_a_411_, 1);
v_buildTime_417_ = lean_ctor_get(v_a_411_, 2);
v_isSharedCheck_427_ = !lean_is_exclusive(v_a_411_);
if (v_isSharedCheck_427_ == 0)
{
v___x_419_ = v_a_411_;
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_buildTime_417_);
lean_inc(v_trace_416_);
lean_inc(v_log_413_);
lean_dec(v_a_411_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_427_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; uint8_t v___x_422_; lean_object* v___x_424_; 
v___x_421_ = lean_box(0);
v___x_422_ = l_Lake_JobAction_merge(v_action_414_, v_action_405_);
if (v_isShared_420_ == 0)
{
v___x_424_ = v___x_419_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_log_413_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_trace_416_);
lean_ctor_set(v_reuseFailAlloc_426_, 2, v_buildTime_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_426_, sizeof(void*)*3 + 1, v_wantsRebuild_415_);
v___x_424_ = v_reuseFailAlloc_426_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_425_; 
lean_ctor_set_uint8(v___x_424_, sizeof(void*)*3, v___x_422_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_421_);
lean_ctor_set(v___x_425_, 1, v___x_424_);
return v___x_425_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___boxed(lean_object* v_action_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
uint8_t v_action_boxed_436_; lean_object* v_res_437_; 
v_action_boxed_436_ = lean_unbox(v_action_428_);
v_res_437_ = l_Lake_updateAction(v_action_boxed_436_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_);
lean_dec_ref(v_a_433_);
lean_dec(v_a_432_);
lean_dec(v_a_431_);
lean_dec(v_a_430_);
lean_dec_ref(v_a_429_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg(lean_object* v_a_438_){
_start:
{
lean_object* v_trace_440_; lean_object* v___x_441_; 
v_trace_440_ = lean_ctor_get(v_a_438_, 1);
lean_inc_ref(v_trace_440_);
v___x_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_441_, 0, v_trace_440_);
lean_ctor_set(v___x_441_, 1, v_a_438_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg___boxed(lean_object* v_a_442_, lean_object* v_a_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lake_getTrace___redArg(v_a_442_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace(lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_, lean_object* v_a_448_, lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_trace_452_; lean_object* v___x_453_; 
v_trace_452_ = lean_ctor_get(v_a_450_, 1);
lean_inc_ref(v_trace_452_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v_trace_452_);
lean_ctor_set(v___x_453_, 1, v_a_450_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___boxed(lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_, lean_object* v_a_458_, lean_object* v_a_459_, lean_object* v_a_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lake_getTrace(v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_);
lean_dec_ref(v_a_458_);
lean_dec(v_a_457_);
lean_dec(v_a_456_);
lean_dec(v_a_455_);
lean_dec_ref(v_a_454_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg(lean_object* v_trace_462_, lean_object* v_a_463_){
_start:
{
lean_object* v_log_465_; uint8_t v_action_466_; uint8_t v_wantsRebuild_467_; lean_object* v_buildTime_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v_log_465_ = lean_ctor_get(v_a_463_, 0);
v_action_466_ = lean_ctor_get_uint8(v_a_463_, sizeof(void*)*3);
v_wantsRebuild_467_ = lean_ctor_get_uint8(v_a_463_, sizeof(void*)*3 + 1);
v_buildTime_468_ = lean_ctor_get(v_a_463_, 2);
v_isSharedCheck_477_ = !lean_is_exclusive(v_a_463_);
if (v_isSharedCheck_477_ == 0)
{
lean_object* v_unused_478_; 
v_unused_478_ = lean_ctor_get(v_a_463_, 1);
lean_dec(v_unused_478_);
v___x_470_ = v_a_463_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_buildTime_468_);
lean_inc(v_log_465_);
lean_dec(v_a_463_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_472_ = lean_box(0);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 1, v_trace_462_);
v___x_474_ = v___x_470_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_log_465_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_trace_462_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_buildTime_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*3, v_action_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*3 + 1, v_wantsRebuild_467_);
v___x_474_ = v_reuseFailAlloc_476_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
lean_object* v___x_475_; 
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___x_472_);
lean_ctor_set(v___x_475_, 1, v___x_474_);
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg___boxed(lean_object* v_trace_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lake_setTrace___redArg(v_trace_479_, v_a_480_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace(lean_object* v_trace_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_log_491_; uint8_t v_action_492_; uint8_t v_wantsRebuild_493_; lean_object* v_buildTime_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_503_; 
v_log_491_ = lean_ctor_get(v_a_489_, 0);
v_action_492_ = lean_ctor_get_uint8(v_a_489_, sizeof(void*)*3);
v_wantsRebuild_493_ = lean_ctor_get_uint8(v_a_489_, sizeof(void*)*3 + 1);
v_buildTime_494_ = lean_ctor_get(v_a_489_, 2);
v_isSharedCheck_503_ = !lean_is_exclusive(v_a_489_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v_a_489_, 1);
lean_dec(v_unused_504_);
v___x_496_ = v_a_489_;
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_buildTime_494_);
lean_inc(v_log_491_);
lean_dec(v_a_489_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_503_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_500_; 
v___x_498_ = lean_box(0);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_trace_483_);
v___x_500_ = v___x_496_;
goto v_reusejp_499_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_log_491_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_trace_483_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_buildTime_494_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*3, v_action_492_);
lean_ctor_set_uint8(v_reuseFailAlloc_502_, sizeof(void*)*3 + 1, v_wantsRebuild_493_);
v___x_500_ = v_reuseFailAlloc_502_;
goto v_reusejp_499_;
}
v_reusejp_499_:
{
lean_object* v___x_501_; 
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_498_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
return v___x_501_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___boxed(lean_object* v_trace_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lake_setTrace(v_trace_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec(v_a_508_);
lean_dec(v_a_507_);
lean_dec_ref(v_a_506_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg(lean_object* v_caption_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_log_517_; uint8_t v_action_518_; uint8_t v_wantsRebuild_519_; lean_object* v_buildTime_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_530_; 
v_log_517_ = lean_ctor_get(v_a_515_, 0);
v_action_518_ = lean_ctor_get_uint8(v_a_515_, sizeof(void*)*3);
v_wantsRebuild_519_ = lean_ctor_get_uint8(v_a_515_, sizeof(void*)*3 + 1);
v_buildTime_520_ = lean_ctor_get(v_a_515_, 2);
v_isSharedCheck_530_ = !lean_is_exclusive(v_a_515_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_a_515_, 1);
lean_dec(v_unused_531_);
v___x_522_ = v_a_515_;
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_buildTime_520_);
lean_inc(v_log_517_);
lean_dec(v_a_515_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_530_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_527_; 
v___x_524_ = l_Lake_BuildTrace_nil(v_caption_514_);
v___x_525_ = lean_box(0);
if (v_isShared_523_ == 0)
{
lean_ctor_set(v___x_522_, 1, v___x_524_);
v___x_527_ = v___x_522_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_log_517_);
lean_ctor_set(v_reuseFailAlloc_529_, 1, v___x_524_);
lean_ctor_set(v_reuseFailAlloc_529_, 2, v_buildTime_520_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3, v_action_518_);
lean_ctor_set_uint8(v_reuseFailAlloc_529_, sizeof(void*)*3 + 1, v_wantsRebuild_519_);
v___x_527_ = v_reuseFailAlloc_529_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
lean_object* v___x_528_; 
v___x_528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_525_);
lean_ctor_set(v___x_528_, 1, v___x_527_);
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg___boxed(lean_object* v_caption_532_, lean_object* v_a_533_, lean_object* v_a_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lake_newTrace___redArg(v_caption_532_, v_a_533_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace(lean_object* v_caption_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_log_544_; uint8_t v_action_545_; uint8_t v_wantsRebuild_546_; lean_object* v_buildTime_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_557_; 
v_log_544_ = lean_ctor_get(v_a_542_, 0);
v_action_545_ = lean_ctor_get_uint8(v_a_542_, sizeof(void*)*3);
v_wantsRebuild_546_ = lean_ctor_get_uint8(v_a_542_, sizeof(void*)*3 + 1);
v_buildTime_547_ = lean_ctor_get(v_a_542_, 2);
v_isSharedCheck_557_ = !lean_is_exclusive(v_a_542_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v_a_542_, 1);
lean_dec(v_unused_558_);
v___x_549_ = v_a_542_;
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_buildTime_547_);
lean_inc(v_log_544_);
lean_dec(v_a_542_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_551_ = l_Lake_BuildTrace_nil(v_caption_536_);
v___x_552_ = lean_box(0);
if (v_isShared_550_ == 0)
{
lean_ctor_set(v___x_549_, 1, v___x_551_);
v___x_554_ = v___x_549_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_log_544_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_buildTime_547_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*3, v_action_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*3 + 1, v_wantsRebuild_546_);
v___x_554_ = v_reuseFailAlloc_556_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; 
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_552_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___boxed(lean_object* v_caption_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_, lean_object* v_a_564_, lean_object* v_a_565_, lean_object* v_a_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l_Lake_newTrace(v_caption_559_, v_a_560_, v_a_561_, v_a_562_, v_a_563_, v_a_564_, v_a_565_);
lean_dec_ref(v_a_564_);
lean_dec(v_a_563_);
lean_dec(v_a_562_);
lean_dec(v_a_561_);
lean_dec_ref(v_a_560_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg(lean_object* v_f_568_, lean_object* v_a_569_){
_start:
{
lean_object* v_log_571_; uint8_t v_action_572_; uint8_t v_wantsRebuild_573_; lean_object* v_trace_574_; lean_object* v_buildTime_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_585_; 
v_log_571_ = lean_ctor_get(v_a_569_, 0);
v_action_572_ = lean_ctor_get_uint8(v_a_569_, sizeof(void*)*3);
v_wantsRebuild_573_ = lean_ctor_get_uint8(v_a_569_, sizeof(void*)*3 + 1);
v_trace_574_ = lean_ctor_get(v_a_569_, 1);
v_buildTime_575_ = lean_ctor_get(v_a_569_, 2);
v_isSharedCheck_585_ = !lean_is_exclusive(v_a_569_);
if (v_isSharedCheck_585_ == 0)
{
v___x_577_ = v_a_569_;
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_buildTime_575_);
lean_inc(v_trace_574_);
lean_inc(v_log_571_);
lean_dec(v_a_569_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_585_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
v___x_579_ = lean_box(0);
v___x_580_ = lean_apply_1(v_f_568_, v_trace_574_);
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v___x_580_);
v___x_582_ = v___x_577_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_log_571_);
lean_ctor_set(v_reuseFailAlloc_584_, 1, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_584_, 2, v_buildTime_575_);
lean_ctor_set_uint8(v_reuseFailAlloc_584_, sizeof(void*)*3, v_action_572_);
lean_ctor_set_uint8(v_reuseFailAlloc_584_, sizeof(void*)*3 + 1, v_wantsRebuild_573_);
v___x_582_ = v_reuseFailAlloc_584_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_583_; 
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_579_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
return v___x_583_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg___boxed(lean_object* v_f_586_, lean_object* v_a_587_, lean_object* v_a_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lake_modifyTrace___redArg(v_f_586_, v_a_587_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace(lean_object* v_f_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_log_598_; uint8_t v_action_599_; uint8_t v_wantsRebuild_600_; lean_object* v_trace_601_; lean_object* v_buildTime_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_612_; 
v_log_598_ = lean_ctor_get(v_a_596_, 0);
v_action_599_ = lean_ctor_get_uint8(v_a_596_, sizeof(void*)*3);
v_wantsRebuild_600_ = lean_ctor_get_uint8(v_a_596_, sizeof(void*)*3 + 1);
v_trace_601_ = lean_ctor_get(v_a_596_, 1);
v_buildTime_602_ = lean_ctor_get(v_a_596_, 2);
v_isSharedCheck_612_ = !lean_is_exclusive(v_a_596_);
if (v_isSharedCheck_612_ == 0)
{
v___x_604_ = v_a_596_;
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_buildTime_602_);
lean_inc(v_trace_601_);
lean_inc(v_log_598_);
lean_dec(v_a_596_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_609_; 
v___x_606_ = lean_box(0);
v___x_607_ = lean_apply_1(v_f_590_, v_trace_601_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v___x_607_);
v___x_609_ = v___x_604_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_log_598_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_611_, 2, v_buildTime_602_);
lean_ctor_set_uint8(v_reuseFailAlloc_611_, sizeof(void*)*3, v_action_599_);
lean_ctor_set_uint8(v_reuseFailAlloc_611_, sizeof(void*)*3 + 1, v_wantsRebuild_600_);
v___x_609_ = v_reuseFailAlloc_611_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
lean_object* v___x_610_; 
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_606_);
lean_ctor_set(v___x_610_, 1, v___x_609_);
return v___x_610_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___boxed(lean_object* v_f_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_, lean_object* v_a_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lake_modifyTrace(v_f_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_);
lean_dec_ref(v_a_618_);
lean_dec(v_a_617_);
lean_dec(v_a_616_);
lean_dec(v_a_615_);
lean_dec_ref(v_a_614_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg(lean_object* v_caption_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_trace_625_; lean_object* v_log_626_; uint8_t v_action_627_; uint8_t v_wantsRebuild_628_; lean_object* v_buildTime_629_; lean_object* v___x_631_; uint8_t v_isShared_632_; uint8_t v_isSharedCheck_649_; 
v_trace_625_ = lean_ctor_get(v_a_623_, 1);
v_log_626_ = lean_ctor_get(v_a_623_, 0);
v_action_627_ = lean_ctor_get_uint8(v_a_623_, sizeof(void*)*3);
v_wantsRebuild_628_ = lean_ctor_get_uint8(v_a_623_, sizeof(void*)*3 + 1);
v_buildTime_629_ = lean_ctor_get(v_a_623_, 2);
v_isSharedCheck_649_ = !lean_is_exclusive(v_a_623_);
if (v_isSharedCheck_649_ == 0)
{
v___x_631_ = v_a_623_;
v_isShared_632_ = v_isSharedCheck_649_;
goto v_resetjp_630_;
}
else
{
lean_inc(v_buildTime_629_);
lean_inc(v_trace_625_);
lean_inc(v_log_626_);
lean_dec(v_a_623_);
v___x_631_ = lean_box(0);
v_isShared_632_ = v_isSharedCheck_649_;
goto v_resetjp_630_;
}
v_resetjp_630_:
{
lean_object* v_inputs_633_; uint64_t v_hash_634_; lean_object* v_mtime_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_647_; 
v_inputs_633_ = lean_ctor_get(v_trace_625_, 1);
v_hash_634_ = lean_ctor_get_uint64(v_trace_625_, sizeof(void*)*3);
v_mtime_635_ = lean_ctor_get(v_trace_625_, 2);
v_isSharedCheck_647_ = !lean_is_exclusive(v_trace_625_);
if (v_isSharedCheck_647_ == 0)
{
lean_object* v_unused_648_; 
v_unused_648_ = lean_ctor_get(v_trace_625_, 0);
lean_dec(v_unused_648_);
v___x_637_ = v_trace_625_;
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_mtime_635_);
lean_inc(v_inputs_633_);
lean_dec(v_trace_625_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_641_; 
v___x_639_ = lean_box(0);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v_caption_622_);
v___x_641_ = v___x_637_;
goto v_reusejp_640_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v_caption_622_);
lean_ctor_set(v_reuseFailAlloc_646_, 1, v_inputs_633_);
lean_ctor_set(v_reuseFailAlloc_646_, 2, v_mtime_635_);
lean_ctor_set_uint64(v_reuseFailAlloc_646_, sizeof(void*)*3, v_hash_634_);
v___x_641_ = v_reuseFailAlloc_646_;
goto v_reusejp_640_;
}
v_reusejp_640_:
{
lean_object* v___x_643_; 
if (v_isShared_632_ == 0)
{
lean_ctor_set(v___x_631_, 1, v___x_641_);
v___x_643_ = v___x_631_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_log_626_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_641_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_buildTime_629_);
lean_ctor_set_uint8(v_reuseFailAlloc_645_, sizeof(void*)*3, v_action_627_);
lean_ctor_set_uint8(v_reuseFailAlloc_645_, sizeof(void*)*3 + 1, v_wantsRebuild_628_);
v___x_643_ = v_reuseFailAlloc_645_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
lean_object* v___x_644_; 
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_639_);
lean_ctor_set(v___x_644_, 1, v___x_643_);
return v___x_644_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg___boxed(lean_object* v_caption_650_, lean_object* v_a_651_, lean_object* v_a_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lake_setTraceCaption___redArg(v_caption_650_, v_a_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption(lean_object* v_caption_654_, lean_object* v_a_655_, lean_object* v_a_656_, lean_object* v_a_657_, lean_object* v_a_658_, lean_object* v_a_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_trace_662_; lean_object* v_log_663_; uint8_t v_action_664_; uint8_t v_wantsRebuild_665_; lean_object* v_buildTime_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_686_; 
v_trace_662_ = lean_ctor_get(v_a_660_, 1);
v_log_663_ = lean_ctor_get(v_a_660_, 0);
v_action_664_ = lean_ctor_get_uint8(v_a_660_, sizeof(void*)*3);
v_wantsRebuild_665_ = lean_ctor_get_uint8(v_a_660_, sizeof(void*)*3 + 1);
v_buildTime_666_ = lean_ctor_get(v_a_660_, 2);
v_isSharedCheck_686_ = !lean_is_exclusive(v_a_660_);
if (v_isSharedCheck_686_ == 0)
{
v___x_668_ = v_a_660_;
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_buildTime_666_);
lean_inc(v_trace_662_);
lean_inc(v_log_663_);
lean_dec(v_a_660_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_686_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_inputs_670_; uint64_t v_hash_671_; lean_object* v_mtime_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_684_; 
v_inputs_670_ = lean_ctor_get(v_trace_662_, 1);
v_hash_671_ = lean_ctor_get_uint64(v_trace_662_, sizeof(void*)*3);
v_mtime_672_ = lean_ctor_get(v_trace_662_, 2);
v_isSharedCheck_684_ = !lean_is_exclusive(v_trace_662_);
if (v_isSharedCheck_684_ == 0)
{
lean_object* v_unused_685_; 
v_unused_685_ = lean_ctor_get(v_trace_662_, 0);
lean_dec(v_unused_685_);
v___x_674_ = v_trace_662_;
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_mtime_672_);
lean_inc(v_inputs_670_);
lean_dec(v_trace_662_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_684_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v_caption_654_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_683_; 
v_reuseFailAlloc_683_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_683_, 0, v_caption_654_);
lean_ctor_set(v_reuseFailAlloc_683_, 1, v_inputs_670_);
lean_ctor_set(v_reuseFailAlloc_683_, 2, v_mtime_672_);
lean_ctor_set_uint64(v_reuseFailAlloc_683_, sizeof(void*)*3, v_hash_671_);
v___x_678_ = v_reuseFailAlloc_683_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; 
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 1, v___x_678_);
v___x_680_ = v___x_668_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v_log_663_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_682_, 2, v_buildTime_666_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*3, v_action_664_);
lean_ctor_set_uint8(v_reuseFailAlloc_682_, sizeof(void*)*3 + 1, v_wantsRebuild_665_);
v___x_680_ = v_reuseFailAlloc_682_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
lean_object* v___x_681_; 
v___x_681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_676_);
lean_ctor_set(v___x_681_, 1, v___x_680_);
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___boxed(lean_object* v_caption_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_Lake_setTraceCaption(v_caption_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
lean_dec_ref(v_a_692_);
lean_dec(v_a_691_);
lean_dec(v_a_690_);
lean_dec(v_a_689_);
lean_dec_ref(v_a_688_);
return v_res_695_;
}
}
static lean_object* _init_l_Lake_takeTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Lake_takeTrace___redArg___closed__0));
v___x_698_ = l_Lake_BuildTrace_nil(v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg(lean_object* v_a_699_){
_start:
{
lean_object* v_log_701_; uint8_t v_action_702_; uint8_t v_wantsRebuild_703_; lean_object* v_trace_704_; lean_object* v_buildTime_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_714_; 
v_log_701_ = lean_ctor_get(v_a_699_, 0);
v_action_702_ = lean_ctor_get_uint8(v_a_699_, sizeof(void*)*3);
v_wantsRebuild_703_ = lean_ctor_get_uint8(v_a_699_, sizeof(void*)*3 + 1);
v_trace_704_ = lean_ctor_get(v_a_699_, 1);
v_buildTime_705_ = lean_ctor_get(v_a_699_, 2);
v_isSharedCheck_714_ = !lean_is_exclusive(v_a_699_);
if (v_isSharedCheck_714_ == 0)
{
v___x_707_ = v_a_699_;
v_isShared_708_ = v_isSharedCheck_714_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_buildTime_705_);
lean_inc(v_trace_704_);
lean_inc(v_log_701_);
lean_dec(v_a_699_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_714_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 1, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_log_701_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_buildTime_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*3, v_action_702_);
lean_ctor_set_uint8(v_reuseFailAlloc_713_, sizeof(void*)*3 + 1, v_wantsRebuild_703_);
v___x_711_ = v_reuseFailAlloc_713_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
lean_object* v___x_712_; 
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_trace_704_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
return v___x_712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg___boxed(lean_object* v_a_715_, lean_object* v_a_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lake_takeTrace___redArg(v_a_715_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace(lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_){
_start:
{
lean_object* v_log_725_; uint8_t v_action_726_; uint8_t v_wantsRebuild_727_; lean_object* v_trace_728_; lean_object* v_buildTime_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_738_; 
v_log_725_ = lean_ctor_get(v_a_723_, 0);
v_action_726_ = lean_ctor_get_uint8(v_a_723_, sizeof(void*)*3);
v_wantsRebuild_727_ = lean_ctor_get_uint8(v_a_723_, sizeof(void*)*3 + 1);
v_trace_728_ = lean_ctor_get(v_a_723_, 1);
v_buildTime_729_ = lean_ctor_get(v_a_723_, 2);
v_isSharedCheck_738_ = !lean_is_exclusive(v_a_723_);
if (v_isSharedCheck_738_ == 0)
{
v___x_731_ = v_a_723_;
v_isShared_732_ = v_isSharedCheck_738_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_buildTime_729_);
lean_inc(v_trace_728_);
lean_inc(v_log_725_);
lean_dec(v_a_723_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_738_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_733_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_732_ == 0)
{
lean_ctor_set(v___x_731_, 1, v___x_733_);
v___x_735_ = v___x_731_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_log_725_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_733_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_buildTime_729_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*3, v_action_726_);
lean_ctor_set_uint8(v_reuseFailAlloc_737_, sizeof(void*)*3 + 1, v_wantsRebuild_727_);
v___x_735_ = v_reuseFailAlloc_737_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; 
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v_trace_728_);
lean_ctor_set(v___x_736_, 1, v___x_735_);
return v___x_736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___boxed(lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lake_takeTrace(v_a_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec(v_a_741_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg(lean_object* v_trace_747_, lean_object* v_a_748_){
_start:
{
lean_object* v_log_750_; uint8_t v_action_751_; uint8_t v_wantsRebuild_752_; lean_object* v_trace_753_; lean_object* v_buildTime_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_762_; 
v_log_750_ = lean_ctor_get(v_a_748_, 0);
v_action_751_ = lean_ctor_get_uint8(v_a_748_, sizeof(void*)*3);
v_wantsRebuild_752_ = lean_ctor_get_uint8(v_a_748_, sizeof(void*)*3 + 1);
v_trace_753_ = lean_ctor_get(v_a_748_, 1);
v_buildTime_754_ = lean_ctor_get(v_a_748_, 2);
v_isSharedCheck_762_ = !lean_is_exclusive(v_a_748_);
if (v_isSharedCheck_762_ == 0)
{
v___x_756_ = v_a_748_;
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_buildTime_754_);
lean_inc(v_trace_753_);
lean_inc(v_log_750_);
lean_dec(v_a_748_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_762_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
lean_ctor_set(v___x_756_, 1, v_trace_747_);
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_log_750_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_trace_747_);
lean_ctor_set(v_reuseFailAlloc_761_, 2, v_buildTime_754_);
lean_ctor_set_uint8(v_reuseFailAlloc_761_, sizeof(void*)*3, v_action_751_);
lean_ctor_set_uint8(v_reuseFailAlloc_761_, sizeof(void*)*3 + 1, v_wantsRebuild_752_);
v___x_759_ = v_reuseFailAlloc_761_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; 
v___x_760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_760_, 0, v_trace_753_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
return v___x_760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg___boxed(lean_object* v_trace_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_res_766_; 
v_res_766_ = l_Lake_swapTrace___redArg(v_trace_763_, v_a_764_);
return v_res_766_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace(lean_object* v_trace_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_){
_start:
{
lean_object* v_log_775_; uint8_t v_action_776_; uint8_t v_wantsRebuild_777_; lean_object* v_trace_778_; lean_object* v_buildTime_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
v_log_775_ = lean_ctor_get(v_a_773_, 0);
v_action_776_ = lean_ctor_get_uint8(v_a_773_, sizeof(void*)*3);
v_wantsRebuild_777_ = lean_ctor_get_uint8(v_a_773_, sizeof(void*)*3 + 1);
v_trace_778_ = lean_ctor_get(v_a_773_, 1);
v_buildTime_779_ = lean_ctor_get(v_a_773_, 2);
v_isSharedCheck_787_ = !lean_is_exclusive(v_a_773_);
if (v_isSharedCheck_787_ == 0)
{
v___x_781_ = v_a_773_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_buildTime_779_);
lean_inc(v_trace_778_);
lean_inc(v_log_775_);
lean_dec(v_a_773_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_trace_767_);
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_log_775_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v_trace_767_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v_buildTime_779_);
lean_ctor_set_uint8(v_reuseFailAlloc_786_, sizeof(void*)*3, v_action_776_);
lean_ctor_set_uint8(v_reuseFailAlloc_786_, sizeof(void*)*3 + 1, v_wantsRebuild_777_);
v___x_784_ = v_reuseFailAlloc_786_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
lean_object* v___x_785_; 
v___x_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_785_, 0, v_trace_778_);
lean_ctor_set(v___x_785_, 1, v___x_784_);
return v___x_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___boxed(lean_object* v_trace_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lake_swapTrace(v_trace_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
lean_dec_ref(v_a_793_);
lean_dec(v_a_792_);
lean_dec(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg(lean_object* v_trace_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_log_800_; uint8_t v_action_801_; uint8_t v_wantsRebuild_802_; lean_object* v_trace_803_; lean_object* v_buildTime_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_814_; 
v_log_800_ = lean_ctor_get(v_a_798_, 0);
v_action_801_ = lean_ctor_get_uint8(v_a_798_, sizeof(void*)*3);
v_wantsRebuild_802_ = lean_ctor_get_uint8(v_a_798_, sizeof(void*)*3 + 1);
v_trace_803_ = lean_ctor_get(v_a_798_, 1);
v_buildTime_804_ = lean_ctor_get(v_a_798_, 2);
v_isSharedCheck_814_ = !lean_is_exclusive(v_a_798_);
if (v_isSharedCheck_814_ == 0)
{
v___x_806_ = v_a_798_;
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_buildTime_804_);
lean_inc(v_trace_803_);
lean_inc(v_log_800_);
lean_dec(v_a_798_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_814_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_811_; 
v___x_808_ = lean_box(0);
v___x_809_ = l_Lake_BuildTrace_mix(v_trace_803_, v_trace_797_);
if (v_isShared_807_ == 0)
{
lean_ctor_set(v___x_806_, 1, v___x_809_);
v___x_811_ = v___x_806_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_log_800_);
lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_809_);
lean_ctor_set(v_reuseFailAlloc_813_, 2, v_buildTime_804_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*3, v_action_801_);
lean_ctor_set_uint8(v_reuseFailAlloc_813_, sizeof(void*)*3 + 1, v_wantsRebuild_802_);
v___x_811_ = v_reuseFailAlloc_813_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
lean_object* v___x_812_; 
v___x_812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_812_, 0, v___x_808_);
lean_ctor_set(v___x_812_, 1, v___x_811_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg___boxed(lean_object* v_trace_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Lake_addTrace___redArg(v_trace_815_, v_a_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace(lean_object* v_trace_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_log_827_; uint8_t v_action_828_; uint8_t v_wantsRebuild_829_; lean_object* v_trace_830_; lean_object* v_buildTime_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_841_; 
v_log_827_ = lean_ctor_get(v_a_825_, 0);
v_action_828_ = lean_ctor_get_uint8(v_a_825_, sizeof(void*)*3);
v_wantsRebuild_829_ = lean_ctor_get_uint8(v_a_825_, sizeof(void*)*3 + 1);
v_trace_830_ = lean_ctor_get(v_a_825_, 1);
v_buildTime_831_ = lean_ctor_get(v_a_825_, 2);
v_isSharedCheck_841_ = !lean_is_exclusive(v_a_825_);
if (v_isSharedCheck_841_ == 0)
{
v___x_833_ = v_a_825_;
v_isShared_834_ = v_isSharedCheck_841_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_buildTime_831_);
lean_inc(v_trace_830_);
lean_inc(v_log_827_);
lean_dec(v_a_825_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_841_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_838_; 
v___x_835_ = lean_box(0);
v___x_836_ = l_Lake_BuildTrace_mix(v_trace_830_, v_trace_819_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v___x_836_);
v___x_838_ = v___x_833_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v_log_827_);
lean_ctor_set(v_reuseFailAlloc_840_, 1, v___x_836_);
lean_ctor_set(v_reuseFailAlloc_840_, 2, v_buildTime_831_);
lean_ctor_set_uint8(v_reuseFailAlloc_840_, sizeof(void*)*3, v_action_828_);
lean_ctor_set_uint8(v_reuseFailAlloc_840_, sizeof(void*)*3 + 1, v_wantsRebuild_829_);
v___x_838_ = v_reuseFailAlloc_840_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
lean_object* v___x_839_; 
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_835_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
return v___x_839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___boxed(lean_object* v_trace_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lake_addTrace(v_trace_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg(lean_object* v_caption_851_, lean_object* v_x_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_log_860_; uint8_t v_action_861_; uint8_t v_wantsRebuild_862_; lean_object* v_trace_863_; lean_object* v_buildTime_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_895_; 
v_log_860_ = lean_ctor_get(v_a_858_, 0);
v_action_861_ = lean_ctor_get_uint8(v_a_858_, sizeof(void*)*3);
v_wantsRebuild_862_ = lean_ctor_get_uint8(v_a_858_, sizeof(void*)*3 + 1);
v_trace_863_ = lean_ctor_get(v_a_858_, 1);
v_buildTime_864_ = lean_ctor_get(v_a_858_, 2);
v_isSharedCheck_895_ = !lean_is_exclusive(v_a_858_);
if (v_isSharedCheck_895_ == 0)
{
v___x_866_ = v_a_858_;
v_isShared_867_ = v_isSharedCheck_895_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_buildTime_864_);
lean_inc(v_trace_863_);
lean_inc(v_log_860_);
lean_dec(v_a_858_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_895_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = l_Lake_BuildTrace_nil(v_caption_851_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 1, v___x_868_);
v___x_870_ = v___x_866_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_log_860_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___x_868_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v_buildTime_864_);
lean_ctor_set_uint8(v_reuseFailAlloc_894_, sizeof(void*)*3, v_action_861_);
lean_ctor_set_uint8(v_reuseFailAlloc_894_, sizeof(void*)*3 + 1, v_wantsRebuild_862_);
v___x_870_ = v_reuseFailAlloc_894_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
lean_object* v___x_871_; 
lean_inc_ref(v_a_857_);
lean_inc(v_a_856_);
lean_inc(v_a_855_);
lean_inc(v_a_854_);
v___x_871_ = lean_apply_7(v_x_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v___x_870_, lean_box(0));
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_893_; 
v_a_872_ = lean_ctor_get(v___x_871_, 1);
v_a_873_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_893_ == 0)
{
v___x_875_ = v___x_871_;
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_872_);
lean_inc(v_a_873_);
lean_dec(v___x_871_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_893_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v_log_877_; uint8_t v_action_878_; uint8_t v_wantsRebuild_879_; lean_object* v_trace_880_; lean_object* v_buildTime_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_892_; 
v_log_877_ = lean_ctor_get(v_a_872_, 0);
v_action_878_ = lean_ctor_get_uint8(v_a_872_, sizeof(void*)*3);
v_wantsRebuild_879_ = lean_ctor_get_uint8(v_a_872_, sizeof(void*)*3 + 1);
v_trace_880_ = lean_ctor_get(v_a_872_, 1);
v_buildTime_881_ = lean_ctor_get(v_a_872_, 2);
v_isSharedCheck_892_ = !lean_is_exclusive(v_a_872_);
if (v_isSharedCheck_892_ == 0)
{
v___x_883_ = v_a_872_;
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_buildTime_881_);
lean_inc(v_trace_880_);
lean_inc(v_log_877_);
lean_dec(v_a_872_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_892_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = l_Lake_BuildTrace_mix(v_trace_863_, v_trace_880_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 1, v___x_885_);
v___x_887_ = v___x_883_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_log_877_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_891_, 2, v_buildTime_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, sizeof(void*)*3, v_action_878_);
lean_ctor_set_uint8(v_reuseFailAlloc_891_, sizeof(void*)*3 + 1, v_wantsRebuild_879_);
v___x_887_ = v_reuseFailAlloc_891_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_889_; 
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 1, v___x_887_);
v___x_889_ = v___x_875_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_873_);
lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
else
{
lean_dec_ref(v_trace_863_);
return v___x_871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg___boxed(lean_object* v_caption_896_, lean_object* v_x_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Lake_addSubTrace___redArg(v_caption_896_, v_x_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_);
lean_dec_ref(v_a_902_);
lean_dec(v_a_901_);
lean_dec(v_a_900_);
lean_dec(v_a_899_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace(lean_object* v_00_u03b1_906_, lean_object* v_caption_907_, lean_object* v_x_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_log_916_; uint8_t v_action_917_; uint8_t v_wantsRebuild_918_; lean_object* v_trace_919_; lean_object* v_buildTime_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_951_; 
v_log_916_ = lean_ctor_get(v_a_914_, 0);
v_action_917_ = lean_ctor_get_uint8(v_a_914_, sizeof(void*)*3);
v_wantsRebuild_918_ = lean_ctor_get_uint8(v_a_914_, sizeof(void*)*3 + 1);
v_trace_919_ = lean_ctor_get(v_a_914_, 1);
v_buildTime_920_ = lean_ctor_get(v_a_914_, 2);
v_isSharedCheck_951_ = !lean_is_exclusive(v_a_914_);
if (v_isSharedCheck_951_ == 0)
{
v___x_922_ = v_a_914_;
v_isShared_923_ = v_isSharedCheck_951_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_buildTime_920_);
lean_inc(v_trace_919_);
lean_inc(v_log_916_);
lean_dec(v_a_914_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_951_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_926_; 
v___x_924_ = l_Lake_BuildTrace_nil(v_caption_907_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 1, v___x_924_);
v___x_926_ = v___x_922_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_log_916_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_924_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v_buildTime_920_);
lean_ctor_set_uint8(v_reuseFailAlloc_950_, sizeof(void*)*3, v_action_917_);
lean_ctor_set_uint8(v_reuseFailAlloc_950_, sizeof(void*)*3 + 1, v_wantsRebuild_918_);
v___x_926_ = v_reuseFailAlloc_950_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
lean_object* v___x_927_; 
lean_inc_ref(v_a_913_);
lean_inc(v_a_912_);
lean_inc(v_a_911_);
lean_inc(v_a_910_);
v___x_927_ = lean_apply_7(v_x_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v___x_926_, lean_box(0));
if (lean_obj_tag(v___x_927_) == 0)
{
lean_object* v_a_928_; lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_949_; 
v_a_928_ = lean_ctor_get(v___x_927_, 1);
v_a_929_ = lean_ctor_get(v___x_927_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_927_);
if (v_isSharedCheck_949_ == 0)
{
v___x_931_ = v___x_927_;
v_isShared_932_ = v_isSharedCheck_949_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_928_);
lean_inc(v_a_929_);
lean_dec(v___x_927_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_949_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v_log_933_; uint8_t v_action_934_; uint8_t v_wantsRebuild_935_; lean_object* v_trace_936_; lean_object* v_buildTime_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_948_; 
v_log_933_ = lean_ctor_get(v_a_928_, 0);
v_action_934_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*3);
v_wantsRebuild_935_ = lean_ctor_get_uint8(v_a_928_, sizeof(void*)*3 + 1);
v_trace_936_ = lean_ctor_get(v_a_928_, 1);
v_buildTime_937_ = lean_ctor_get(v_a_928_, 2);
v_isSharedCheck_948_ = !lean_is_exclusive(v_a_928_);
if (v_isSharedCheck_948_ == 0)
{
v___x_939_ = v_a_928_;
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_buildTime_937_);
lean_inc(v_trace_936_);
lean_inc(v_log_933_);
lean_dec(v_a_928_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_948_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_943_; 
v___x_941_ = l_Lake_BuildTrace_mix(v_trace_919_, v_trace_936_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 1, v___x_941_);
v___x_943_ = v___x_939_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_log_933_);
lean_ctor_set(v_reuseFailAlloc_947_, 1, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_947_, 2, v_buildTime_937_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*3, v_action_934_);
lean_ctor_set_uint8(v_reuseFailAlloc_947_, sizeof(void*)*3 + 1, v_wantsRebuild_935_);
v___x_943_ = v_reuseFailAlloc_947_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
lean_object* v___x_945_; 
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 1, v___x_943_);
v___x_945_ = v___x_931_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_a_929_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
else
{
lean_dec_ref(v_trace_919_);
return v___x_927_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___boxed(lean_object* v_00_u03b1_952_, lean_object* v_caption_953_, lean_object* v_x_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lake_addSubTrace(v_00_u03b1_952_, v_caption_953_, v_x_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_, v_a_959_, v_a_960_);
lean_dec_ref(v_a_959_);
lean_dec(v_a_958_);
lean_dec(v_a_957_);
lean_dec(v_a_956_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg(lean_object* v_f_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_){
_start:
{
lean_object* v___x_971_; 
lean_inc_ref(v_a_969_);
lean_inc_ref(v_a_968_);
lean_inc(v_a_967_);
lean_inc(v_a_966_);
lean_inc(v_a_965_);
v___x_971_ = lean_apply_7(v_f_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, lean_box(0));
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg___boxed(lean_object* v_f_972_, lean_object* v_a_973_, lean_object* v_a_974_, lean_object* v_a_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lake_SpawnM_ofFn___redArg(v_f_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_, v_a_978_);
lean_dec_ref(v_a_978_);
lean_dec_ref(v_a_977_);
lean_dec(v_a_976_);
lean_dec(v_a_975_);
lean_dec(v_a_974_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn(lean_object* v_00_u03b1_981_, lean_object* v_f_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
lean_object* v___x_990_; 
lean_inc_ref(v_a_988_);
lean_inc_ref(v_a_987_);
lean_inc(v_a_986_);
lean_inc(v_a_985_);
lean_inc(v_a_984_);
v___x_990_ = lean_apply_7(v_f_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, lean_box(0));
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___boxed(lean_object* v_00_u03b1_991_, lean_object* v_f_992_, lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lake_SpawnM_ofFn(v_00_u03b1_991_, v_f_992_, v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_);
lean_dec_ref(v_a_998_);
lean_dec_ref(v_a_997_);
lean_dec(v_a_996_);
lean_dec(v_a_995_);
lean_dec(v_a_994_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg(lean_object* v_self_1001_, lean_object* v_fetch_1002_, lean_object* v_pkg_x3f_1003_, lean_object* v_stack_1004_, lean_object* v_store_1005_, lean_object* v_ctx_1006_, lean_object* v_s_1007_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = lean_apply_7(v_self_1001_, v_fetch_1002_, v_pkg_x3f_1003_, v_stack_1004_, v_store_1005_, v_ctx_1006_, v_s_1007_, lean_box(0));
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg___boxed(lean_object* v_self_1010_, lean_object* v_fetch_1011_, lean_object* v_pkg_x3f_1012_, lean_object* v_stack_1013_, lean_object* v_store_1014_, lean_object* v_ctx_1015_, lean_object* v_s_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lake_SpawnM_toFn___redArg(v_self_1010_, v_fetch_1011_, v_pkg_x3f_1012_, v_stack_1013_, v_store_1014_, v_ctx_1015_, v_s_1016_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn(lean_object* v_00_u03b1_1019_, lean_object* v_self_1020_, lean_object* v_fetch_1021_, lean_object* v_pkg_x3f_1022_, lean_object* v_stack_1023_, lean_object* v_store_1024_, lean_object* v_ctx_1025_, lean_object* v_s_1026_){
_start:
{
lean_object* v___x_1028_; 
v___x_1028_ = lean_apply_7(v_self_1020_, v_fetch_1021_, v_pkg_x3f_1022_, v_stack_1023_, v_store_1024_, v_ctx_1025_, v_s_1026_, lean_box(0));
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_self_1030_, lean_object* v_fetch_1031_, lean_object* v_pkg_x3f_1032_, lean_object* v_stack_1033_, lean_object* v_store_1034_, lean_object* v_ctx_1035_, lean_object* v_s_1036_, lean_object* v_a_1037_){
_start:
{
lean_object* v_res_1038_; 
v_res_1038_ = l_Lake_SpawnM_toFn(v_00_u03b1_1029_, v_self_1030_, v_fetch_1031_, v_pkg_x3f_1032_, v_stack_1033_, v_store_1034_, v_ctx_1035_, v_s_1036_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg(lean_object* v_x_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v_trace_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_trace_1047_ = lean_ctor_get(v_a_1045_, 1);
lean_inc_ref(v_trace_1047_);
lean_inc_ref(v_a_1044_);
lean_inc(v_a_1043_);
lean_inc(v_a_1042_);
lean_inc(v_a_1041_);
v___x_1048_ = lean_apply_7(v_x_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_trace_1047_, lean_box(0));
v___x_1049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1049_, 0, v___x_1048_);
lean_ctor_set(v___x_1049_, 1, v_a_1045_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg___boxed(lean_object* v_x_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lake_JobM_runSpawnM___redArg(v_x_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec(v_a_1052_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM(lean_object* v_00_u03b1_1059_, lean_object* v_x_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_trace_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v_trace_1068_ = lean_ctor_get(v_a_1066_, 1);
lean_inc_ref(v_trace_1068_);
lean_inc_ref(v_a_1065_);
lean_inc(v_a_1064_);
lean_inc(v_a_1063_);
lean_inc(v_a_1062_);
v___x_1069_ = lean_apply_7(v_x_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_trace_1068_, lean_box(0));
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_a_1066_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___boxed(lean_object* v_00_u03b1_1071_, lean_object* v_x_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lake_JobM_runSpawnM(v_00_u03b1_1071_, v_x_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec(v_a_1074_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg(lean_object* v_x_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
uint8_t v___x_1091_; uint8_t v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1091_ = 0;
v___x_1092_ = 0;
v___x_1093_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1095_, 0, v_a_1089_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
lean_ctor_set(v___x_1095_, 2, v___x_1094_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3, v___x_1091_);
lean_ctor_set_uint8(v___x_1095_, sizeof(void*)*3 + 1, v___x_1092_);
lean_inc_ref(v_a_1088_);
lean_inc(v_a_1087_);
lean_inc(v_a_1086_);
lean_inc(v_a_1085_);
v___x_1096_ = lean_apply_7(v_x_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v___x_1095_, lean_box(0));
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v_a_1097_; lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1106_; 
v_a_1097_ = lean_ctor_get(v___x_1096_, 1);
v_a_1098_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1100_ = v___x_1096_;
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1097_);
lean_inc(v_a_1098_);
lean_dec(v___x_1096_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1106_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_log_1102_; lean_object* v___x_1104_; 
v_log_1102_ = lean_ctor_get(v_a_1097_, 0);
lean_inc_ref(v_log_1102_);
lean_dec(v_a_1097_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 1, v_log_1102_);
v___x_1104_ = v___x_1100_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1098_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_log_1102_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1116_; 
v_a_1107_ = lean_ctor_get(v___x_1096_, 1);
v_a_1108_ = lean_ctor_get(v___x_1096_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1110_ = v___x_1096_;
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1107_);
lean_inc(v_a_1108_);
lean_dec(v___x_1096_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1116_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v_log_1112_; lean_object* v___x_1114_; 
v_log_1112_ = lean_ctor_get(v_a_1107_, 0);
lean_inc_ref(v_log_1112_);
lean_dec(v_a_1107_);
if (v_isShared_1111_ == 0)
{
lean_ctor_set(v___x_1110_, 1, v_log_1112_);
v___x_1114_ = v___x_1110_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1108_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_log_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg___boxed(lean_object* v_x_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Lake_FetchM_runJobM___redArg(v_x_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec_ref(v_a_1122_);
lean_dec(v_a_1121_);
lean_dec(v_a_1120_);
lean_dec(v_a_1119_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM(lean_object* v_00_u03b1_1126_, lean_object* v_x_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
uint8_t v___x_1135_; uint8_t v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1135_ = 0;
v___x_1136_ = 0;
v___x_1137_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1138_ = lean_unsigned_to_nat(0u);
v___x_1139_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1139_, 0, v_a_1133_);
lean_ctor_set(v___x_1139_, 1, v___x_1137_);
lean_ctor_set(v___x_1139_, 2, v___x_1138_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*3, v___x_1135_);
lean_ctor_set_uint8(v___x_1139_, sizeof(void*)*3 + 1, v___x_1136_);
lean_inc_ref(v_a_1132_);
lean_inc(v_a_1131_);
lean_inc(v_a_1130_);
lean_inc(v_a_1129_);
v___x_1140_ = lean_apply_7(v_x_1127_, v_a_1128_, v_a_1129_, v_a_1130_, v_a_1131_, v_a_1132_, v___x_1139_, lean_box(0));
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1150_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 1);
v_a_1142_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1144_ = v___x_1140_;
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1141_);
lean_inc(v_a_1142_);
lean_dec(v___x_1140_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1150_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v_log_1146_; lean_object* v___x_1148_; 
v_log_1146_ = lean_ctor_get(v_a_1141_, 0);
lean_inc_ref(v_log_1146_);
lean_dec(v_a_1141_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 1, v_log_1146_);
v___x_1148_ = v___x_1144_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1142_);
lean_ctor_set(v_reuseFailAlloc_1149_, 1, v_log_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
else
{
lean_object* v_a_1151_; lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1160_; 
v_a_1151_ = lean_ctor_get(v___x_1140_, 1);
v_a_1152_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1154_ = v___x_1140_;
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1151_);
lean_inc(v_a_1152_);
lean_dec(v___x_1140_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1160_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_log_1156_; lean_object* v___x_1158_; 
v_log_1156_ = lean_ctor_get(v_a_1151_, 0);
lean_inc_ref(v_log_1156_);
lean_dec(v_a_1151_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 1, v_log_1156_);
v___x_1158_ = v___x_1154_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1152_);
lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_log_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___boxed(lean_object* v_00_u03b1_1161_, lean_object* v_x_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lake_FetchM_runJobM(v_00_u03b1_1161_, v_x_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec(v_a_1164_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg(lean_object* v_x_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_, lean_object* v_a_1179_){
_start:
{
lean_object* v_log_1181_; uint8_t v_action_1182_; uint8_t v_wantsRebuild_1183_; lean_object* v_trace_1184_; lean_object* v_buildTime_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1214_; 
v_log_1181_ = lean_ctor_get(v_a_1179_, 0);
v_action_1182_ = lean_ctor_get_uint8(v_a_1179_, sizeof(void*)*3);
v_wantsRebuild_1183_ = lean_ctor_get_uint8(v_a_1179_, sizeof(void*)*3 + 1);
v_trace_1184_ = lean_ctor_get(v_a_1179_, 1);
v_buildTime_1185_ = lean_ctor_get(v_a_1179_, 2);
v_isSharedCheck_1214_ = !lean_is_exclusive(v_a_1179_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1187_ = v_a_1179_;
v_isShared_1188_ = v_isSharedCheck_1214_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_buildTime_1185_);
lean_inc(v_trace_1184_);
lean_inc(v_log_1181_);
lean_dec(v_a_1179_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1214_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v___x_1189_; 
lean_inc_ref(v_a_1178_);
lean_inc(v_a_1177_);
lean_inc(v_a_1176_);
lean_inc(v_a_1175_);
v___x_1189_ = lean_apply_7(v_x_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_, v_a_1178_, v_log_1181_, lean_box(0));
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1201_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_a_1191_ = lean_ctor_get(v___x_1189_, 1);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1193_ = v___x_1189_;
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1201_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v_a_1191_);
v___x_1196_ = v___x_1187_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1191_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_trace_1184_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v_buildTime_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*3, v_action_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1200_, sizeof(void*)*3 + 1, v_wantsRebuild_1183_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1194_ == 0)
{
lean_ctor_set(v___x_1193_, 1, v___x_1196_);
v___x_1198_ = v___x_1193_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1190_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1213_; 
v_a_1202_ = lean_ctor_get(v___x_1189_, 0);
v_a_1203_ = lean_ctor_get(v___x_1189_, 1);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1205_ = v___x_1189_;
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_inc(v_a_1202_);
lean_dec(v___x_1189_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1213_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v_a_1203_);
v___x_1208_ = v___x_1187_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1203_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_trace_1184_);
lean_ctor_set(v_reuseFailAlloc_1212_, 2, v_buildTime_1185_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*3, v_action_1182_);
lean_ctor_set_uint8(v_reuseFailAlloc_1212_, sizeof(void*)*3 + 1, v_wantsRebuild_1183_);
v___x_1208_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1210_; 
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 1, v___x_1208_);
v___x_1210_ = v___x_1205_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1202_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v___x_1208_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg___boxed(lean_object* v_x_1215_, lean_object* v_a_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_, lean_object* v_a_1219_, lean_object* v_a_1220_, lean_object* v_a_1221_, lean_object* v_a_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Lake_JobM_runFetchM___redArg(v_x_1215_, v_a_1216_, v_a_1217_, v_a_1218_, v_a_1219_, v_a_1220_, v_a_1221_);
lean_dec_ref(v_a_1220_);
lean_dec(v_a_1219_);
lean_dec(v_a_1218_);
lean_dec(v_a_1217_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM(lean_object* v_00_u03b1_1224_, lean_object* v_x_1225_, lean_object* v_a_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_){
_start:
{
lean_object* v_log_1233_; uint8_t v_action_1234_; uint8_t v_wantsRebuild_1235_; lean_object* v_trace_1236_; lean_object* v_buildTime_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1266_; 
v_log_1233_ = lean_ctor_get(v_a_1231_, 0);
v_action_1234_ = lean_ctor_get_uint8(v_a_1231_, sizeof(void*)*3);
v_wantsRebuild_1235_ = lean_ctor_get_uint8(v_a_1231_, sizeof(void*)*3 + 1);
v_trace_1236_ = lean_ctor_get(v_a_1231_, 1);
v_buildTime_1237_ = lean_ctor_get(v_a_1231_, 2);
v_isSharedCheck_1266_ = !lean_is_exclusive(v_a_1231_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1239_ = v_a_1231_;
v_isShared_1240_ = v_isSharedCheck_1266_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_buildTime_1237_);
lean_inc(v_trace_1236_);
lean_inc(v_log_1233_);
lean_dec(v_a_1231_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1266_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1241_; 
lean_inc_ref(v_a_1230_);
lean_inc(v_a_1229_);
lean_inc(v_a_1228_);
lean_inc(v_a_1227_);
v___x_1241_ = lean_apply_7(v_x_1225_, v_a_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_log_1233_, lean_box(0));
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1253_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
v_a_1243_ = lean_ctor_get(v___x_1241_, 1);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1245_ = v___x_1241_;
v_isShared_1246_ = v_isSharedCheck_1253_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_inc(v_a_1242_);
lean_dec(v___x_1241_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1253_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_a_1243_);
v___x_1248_ = v___x_1239_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1243_);
lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_trace_1236_);
lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_buildTime_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*3, v_action_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1252_, sizeof(void*)*3 + 1, v_wantsRebuild_1235_);
v___x_1248_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1250_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 1, v___x_1248_);
v___x_1250_ = v___x_1245_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1242_);
lean_ctor_set(v_reuseFailAlloc_1251_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1265_; 
v_a_1254_ = lean_ctor_get(v___x_1241_, 0);
v_a_1255_ = lean_ctor_get(v___x_1241_, 1);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1257_ = v___x_1241_;
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_inc(v_a_1254_);
lean_dec(v___x_1241_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1265_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_a_1255_);
v___x_1260_ = v___x_1239_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1255_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_trace_1236_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_buildTime_1237_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*3, v_action_1234_);
lean_ctor_set_uint8(v_reuseFailAlloc_1264_, sizeof(void*)*3 + 1, v_wantsRebuild_1235_);
v___x_1260_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
lean_object* v___x_1262_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v___x_1260_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1254_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___boxed(lean_object* v_00_u03b1_1267_, lean_object* v_x_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lake_JobM_runFetchM(v_00_u03b1_1267_, v_x_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec(v_a_1271_);
lean_dec(v_a_1270_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0(lean_object* v_inst_1279_, lean_object* v_caption_1280_, uint8_t v_optional_1281_, lean_object* v_toPure_1282_, lean_object* v_____do__lift_1283_){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1284_, 0, v_____do__lift_1283_);
lean_ctor_set(v___x_1284_, 1, v_inst_1279_);
lean_ctor_set(v___x_1284_, 2, v_caption_1280_);
lean_ctor_set_uint8(v___x_1284_, sizeof(void*)*3, v_optional_1281_);
v___x_1285_ = lean_apply_2(v_toPure_1282_, lean_box(0), v___x_1284_);
return v___x_1285_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0___boxed(lean_object* v_inst_1286_, lean_object* v_caption_1287_, lean_object* v_optional_1288_, lean_object* v_toPure_1289_, lean_object* v_____do__lift_1290_){
_start:
{
uint8_t v_optional_boxed_1291_; lean_object* v_res_1292_; 
v_optional_boxed_1291_ = lean_unbox(v_optional_1288_);
v_res_1292_ = l_Lake_Job_bindTask___redArg___lam__0(v_inst_1286_, v_caption_1287_, v_optional_boxed_1291_, v_toPure_1289_, v_____do__lift_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg(lean_object* v_inst_1293_, lean_object* v_inst_1294_, lean_object* v_f_1295_, lean_object* v_self_1296_){
_start:
{
lean_object* v_toApplicative_1297_; lean_object* v_toBind_1298_; lean_object* v_task_1299_; lean_object* v_caption_1300_; uint8_t v_optional_1301_; lean_object* v_toPure_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___f_1305_; lean_object* v___x_1306_; 
v_toApplicative_1297_ = lean_ctor_get(v_inst_1293_, 0);
lean_inc_ref(v_toApplicative_1297_);
v_toBind_1298_ = lean_ctor_get(v_inst_1293_, 1);
lean_inc(v_toBind_1298_);
lean_dec_ref(v_inst_1293_);
v_task_1299_ = lean_ctor_get(v_self_1296_, 0);
lean_inc_ref(v_task_1299_);
v_caption_1300_ = lean_ctor_get(v_self_1296_, 2);
lean_inc_ref(v_caption_1300_);
v_optional_1301_ = lean_ctor_get_uint8(v_self_1296_, sizeof(void*)*3);
lean_dec_ref(v_self_1296_);
v_toPure_1302_ = lean_ctor_get(v_toApplicative_1297_, 1);
lean_inc(v_toPure_1302_);
lean_dec_ref(v_toApplicative_1297_);
v___x_1303_ = lean_apply_1(v_f_1295_, v_task_1299_);
v___x_1304_ = lean_box(v_optional_1301_);
v___f_1305_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1305_, 0, v_inst_1294_);
lean_closure_set(v___f_1305_, 1, v_caption_1300_);
lean_closure_set(v___f_1305_, 2, v___x_1304_);
lean_closure_set(v___f_1305_, 3, v_toPure_1302_);
v___x_1306_ = lean_apply_4(v_toBind_1298_, lean_box(0), lean_box(0), v___x_1303_, v___f_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask(lean_object* v_m_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_00_u03b1_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_f_1312_, lean_object* v_self_1313_){
_start:
{
lean_object* v_toApplicative_1314_; lean_object* v_toBind_1315_; lean_object* v_task_1316_; lean_object* v_caption_1317_; uint8_t v_optional_1318_; lean_object* v_toPure_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___f_1322_; lean_object* v___x_1323_; 
v_toApplicative_1314_ = lean_ctor_get(v_inst_1310_, 0);
lean_inc_ref(v_toApplicative_1314_);
v_toBind_1315_ = lean_ctor_get(v_inst_1310_, 1);
lean_inc(v_toBind_1315_);
lean_dec_ref(v_inst_1310_);
v_task_1316_ = lean_ctor_get(v_self_1313_, 0);
lean_inc_ref(v_task_1316_);
v_caption_1317_ = lean_ctor_get(v_self_1313_, 2);
lean_inc_ref(v_caption_1317_);
v_optional_1318_ = lean_ctor_get_uint8(v_self_1313_, sizeof(void*)*3);
lean_dec_ref(v_self_1313_);
v_toPure_1319_ = lean_ctor_get(v_toApplicative_1314_, 1);
lean_inc(v_toPure_1319_);
lean_dec_ref(v_toApplicative_1314_);
v___x_1320_ = lean_apply_1(v_f_1312_, v_task_1316_);
v___x_1321_ = lean_box(v_optional_1318_);
v___f_1322_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1322_, 0, v_inst_1311_);
lean_closure_set(v___f_1322_, 1, v_caption_1317_);
lean_closure_set(v___f_1322_, 2, v___x_1321_);
lean_closure_set(v___f_1322_, 3, v_toPure_1319_);
v___x_1323_ = lean_apply_4(v_toBind_1315_, lean_box(0), lean_box(0), v___x_1320_, v___f_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Job_sync_spec__0(lean_object* v_msg_1325_){
_start:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
v___x_1326_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_1327_ = lean_panic_fn_borrowed(v___x_1326_, v_msg_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0(lean_object* v_val_1328_, lean_object* v_val_1329_, lean_object* v_a_x3f_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1333_ = lean_get_set_stdout(v_val_1328_);
lean_dec_ref(v___x_1333_);
v___x_1334_ = lean_get_set_stderr(v_val_1329_);
lean_dec_ref(v___x_1334_);
v___x_1335_ = lean_box(0);
v___x_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v___y_1331_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0___boxed(lean_object* v_val_1337_, lean_object* v_val_1338_, lean_object* v_a_x3f_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lake_Job_sync___redArg___lam__0(v_val_1337_, v_val_1338_, v_a_x3f_1339_, v___y_1340_);
lean_dec(v_a_x3f_1339_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1(lean_object* v_a_1343_, lean_object* v_____r_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1343_);
lean_ctor_set(v___x_1352_, 1, v___y_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1___boxed(lean_object* v_a_1353_, lean_object* v_____r_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Lake_Job_sync___redArg___lam__1(v_a_1353_, v_____r_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1362_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__0(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = l_ByteArray_empty;
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v___x_1363_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__2(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; uint8_t v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1370_ = 0;
v___x_1371_ = 0;
v___x_1372_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1373_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
lean_ctor_set(v___x_1373_, 1, v___x_1369_);
lean_ctor_set(v___x_1373_, 2, v___x_1368_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3, v___x_1371_);
lean_ctor_set_uint8(v___x_1373_, sizeof(void*)*3 + 1, v___x_1370_);
return v___x_1373_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__7(void){
_start:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1378_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__6));
v___x_1379_ = lean_unsigned_to_nat(46u);
v___x_1380_ = lean_unsigned_to_nat(193u);
v___x_1381_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__5));
v___x_1382_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__4));
v___x_1383_ = l_mkPanicMessageWithDecl(v___x_1382_, v___x_1381_, v___x_1380_, v___x_1379_, v___x_1378_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg(lean_object* v_inst_1384_, lean_object* v_act_1385_, lean_object* v_caption_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_, lean_object* v_a_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_){
_start:
{
lean_object* v_val_1394_; lean_object* v___y_1399_; lean_object* v_a_1401_; lean_object* v_a_1402_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
v___x_1405_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1406_ = lean_st_mk_ref(v___x_1405_);
lean_inc(v___x_1406_);
v___x_1407_ = l_IO_FS_Stream_ofBuffer(v___x_1406_);
lean_inc_ref(v___x_1407_);
v___x_1408_ = lean_get_set_stdout(v___x_1407_);
v___x_1409_ = lean_get_set_stderr(v___x_1407_);
v___x_1410_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__2, &l_Lake_Job_sync___redArg___closed__2_once, _init_l_Lake_Job_sync___redArg___closed__2);
lean_inc_ref(v_a_1391_);
lean_inc(v_a_1390_);
lean_inc(v_a_1389_);
lean_inc(v_a_1388_);
lean_inc_ref(v_a_1387_);
v___x_1411_ = lean_apply_7(v_act_1385_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v___x_1410_, lean_box(0));
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v_a_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_a_1416_; lean_object* v___x_1417_; lean_object* v_log_1418_; uint8_t v_action_1419_; uint8_t v_wantsRebuild_1420_; lean_object* v_trace_1421_; lean_object* v_buildTime_1422_; lean_object* v_data_1423_; lean_object* v___y_1425_; uint8_t v___x_1450_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc_n(v_a_1412_, 2);
v_a_1413_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1411_, 2);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_a_1412_);
v___x_1415_ = l_Lake_Job_sync___redArg___lam__0(v___x_1408_, v___x_1409_, v___x_1414_, v_a_1413_);
lean_dec_ref_known(v___x_1414_, 1);
v_a_1416_ = lean_ctor_get(v___x_1415_, 1);
lean_inc(v_a_1416_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = lean_st_ref_get(v___x_1406_);
lean_dec(v___x_1406_);
v_log_1418_ = lean_ctor_get(v_a_1416_, 0);
v_action_1419_ = lean_ctor_get_uint8(v_a_1416_, sizeof(void*)*3);
v_wantsRebuild_1420_ = lean_ctor_get_uint8(v_a_1416_, sizeof(void*)*3 + 1);
v_trace_1421_ = lean_ctor_get(v_a_1416_, 1);
v_buildTime_1422_ = lean_ctor_get(v_a_1416_, 2);
v_data_1423_ = lean_ctor_get(v___x_1417_, 0);
lean_inc_ref(v_data_1423_);
lean_dec(v___x_1417_);
v___x_1450_ = lean_string_validate_utf8(v_data_1423_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec_ref(v_data_1423_);
v___x_1451_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1452_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1451_);
v___y_1425_ = v___x_1452_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1453_; 
v___x_1453_ = lean_string_from_utf8_unchecked(v_data_1423_);
v___y_1425_ = v___x_1453_;
goto v___jp_1424_;
}
v___jp_1424_:
{
lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = lean_string_utf8_byte_size(v___y_1425_);
v___x_1427_ = lean_nat_dec_eq(v___x_1426_, v___x_1404_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1444_; 
lean_inc(v_buildTime_1422_);
lean_inc_ref(v_trace_1421_);
lean_inc_ref(v_log_1418_);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_a_1416_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; lean_object* v_unused_1446_; lean_object* v_unused_1447_; 
v_unused_1445_ = lean_ctor_get(v_a_1416_, 2);
lean_dec(v_unused_1445_);
v_unused_1446_ = lean_ctor_get(v_a_1416_, 1);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_a_1416_, 0);
lean_dec(v_unused_1447_);
v___x_1429_ = v_a_1416_;
v_isShared_1430_ = v_isSharedCheck_1444_;
goto v_resetjp_1428_;
}
else
{
lean_dec(v_a_1416_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1444_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1441_; 
v___x_1431_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1432_, 0, v___y_1425_);
lean_ctor_set(v___x_1432_, 1, v___x_1404_);
lean_ctor_set(v___x_1432_, 2, v___x_1426_);
v___x_1433_ = l_String_Slice_trimAscii(v___x_1432_);
v___x_1434_ = l_String_Slice_toString(v___x_1433_);
lean_dec_ref(v___x_1433_);
v___x_1435_ = lean_string_append(v___x_1431_, v___x_1434_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = 1;
v___x_1437_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set_uint8(v___x_1437_, sizeof(void*)*1, v___x_1436_);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_array_push(v_log_1418_, v___x_1437_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set(v___x_1429_, 0, v___x_1439_);
v___x_1441_ = v___x_1429_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1439_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_trace_1421_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_buildTime_1422_);
lean_ctor_set_uint8(v_reuseFailAlloc_1443_, sizeof(void*)*3, v_action_1419_);
lean_ctor_set_uint8(v_reuseFailAlloc_1443_, sizeof(void*)*3 + 1, v_wantsRebuild_1420_);
v___x_1441_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lake_Job_sync___redArg___lam__1(v_a_1412_, v___x_1438_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v___x_1441_);
lean_dec_ref(v_a_1387_);
v___y_1399_ = v___x_1442_;
goto v___jp_1398_;
}
}
}
else
{
lean_object* v___x_1448_; lean_object* v___x_1449_; 
lean_dec_ref(v___y_1425_);
v___x_1448_ = lean_box(0);
v___x_1449_ = l_Lake_Job_sync___redArg___lam__1(v_a_1412_, v___x_1448_, v_a_1387_, v_a_1388_, v_a_1389_, v_a_1390_, v_a_1391_, v_a_1416_);
lean_dec_ref(v_a_1387_);
v___y_1399_ = v___x_1449_;
goto v___jp_1398_;
}
}
}
else
{
lean_object* v_a_1454_; lean_object* v_a_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v_a_1458_; 
lean_dec(v___x_1406_);
lean_dec_ref(v_a_1387_);
v_a_1454_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1454_);
v_a_1455_ = lean_ctor_get(v___x_1411_, 1);
lean_inc(v_a_1455_);
lean_dec_ref_known(v___x_1411_, 2);
v___x_1456_ = lean_box(0);
v___x_1457_ = l_Lake_Job_sync___redArg___lam__0(v___x_1408_, v___x_1409_, v___x_1456_, v_a_1455_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 1);
lean_inc(v_a_1458_);
lean_dec_ref(v___x_1457_);
v_a_1401_ = v_a_1454_;
v_a_1402_ = v_a_1458_;
goto v___jp_1400_;
}
v___jp_1393_:
{
lean_object* v___x_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; 
v___x_1395_ = lean_task_pure(v_val_1394_);
v___x_1396_ = 0;
v___x_1397_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1397_, 0, v___x_1395_);
lean_ctor_set(v___x_1397_, 1, v_inst_1384_);
lean_ctor_set(v___x_1397_, 2, v_caption_1386_);
lean_ctor_set_uint8(v___x_1397_, sizeof(void*)*3, v___x_1396_);
return v___x_1397_;
}
v___jp_1398_:
{
v_val_1394_ = v___y_1399_;
goto v___jp_1393_;
}
v___jp_1400_:
{
lean_object* v___x_1403_; 
v___x_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_a_1401_);
lean_ctor_set(v___x_1403_, 1, v_a_1402_);
v_val_1394_ = v___x_1403_;
goto v___jp_1393_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___boxed(lean_object* v_inst_1459_, lean_object* v_act_1460_, lean_object* v_caption_1461_, lean_object* v_a_1462_, lean_object* v_a_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_){
_start:
{
lean_object* v_res_1468_; 
v_res_1468_ = l_Lake_Job_sync___redArg(v_inst_1459_, v_act_1460_, v_caption_1461_, v_a_1462_, v_a_1463_, v_a_1464_, v_a_1465_, v_a_1466_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec(v_a_1464_);
lean_dec(v_a_1463_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync(lean_object* v_00_u03b1_1469_, lean_object* v_inst_1470_, lean_object* v_act_1471_, lean_object* v_caption_1472_, lean_object* v_a_1473_, lean_object* v_a_1474_, lean_object* v_a_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_, lean_object* v_a_1478_){
_start:
{
lean_object* v___x_1480_; 
v___x_1480_ = l_Lake_Job_sync___redArg(v_inst_1470_, v_act_1471_, v_caption_1472_, v_a_1473_, v_a_1474_, v_a_1475_, v_a_1476_, v_a_1477_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___boxed(lean_object* v_00_u03b1_1481_, lean_object* v_inst_1482_, lean_object* v_act_1483_, lean_object* v_caption_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lake_Job_sync(v_00_u03b1_1481_, v_inst_1482_, v_act_1483_, v_caption_1484_, v_a_1485_, v_a_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec_ref(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec(v_a_1487_);
lean_dec(v_a_1486_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1(lean_object* v___x_1493_, lean_object* v___x_1494_, uint8_t v___x_1495_, uint8_t v___x_1496_, lean_object* v___x_1497_, lean_object* v___x_1498_, lean_object* v_act_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v_a_1507_; lean_object* v_a_1508_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1510_ = lean_st_mk_ref(v___x_1493_);
lean_inc(v___x_1510_);
v___x_1511_ = l_IO_FS_Stream_ofBuffer(v___x_1510_);
lean_inc_ref(v___x_1511_);
v___x_1512_ = lean_get_set_stdout(v___x_1511_);
v___x_1513_ = lean_get_set_stderr(v___x_1511_);
lean_inc(v___x_1498_);
v___x_1514_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1514_, 0, v___x_1494_);
lean_ctor_set(v___x_1514_, 1, v___x_1497_);
lean_ctor_set(v___x_1514_, 2, v___x_1498_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*3, v___x_1495_);
lean_ctor_set_uint8(v___x_1514_, sizeof(void*)*3 + 1, v___x_1496_);
lean_inc_ref(v_a_1504_);
lean_inc(v_a_1503_);
lean_inc(v_a_1502_);
lean_inc(v_a_1501_);
v___x_1515_ = lean_apply_7(v_act_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v___x_1514_, lean_box(0));
if (lean_obj_tag(v___x_1515_) == 0)
{
lean_object* v_a_1516_; lean_object* v_a_1517_; lean_object* v___x_1519_; uint8_t v_isShared_1520_; uint8_t v_isSharedCheck_1562_; 
v_a_1516_ = lean_ctor_get(v___x_1515_, 0);
v_a_1517_ = lean_ctor_get(v___x_1515_, 1);
v_isSharedCheck_1562_ = !lean_is_exclusive(v___x_1515_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1519_ = v___x_1515_;
v_isShared_1520_ = v_isSharedCheck_1562_;
goto v_resetjp_1518_;
}
else
{
lean_inc(v_a_1517_);
lean_inc(v_a_1516_);
lean_dec(v___x_1515_);
v___x_1519_ = lean_box(0);
v_isShared_1520_ = v_isSharedCheck_1562_;
goto v_resetjp_1518_;
}
v_resetjp_1518_:
{
lean_object* v___y_1522_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v_a_1528_; lean_object* v___x_1529_; lean_object* v_log_1530_; uint8_t v_action_1531_; uint8_t v_wantsRebuild_1532_; lean_object* v_trace_1533_; lean_object* v_buildTime_1534_; lean_object* v___y_1536_; lean_object* v_data_1557_; uint8_t v___x_1558_; 
lean_inc(v_a_1516_);
v___x_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_a_1516_);
v___x_1527_ = l_Lake_Job_sync___redArg___lam__0(v___x_1512_, v___x_1513_, v___x_1526_, v_a_1517_);
lean_dec_ref_known(v___x_1526_, 1);
v_a_1528_ = lean_ctor_get(v___x_1527_, 1);
lean_inc(v_a_1528_);
lean_dec_ref(v___x_1527_);
v___x_1529_ = lean_st_ref_get(v___x_1510_);
lean_dec(v___x_1510_);
v_log_1530_ = lean_ctor_get(v_a_1528_, 0);
v_action_1531_ = lean_ctor_get_uint8(v_a_1528_, sizeof(void*)*3);
v_wantsRebuild_1532_ = lean_ctor_get_uint8(v_a_1528_, sizeof(void*)*3 + 1);
v_trace_1533_ = lean_ctor_get(v_a_1528_, 1);
v_buildTime_1534_ = lean_ctor_get(v_a_1528_, 2);
v_data_1557_ = lean_ctor_get(v___x_1529_, 0);
lean_inc_ref(v_data_1557_);
lean_dec(v___x_1529_);
v___x_1558_ = lean_string_validate_utf8(v_data_1557_);
if (v___x_1558_ == 0)
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
lean_dec_ref(v_data_1557_);
v___x_1559_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1560_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1559_);
v___y_1536_ = v___x_1560_;
goto v___jp_1535_;
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_string_from_utf8_unchecked(v_data_1557_);
v___y_1536_ = v___x_1561_;
goto v___jp_1535_;
}
v___jp_1521_:
{
lean_object* v___x_1524_; 
if (v_isShared_1520_ == 0)
{
lean_ctor_set(v___x_1519_, 1, v___y_1522_);
v___x_1524_ = v___x_1519_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1516_);
lean_ctor_set(v_reuseFailAlloc_1525_, 1, v___y_1522_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
v___jp_1535_:
{
lean_object* v___x_1537_; uint8_t v___x_1538_; 
v___x_1537_ = lean_string_utf8_byte_size(v___y_1536_);
v___x_1538_ = lean_nat_dec_eq(v___x_1537_, v___x_1498_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1553_; 
lean_inc(v_buildTime_1534_);
lean_inc_ref(v_trace_1533_);
lean_inc_ref(v_log_1530_);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_a_1528_);
if (v_isSharedCheck_1553_ == 0)
{
lean_object* v_unused_1554_; lean_object* v_unused_1555_; lean_object* v_unused_1556_; 
v_unused_1554_ = lean_ctor_get(v_a_1528_, 2);
lean_dec(v_unused_1554_);
v_unused_1555_ = lean_ctor_get(v_a_1528_, 1);
lean_dec(v_unused_1555_);
v_unused_1556_ = lean_ctor_get(v_a_1528_, 0);
lean_dec(v_unused_1556_);
v___x_1540_ = v_a_1528_;
v_isShared_1541_ = v_isSharedCheck_1553_;
goto v_resetjp_1539_;
}
else
{
lean_dec(v_a_1528_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1553_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1542_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1543_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1543_, 0, v___y_1536_);
lean_ctor_set(v___x_1543_, 1, v___x_1498_);
lean_ctor_set(v___x_1543_, 2, v___x_1537_);
v___x_1544_ = l_String_Slice_trimAscii(v___x_1543_);
v___x_1545_ = l_String_Slice_toString(v___x_1544_);
lean_dec_ref(v___x_1544_);
v___x_1546_ = lean_string_append(v___x_1542_, v___x_1545_);
lean_dec_ref(v___x_1545_);
v___x_1547_ = 1;
v___x_1548_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1548_, 0, v___x_1546_);
lean_ctor_set_uint8(v___x_1548_, sizeof(void*)*1, v___x_1547_);
v___x_1549_ = lean_array_push(v_log_1530_, v___x_1548_);
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 0, v___x_1549_);
v___x_1551_ = v___x_1540_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_trace_1533_);
lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_buildTime_1534_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*3, v_action_1531_);
lean_ctor_set_uint8(v_reuseFailAlloc_1552_, sizeof(void*)*3 + 1, v_wantsRebuild_1532_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
v___y_1522_ = v___x_1551_;
goto v___jp_1521_;
}
}
}
else
{
lean_dec_ref(v___y_1536_);
lean_dec(v___x_1498_);
v___y_1522_ = v_a_1528_;
goto v___jp_1521_;
}
}
}
}
else
{
lean_object* v_a_1563_; lean_object* v_a_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v_a_1567_; 
lean_dec(v___x_1510_);
lean_dec(v___x_1498_);
v_a_1563_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_a_1563_);
v_a_1564_ = lean_ctor_get(v___x_1515_, 1);
lean_inc(v_a_1564_);
lean_dec_ref_known(v___x_1515_, 2);
v___x_1565_ = lean_box(0);
v___x_1566_ = l_Lake_Job_sync___redArg___lam__0(v___x_1512_, v___x_1513_, v___x_1565_, v_a_1564_);
v_a_1567_ = lean_ctor_get(v___x_1566_, 1);
lean_inc(v_a_1567_);
lean_dec_ref(v___x_1566_);
v_a_1507_ = v_a_1563_;
v_a_1508_ = v_a_1567_;
goto v___jp_1506_;
}
v___jp_1506_:
{
lean_object* v___x_1509_; 
v___x_1509_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1509_, 0, v_a_1507_);
lean_ctor_set(v___x_1509_, 1, v_a_1508_);
return v___x_1509_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1___boxed(lean_object* v___x_1568_, lean_object* v___x_1569_, lean_object* v___x_1570_, lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v___x_1573_, lean_object* v_act_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v___y_1580_){
_start:
{
uint8_t v___x_22707__boxed_1581_; uint8_t v___x_22708__boxed_1582_; lean_object* v_res_1583_; 
v___x_22707__boxed_1581_ = lean_unbox(v___x_1570_);
v___x_22708__boxed_1582_ = lean_unbox(v___x_1571_);
v_res_1583_ = l_Lake_Job_async___redArg___lam__1(v___x_1568_, v___x_1569_, v___x_22707__boxed_1581_, v___x_22708__boxed_1582_, v___x_1572_, v___x_1573_, v_act_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
lean_dec_ref(v_a_1579_);
lean_dec(v_a_1578_);
lean_dec(v_a_1577_);
lean_dec(v_a_1576_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg(lean_object* v_inst_1584_, lean_object* v_act_1585_, lean_object* v_prio_1586_, lean_object* v_caption_1587_, lean_object* v_a_1588_, lean_object* v_a_1589_, lean_object* v_a_1590_, lean_object* v_a_1591_, lean_object* v_a_1592_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; uint8_t v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___f_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1596_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1597_ = 0;
v___x_1598_ = 0;
v___x_1599_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1600_ = lean_box(v___x_1597_);
v___x_1601_ = lean_box(v___x_1598_);
lean_inc_ref(v_a_1592_);
lean_inc(v_a_1591_);
lean_inc(v_a_1590_);
lean_inc(v_a_1589_);
v___f_1602_ = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__1___boxed), 13, 12);
lean_closure_set(v___f_1602_, 0, v___x_1595_);
lean_closure_set(v___f_1602_, 1, v___x_1596_);
lean_closure_set(v___f_1602_, 2, v___x_1600_);
lean_closure_set(v___f_1602_, 3, v___x_1601_);
lean_closure_set(v___f_1602_, 4, v___x_1599_);
lean_closure_set(v___f_1602_, 5, v___x_1594_);
lean_closure_set(v___f_1602_, 6, v_act_1585_);
lean_closure_set(v___f_1602_, 7, v_a_1588_);
lean_closure_set(v___f_1602_, 8, v_a_1589_);
lean_closure_set(v___f_1602_, 9, v_a_1590_);
lean_closure_set(v___f_1602_, 10, v_a_1591_);
lean_closure_set(v___f_1602_, 11, v_a_1592_);
v___x_1603_ = lean_io_as_task(v___f_1602_, v_prio_1586_);
v___x_1604_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
lean_ctor_set(v___x_1604_, 1, v_inst_1584_);
lean_ctor_set(v___x_1604_, 2, v_caption_1587_);
lean_ctor_set_uint8(v___x_1604_, sizeof(void*)*3, v___x_1598_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___boxed(lean_object* v_inst_1605_, lean_object* v_act_1606_, lean_object* v_prio_1607_, lean_object* v_caption_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Lake_Job_async___redArg(v_inst_1605_, v_act_1606_, v_prio_1607_, v_caption_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_);
lean_dec_ref(v_a_1613_);
lean_dec(v_a_1612_);
lean_dec(v_a_1611_);
lean_dec(v_a_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async(lean_object* v_00_u03b1_1616_, lean_object* v_inst_1617_, lean_object* v_act_1618_, lean_object* v_prio_1619_, lean_object* v_caption_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lake_Job_async___redArg(v_inst_1617_, v_act_1618_, v_prio_1619_, v_caption_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___boxed(lean_object* v_00_u03b1_1629_, lean_object* v_inst_1630_, lean_object* v_act_1631_, lean_object* v_prio_1632_, lean_object* v_caption_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lake_Job_async(v_00_u03b1_1629_, v_inst_1630_, v_act_1631_, v_prio_1632_, v_caption_1633_, v_a_1634_, v_a_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_);
lean_dec_ref(v_a_1639_);
lean_dec_ref(v_a_1638_);
lean_dec(v_a_1637_);
lean_dec(v_a_1636_);
lean_dec(v_a_1635_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg(lean_object* v_self_1642_){
_start:
{
lean_object* v_task_1644_; lean_object* v___x_1645_; 
v_task_1644_ = lean_ctor_get(v_self_1642_, 0);
lean_inc_ref(v_task_1644_);
lean_dec_ref(v_self_1642_);
v___x_1645_ = lean_io_wait(v_task_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg___boxed(lean_object* v_self_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Lake_Job_wait___redArg(v_self_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait(lean_object* v_00_u03b1_1649_, lean_object* v_self_1650_){
_start:
{
lean_object* v_task_1652_; lean_object* v___x_1653_; 
v_task_1652_ = lean_ctor_get(v_self_1650_, 0);
lean_inc_ref(v_task_1652_);
lean_dec_ref(v_self_1650_);
v___x_1653_ = lean_io_wait(v_task_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___boxed(lean_object* v_00_u03b1_1654_, lean_object* v_self_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l_Lake_Job_wait(v_00_u03b1_1654_, v_self_1655_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg(lean_object* v_self_1658_){
_start:
{
lean_object* v_task_1660_; lean_object* v___x_1661_; 
v_task_1660_ = lean_ctor_get(v_self_1658_, 0);
lean_inc_ref(v_task_1660_);
lean_dec_ref(v_self_1658_);
v___x_1661_ = lean_io_wait(v_task_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_object* v_a_1662_; lean_object* v___x_1663_; 
v_a_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_a_1662_);
lean_dec_ref_known(v___x_1661_, 2);
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_a_1662_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; 
lean_dec_ref_known(v___x_1661_, 2);
v___x_1664_ = lean_box(0);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg___boxed(lean_object* v_self_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_Lake_Job_wait_x3f___redArg(v_self_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f(lean_object* v_00_u03b1_1668_, lean_object* v_self_1669_){
_start:
{
lean_object* v_task_1671_; lean_object* v___x_1672_; 
v_task_1671_ = lean_ctor_get(v_self_1669_, 0);
lean_inc_ref(v_task_1671_);
lean_dec_ref(v_self_1669_);
v___x_1672_ = lean_io_wait(v_task_1671_);
if (lean_obj_tag(v___x_1672_) == 0)
{
lean_object* v_a_1673_; lean_object* v___x_1674_; 
v_a_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_a_1673_);
lean_dec_ref_known(v___x_1672_, 2);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_a_1673_);
return v___x_1674_;
}
else
{
lean_object* v___x_1675_; 
lean_dec_ref_known(v___x_1672_, 2);
v___x_1675_ = lean_box(0);
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___boxed(lean_object* v_00_u03b1_1676_, lean_object* v_self_1677_, lean_object* v_a_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lake_Job_wait_x3f(v_00_u03b1_1676_, v_self_1677_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(lean_object* v_as_1680_, size_t v_i_1681_, size_t v_stop_1682_, lean_object* v_b_1683_, lean_object* v___y_1684_){
_start:
{
uint8_t v___x_1686_; 
v___x_1686_ = lean_usize_dec_eq(v_i_1681_, v_stop_1682_);
if (v___x_1686_ == 0)
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; size_t v___x_1690_; size_t v___x_1691_; 
v___x_1687_ = lean_array_uget_borrowed(v_as_1680_, v_i_1681_);
v___x_1688_ = lean_box(0);
lean_inc(v___x_1687_);
v___x_1689_ = lean_array_push(v___y_1684_, v___x_1687_);
v___x_1690_ = ((size_t)1ULL);
v___x_1691_ = lean_usize_add(v_i_1681_, v___x_1690_);
v_i_1681_ = v___x_1691_;
v_b_1683_ = v___x_1688_;
v___y_1684_ = v___x_1689_;
goto _start;
}
else
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_b_1683_);
lean_ctor_set(v___x_1693_, 1, v___y_1684_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0___boxed(lean_object* v_as_1694_, lean_object* v_i_1695_, lean_object* v_stop_1696_, lean_object* v_b_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_){
_start:
{
size_t v_i_boxed_1700_; size_t v_stop_boxed_1701_; lean_object* v_res_1702_; 
v_i_boxed_1700_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_stop_boxed_1701_ = lean_unbox_usize(v_stop_1696_);
lean_dec(v_stop_1696_);
v_res_1702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_as_1694_, v_i_boxed_1700_, v_stop_boxed_1701_, v_b_1697_, v___y_1698_);
lean_dec_ref(v_as_1694_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg(lean_object* v_self_1703_, lean_object* v_a_1704_){
_start:
{
lean_object* v_task_1706_; lean_object* v___x_1707_; 
v_task_1706_ = lean_ctor_get(v_self_1703_, 0);
lean_inc_ref(v_task_1706_);
lean_dec_ref(v_self_1703_);
v___x_1707_ = lean_io_wait(v_task_1706_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1736_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_a_1709_ = lean_ctor_get(v___x_1707_, 1);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1711_ = v___x_1707_;
v_isShared_1712_ = v_isSharedCheck_1736_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1736_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_a_1714_; lean_object* v_log_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v_log_1718_ = lean_ctor_get(v_a_1709_, 0);
lean_inc_ref(v_log_1718_);
lean_dec(v_a_1709_);
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_array_get_size(v_log_1718_);
v___x_1721_ = lean_nat_dec_lt(v___x_1719_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_dec_ref(v_log_1718_);
v_a_1714_ = v_a_1704_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1722_; size_t v___x_1723_; size_t v___x_1724_; lean_object* v___x_1725_; 
v___x_1722_ = lean_box(0);
v___x_1723_ = ((size_t)0ULL);
v___x_1724_ = lean_usize_of_nat(v___x_1720_);
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1718_, v___x_1723_, v___x_1724_, v___x_1722_, v_a_1704_);
lean_dec_ref(v_log_1718_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 1);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 2);
v_a_1714_ = v_a_1726_;
goto v___jp_1713_;
}
else
{
lean_object* v_a_1727_; lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
lean_del_object(v___x_1711_);
lean_dec(v_a_1708_);
v_a_1727_ = lean_ctor_get(v___x_1725_, 0);
v_a_1728_ = lean_ctor_get(v___x_1725_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1725_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_inc(v_a_1727_);
lean_dec(v___x_1725_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1727_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
v___jp_1713_:
{
lean_object* v___x_1716_; 
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 1, v_a_1714_);
v___x_1716_ = v___x_1711_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v_a_1708_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_a_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1765_; 
v_a_1737_ = lean_ctor_get(v___x_1707_, 0);
v_a_1738_ = lean_ctor_get(v___x_1707_, 1);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1740_ = v___x_1707_;
v_isShared_1741_ = v_isSharedCheck_1765_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_inc(v_a_1737_);
lean_dec(v___x_1707_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1765_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v_a_1743_; lean_object* v_log_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_log_1747_ = lean_ctor_get(v_a_1738_, 0);
lean_inc_ref(v_log_1747_);
lean_dec(v_a_1738_);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = lean_array_get_size(v_log_1747_);
v___x_1750_ = lean_nat_dec_lt(v___x_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec_ref(v_log_1747_);
v_a_1743_ = v_a_1704_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1751_; size_t v___x_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = lean_usize_of_nat(v___x_1749_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1747_, v___x_1752_, v___x_1753_, v___x_1751_, v_a_1704_);
lean_dec_ref(v_log_1747_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 1);
lean_inc(v_a_1755_);
lean_dec_ref_known(v___x_1754_, 2);
v_a_1743_ = v_a_1755_;
goto v___jp_1742_;
}
else
{
lean_object* v_a_1756_; lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_del_object(v___x_1740_);
lean_dec(v_a_1737_);
v_a_1756_ = lean_ctor_get(v___x_1754_, 0);
v_a_1757_ = lean_ctor_get(v___x_1754_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1754_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_inc(v_a_1756_);
lean_dec(v___x_1754_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1756_);
lean_ctor_set(v_reuseFailAlloc_1763_, 1, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
v___jp_1742_:
{
lean_object* v___x_1745_; 
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 1, v_a_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1737_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_a_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___boxed(lean_object* v_self_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Lake_Job_await___redArg(v_self_1766_, v_a_1767_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await(lean_object* v_00_u03b1_1770_, lean_object* v_self_1771_, lean_object* v_a_1772_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_Lake_Job_await___redArg(v_self_1771_, v_a_1772_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___boxed(lean_object* v_00_u03b1_1775_, lean_object* v_self_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_){
_start:
{
lean_object* v_res_1779_; 
v_res_1779_ = l_Lake_Job_await(v_00_u03b1_1775_, v_self_1776_, v_a_1777_);
return v_res_1779_;
}
}
static lean_object* _init_l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0(void){
_start:
{
lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = l_Lake_cancelMessage;
v___x_1781_ = 0;
v___x_1782_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1782_, 0, v___x_1780_);
lean_ctor_set_uint8(v___x_1782_, sizeof(void*)*1, v___x_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg(lean_object* v_s_1783_){
_start:
{
lean_object* v_log_1784_; uint8_t v_action_1785_; uint8_t v_wantsRebuild_1786_; lean_object* v_trace_1787_; lean_object* v_buildTime_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1799_; 
v_log_1784_ = lean_ctor_get(v_s_1783_, 0);
v_action_1785_ = lean_ctor_get_uint8(v_s_1783_, sizeof(void*)*3);
v_wantsRebuild_1786_ = lean_ctor_get_uint8(v_s_1783_, sizeof(void*)*3 + 1);
v_trace_1787_ = lean_ctor_get(v_s_1783_, 1);
v_buildTime_1788_ = lean_ctor_get(v_s_1783_, 2);
v_isSharedCheck_1799_ = !lean_is_exclusive(v_s_1783_);
if (v_isSharedCheck_1799_ == 0)
{
v___x_1790_ = v_s_1783_;
v_isShared_1791_ = v_isSharedCheck_1799_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_buildTime_1788_);
lean_inc(v_trace_1787_);
lean_inc(v_log_1784_);
lean_dec(v_s_1783_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1799_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1796_; 
v___x_1792_ = lean_array_get_size(v_log_1784_);
v___x_1793_ = lean_obj_once(&l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0, &l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0_once, _init_l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0);
v___x_1794_ = lean_array_push(v_log_1784_, v___x_1793_);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1794_);
v___x_1796_ = v___x_1790_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v___x_1794_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_trace_1787_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_buildTime_1788_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*3, v_action_1785_);
lean_ctor_set_uint8(v_reuseFailAlloc_1798_, sizeof(void*)*3 + 1, v_wantsRebuild_1786_);
v___x_1796_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1792_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult(lean_object* v_00_u03b1_1800_, lean_object* v_s_1801_){
_start:
{
lean_object* v_log_1802_; uint8_t v_action_1803_; uint8_t v_wantsRebuild_1804_; lean_object* v_trace_1805_; lean_object* v_buildTime_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1817_; 
v_log_1802_ = lean_ctor_get(v_s_1801_, 0);
v_action_1803_ = lean_ctor_get_uint8(v_s_1801_, sizeof(void*)*3);
v_wantsRebuild_1804_ = lean_ctor_get_uint8(v_s_1801_, sizeof(void*)*3 + 1);
v_trace_1805_ = lean_ctor_get(v_s_1801_, 1);
v_buildTime_1806_ = lean_ctor_get(v_s_1801_, 2);
v_isSharedCheck_1817_ = !lean_is_exclusive(v_s_1801_);
if (v_isSharedCheck_1817_ == 0)
{
v___x_1808_ = v_s_1801_;
v_isShared_1809_ = v_isSharedCheck_1817_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_buildTime_1806_);
lean_inc(v_trace_1805_);
lean_inc(v_log_1802_);
lean_dec(v_s_1801_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1817_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1810_ = lean_array_get_size(v_log_1802_);
v___x_1811_ = lean_obj_once(&l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0, &l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0_once, _init_l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0);
v___x_1812_ = lean_array_push(v_log_1802_, v___x_1811_);
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 0, v___x_1812_);
v___x_1814_ = v___x_1808_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1816_, 1, v_trace_1805_);
lean_ctor_set(v_reuseFailAlloc_1816_, 2, v_buildTime_1806_);
lean_ctor_set_uint8(v_reuseFailAlloc_1816_, sizeof(void*)*3, v_action_1803_);
lean_ctor_set_uint8(v_reuseFailAlloc_1816_, sizeof(void*)*3 + 1, v_wantsRebuild_1804_);
v___x_1814_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1815_, 0, v___x_1810_);
lean_ctor_set(v___x_1815_, 1, v___x_1814_);
return v___x_1815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1(lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_f_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_x_1825_){
_start:
{
lean_object* v_a_1828_; lean_object* v_a_1829_; lean_object* v___y_1832_; lean_object* v___y_1833_; lean_object* v___y_1836_; uint8_t v___y_1837_; lean_object* v___y_1838_; uint8_t v___y_1839_; lean_object* v___y_1840_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; 
if (lean_obj_tag(v_x_1825_) == 0)
{
lean_object* v_a_1856_; lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1924_; 
v_a_1856_ = lean_ctor_get(v_x_1825_, 0);
v_a_1857_ = lean_ctor_get(v_x_1825_, 1);
v_isSharedCheck_1924_ = !lean_is_exclusive(v_x_1825_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1859_ = v_x_1825_;
v_isShared_1860_ = v_isSharedCheck_1924_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_inc(v_a_1856_);
lean_dec(v_x_1825_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1924_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_cancelTk_x3f_1903_; 
v_cancelTk_x3f_1903_ = lean_ctor_get(v_a_1818_, 6);
if (lean_obj_tag(v_cancelTk_x3f_1903_) == 1)
{
lean_object* v_val_1904_; uint8_t v___x_1905_; 
v_val_1904_ = lean_ctor_get(v_cancelTk_x3f_1903_, 0);
v___x_1905_ = l_IO_CancelToken_isSet(v_val_1904_);
if (v___x_1905_ == 0)
{
lean_del_object(v___x_1859_);
goto v___jp_1861_;
}
else
{
lean_object* v_log_1906_; uint8_t v_action_1907_; uint8_t v_wantsRebuild_1908_; lean_object* v_trace_1909_; lean_object* v_buildTime_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1923_; 
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1821_);
lean_dec_ref(v_f_1820_);
v_log_1906_ = lean_ctor_get(v_a_1857_, 0);
v_action_1907_ = lean_ctor_get_uint8(v_a_1857_, sizeof(void*)*3);
v_wantsRebuild_1908_ = lean_ctor_get_uint8(v_a_1857_, sizeof(void*)*3 + 1);
v_trace_1909_ = lean_ctor_get(v_a_1857_, 1);
v_buildTime_1910_ = lean_ctor_get(v_a_1857_, 2);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_a_1857_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1912_ = v_a_1857_;
v_isShared_1913_ = v_isSharedCheck_1923_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_buildTime_1910_);
lean_inc(v_trace_1909_);
lean_inc(v_log_1906_);
lean_dec(v_a_1857_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1923_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1914_ = lean_array_get_size(v_log_1906_);
v___x_1915_ = lean_obj_once(&l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0, &l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0_once, _init_l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0);
v___x_1916_ = lean_array_push(v_log_1906_, v___x_1915_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 0, v___x_1916_);
v___x_1918_ = v___x_1912_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1916_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_trace_1909_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_buildTime_1910_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*3, v_action_1907_);
lean_ctor_set_uint8(v_reuseFailAlloc_1922_, sizeof(void*)*3 + 1, v_wantsRebuild_1908_);
v___x_1918_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set_tag(v___x_1859_, 1);
lean_ctor_set(v___x_1859_, 1, v___x_1918_);
lean_ctor_set(v___x_1859_, 0, v___x_1914_);
v___x_1920_ = v___x_1859_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
else
{
lean_del_object(v___x_1859_);
goto v___jp_1861_;
}
v___jp_1861_:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v_log_1868_; uint8_t v_action_1869_; uint8_t v_wantsRebuild_1870_; lean_object* v_trace_1871_; lean_object* v_buildTime_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1902_; 
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1864_ = lean_st_mk_ref(v___x_1863_);
lean_inc(v___x_1864_);
v___x_1865_ = l_IO_FS_Stream_ofBuffer(v___x_1864_);
lean_inc_ref(v___x_1865_);
v___x_1866_ = lean_get_set_stdout(v___x_1865_);
v___x_1867_ = lean_get_set_stderr(v___x_1865_);
v_log_1868_ = lean_ctor_get(v_a_1857_, 0);
v_action_1869_ = lean_ctor_get_uint8(v_a_1857_, sizeof(void*)*3);
v_wantsRebuild_1870_ = lean_ctor_get_uint8(v_a_1857_, sizeof(void*)*3 + 1);
v_trace_1871_ = lean_ctor_get(v_a_1857_, 1);
v_buildTime_1872_ = lean_ctor_get(v_a_1857_, 2);
v_isSharedCheck_1902_ = !lean_is_exclusive(v_a_1857_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1874_ = v_a_1857_;
v_isShared_1875_ = v_isSharedCheck_1902_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_buildTime_1872_);
lean_inc(v_trace_1871_);
lean_inc(v_log_1868_);
lean_dec(v_a_1857_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1902_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v_trace_1876_; lean_object* v___x_1878_; 
lean_inc_ref(v_a_1819_);
v_trace_1876_ = l_Lake_BuildTrace_mix(v_a_1819_, v_trace_1871_);
if (v_isShared_1875_ == 0)
{
lean_ctor_set(v___x_1874_, 1, v_trace_1876_);
v___x_1878_ = v___x_1874_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_log_1868_);
lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_trace_1876_);
lean_ctor_set(v_reuseFailAlloc_1901_, 2, v_buildTime_1872_);
lean_ctor_set_uint8(v_reuseFailAlloc_1901_, sizeof(void*)*3, v_action_1869_);
lean_ctor_set_uint8(v_reuseFailAlloc_1901_, sizeof(void*)*3 + 1, v_wantsRebuild_1870_);
v___x_1878_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
lean_object* v___x_1879_; 
lean_inc_ref(v_a_1818_);
lean_inc(v_a_1824_);
lean_inc(v_a_1823_);
lean_inc(v_a_1822_);
v___x_1879_ = lean_apply_8(v_f_1820_, v_a_1856_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_, v_a_1818_, v___x_1878_, lean_box(0));
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v_a_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v_a_1884_; lean_object* v___x_1885_; lean_object* v_log_1886_; uint8_t v_action_1887_; uint8_t v_wantsRebuild_1888_; lean_object* v_trace_1889_; lean_object* v_buildTime_1890_; lean_object* v_data_1891_; uint8_t v___x_1892_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc_n(v_a_1880_, 2);
v_a_1881_ = lean_ctor_get(v___x_1879_, 1);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1879_, 2);
v___x_1882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1882_, 0, v_a_1880_);
v___x_1883_ = l_Lake_Job_sync___redArg___lam__0(v___x_1866_, v___x_1867_, v___x_1882_, v_a_1881_);
lean_dec_ref_known(v___x_1882_, 1);
v_a_1884_ = lean_ctor_get(v___x_1883_, 1);
lean_inc(v_a_1884_);
lean_dec_ref(v___x_1883_);
v___x_1885_ = lean_st_ref_get(v___x_1864_);
lean_dec(v___x_1864_);
v_log_1886_ = lean_ctor_get(v_a_1884_, 0);
lean_inc_ref(v_log_1886_);
v_action_1887_ = lean_ctor_get_uint8(v_a_1884_, sizeof(void*)*3);
v_wantsRebuild_1888_ = lean_ctor_get_uint8(v_a_1884_, sizeof(void*)*3 + 1);
v_trace_1889_ = lean_ctor_get(v_a_1884_, 1);
lean_inc_ref(v_trace_1889_);
v_buildTime_1890_ = lean_ctor_get(v_a_1884_, 2);
lean_inc(v_buildTime_1890_);
v_data_1891_ = lean_ctor_get(v___x_1885_, 0);
lean_inc_ref(v_data_1891_);
lean_dec(v___x_1885_);
v___x_1892_ = lean_string_validate_utf8(v_data_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec_ref(v_data_1891_);
v___x_1893_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1894_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1893_);
v___y_1836_ = v_a_1880_;
v___y_1837_ = v_action_1887_;
v___y_1838_ = v___x_1862_;
v___y_1839_ = v_wantsRebuild_1888_;
v___y_1840_ = v_log_1886_;
v___y_1841_ = v_buildTime_1890_;
v___y_1842_ = v_a_1884_;
v___y_1843_ = v_trace_1889_;
v___y_1844_ = v___x_1894_;
goto v___jp_1835_;
}
else
{
lean_object* v___x_1895_; 
v___x_1895_ = lean_string_from_utf8_unchecked(v_data_1891_);
v___y_1836_ = v_a_1880_;
v___y_1837_ = v_action_1887_;
v___y_1838_ = v___x_1862_;
v___y_1839_ = v_wantsRebuild_1888_;
v___y_1840_ = v_log_1886_;
v___y_1841_ = v_buildTime_1890_;
v___y_1842_ = v_a_1884_;
v___y_1843_ = v_trace_1889_;
v___y_1844_ = v___x_1895_;
goto v___jp_1835_;
}
}
else
{
lean_object* v_a_1896_; lean_object* v_a_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v_a_1900_; 
lean_dec(v___x_1864_);
v_a_1896_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1896_);
v_a_1897_ = lean_ctor_get(v___x_1879_, 1);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1879_, 2);
v___x_1898_ = lean_box(0);
v___x_1899_ = l_Lake_Job_sync___redArg___lam__0(v___x_1866_, v___x_1867_, v___x_1898_, v_a_1897_);
v_a_1900_ = lean_ctor_get(v___x_1899_, 1);
lean_inc(v_a_1900_);
lean_dec_ref(v___x_1899_);
v_a_1828_ = v_a_1896_;
v_a_1829_ = v_a_1900_;
goto v___jp_1827_;
}
}
}
}
}
}
else
{
lean_object* v_a_1925_; lean_object* v_a_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1933_; 
lean_dec_ref(v_a_1821_);
lean_dec_ref(v_f_1820_);
v_a_1925_ = lean_ctor_get(v_x_1825_, 0);
v_a_1926_ = lean_ctor_get(v_x_1825_, 1);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_x_1825_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1928_ = v_x_1825_;
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_a_1926_);
lean_inc(v_a_1925_);
lean_dec(v_x_1825_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1933_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1931_; 
if (v_isShared_1929_ == 0)
{
v___x_1931_ = v___x_1928_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1932_; 
v_reuseFailAlloc_1932_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1932_, 0, v_a_1925_);
lean_ctor_set(v_reuseFailAlloc_1932_, 1, v_a_1926_);
v___x_1931_ = v_reuseFailAlloc_1932_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
return v___x_1931_;
}
}
}
v___jp_1827_:
{
lean_object* v___x_1830_; 
v___x_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1830_, 0, v_a_1828_);
lean_ctor_set(v___x_1830_, 1, v_a_1829_);
return v___x_1830_;
}
v___jp_1831_:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___y_1832_);
lean_ctor_set(v___x_1834_, 1, v___y_1833_);
return v___x_1834_;
}
v___jp_1835_:
{
lean_object* v___x_1845_; uint8_t v___x_1846_; 
v___x_1845_ = lean_string_utf8_byte_size(v___y_1844_);
v___x_1846_ = lean_nat_dec_eq(v___x_1845_, v___y_1838_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
lean_dec_ref(v___y_1842_);
v___x_1847_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1848_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1848_, 0, v___y_1844_);
lean_ctor_set(v___x_1848_, 1, v___y_1838_);
lean_ctor_set(v___x_1848_, 2, v___x_1845_);
v___x_1849_ = l_String_Slice_trimAscii(v___x_1848_);
v___x_1850_ = l_String_Slice_toString(v___x_1849_);
lean_dec_ref(v___x_1849_);
v___x_1851_ = lean_string_append(v___x_1847_, v___x_1850_);
lean_dec_ref(v___x_1850_);
v___x_1852_ = 1;
v___x_1853_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set_uint8(v___x_1853_, sizeof(void*)*1, v___x_1852_);
v___x_1854_ = lean_array_push(v___y_1840_, v___x_1853_);
v___x_1855_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v___y_1843_);
lean_ctor_set(v___x_1855_, 2, v___y_1841_);
lean_ctor_set_uint8(v___x_1855_, sizeof(void*)*3, v___y_1837_);
lean_ctor_set_uint8(v___x_1855_, sizeof(void*)*3 + 1, v___y_1839_);
v___y_1832_ = v___y_1836_;
v___y_1833_ = v___x_1855_;
goto v___jp_1831_;
}
else
{
lean_dec_ref(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec(v___y_1838_);
v___y_1832_ = v___y_1836_;
v___y_1833_ = v___y_1842_;
goto v___jp_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1___boxed(lean_object* v_a_1934_, lean_object* v_a_1935_, lean_object* v_f_1936_, lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_x_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lake_Job_mapM___redArg___lam__1(v_a_1934_, v_a_1935_, v_f_1936_, v_a_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_x_1941_);
lean_dec(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec(v_a_1938_);
lean_dec_ref(v_a_1935_);
lean_dec_ref(v_a_1934_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object* v_kind_1944_, lean_object* v_self_1945_, lean_object* v_f_1946_, lean_object* v_prio_1947_, uint8_t v_sync_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v_task_1956_; lean_object* v_caption_1957_; uint8_t v_optional_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_1967_; 
v_task_1956_ = lean_ctor_get(v_self_1945_, 0);
v_caption_1957_ = lean_ctor_get(v_self_1945_, 2);
v_optional_1958_ = lean_ctor_get_uint8(v_self_1945_, sizeof(void*)*3);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_self_1945_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v_self_1945_, 1);
lean_dec(v_unused_1968_);
v___x_1960_ = v_self_1945_;
v_isShared_1961_ = v_isSharedCheck_1967_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_caption_1957_);
lean_inc(v_task_1956_);
lean_dec(v_self_1945_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_1967_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v___f_1962_; lean_object* v___x_1963_; lean_object* v___x_1965_; 
lean_inc(v_a_1952_);
lean_inc(v_a_1951_);
lean_inc(v_a_1950_);
lean_inc_ref(v_a_1954_);
lean_inc_ref(v_a_1953_);
v___f_1962_ = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__1___boxed), 9, 7);
lean_closure_set(v___f_1962_, 0, v_a_1953_);
lean_closure_set(v___f_1962_, 1, v_a_1954_);
lean_closure_set(v___f_1962_, 2, v_f_1946_);
lean_closure_set(v___f_1962_, 3, v_a_1949_);
lean_closure_set(v___f_1962_, 4, v_a_1950_);
lean_closure_set(v___f_1962_, 5, v_a_1951_);
lean_closure_set(v___f_1962_, 6, v_a_1952_);
v___x_1963_ = lean_io_map_task(v___f_1962_, v_task_1956_, v_prio_1947_, v_sync_1948_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v_kind_1944_);
lean_ctor_set(v___x_1960_, 0, v___x_1963_);
v___x_1965_ = v___x_1960_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v___x_1963_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_kind_1944_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_caption_1957_);
lean_ctor_set_uint8(v_reuseFailAlloc_1966_, sizeof(void*)*3, v_optional_1958_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object* v_kind_1969_, lean_object* v_self_1970_, lean_object* v_f_1971_, lean_object* v_prio_1972_, lean_object* v_sync_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_, lean_object* v_a_1980_){
_start:
{
uint8_t v_sync_boxed_1981_; lean_object* v_res_1982_; 
v_sync_boxed_1981_ = lean_unbox(v_sync_1973_);
v_res_1982_ = l_Lake_Job_mapM___redArg(v_kind_1969_, v_self_1970_, v_f_1971_, v_prio_1972_, v_sync_boxed_1981_, v_a_1974_, v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec_ref(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
lean_dec(v_a_1976_);
lean_dec(v_a_1975_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object* v_00_u03b2_1983_, lean_object* v_00_u03b1_1984_, lean_object* v_kind_1985_, lean_object* v_self_1986_, lean_object* v_f_1987_, lean_object* v_prio_1988_, uint8_t v_sync_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_, lean_object* v_a_1993_, lean_object* v_a_1994_, lean_object* v_a_1995_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Lake_Job_mapM___redArg(v_kind_1985_, v_self_1986_, v_f_1987_, v_prio_1988_, v_sync_1989_, v_a_1990_, v_a_1991_, v_a_1992_, v_a_1993_, v_a_1994_, v_a_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object* v_00_u03b2_1998_, lean_object* v_00_u03b1_1999_, lean_object* v_kind_2000_, lean_object* v_self_2001_, lean_object* v_f_2002_, lean_object* v_prio_2003_, lean_object* v_sync_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
uint8_t v_sync_boxed_2012_; lean_object* v_res_2013_; 
v_sync_boxed_2012_ = lean_unbox(v_sync_2004_);
v_res_2013_ = l_Lake_Job_mapM(v_00_u03b2_1998_, v_00_u03b1_1999_, v_kind_2000_, v_self_2001_, v_f_2002_, v_prio_2003_, v_sync_boxed_2012_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
lean_dec_ref(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec(v_a_2006_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object* v_a_2014_, lean_object* v_x_2015_){
_start:
{
if (lean_obj_tag(v_x_2015_) == 0)
{
lean_object* v_a_2016_; lean_object* v_a_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2039_; 
v_a_2016_ = lean_ctor_get(v_x_2015_, 0);
v_a_2017_ = lean_ctor_get(v_x_2015_, 1);
v_isSharedCheck_2039_ = !lean_is_exclusive(v_x_2015_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2019_ = v_x_2015_;
v_isShared_2020_ = v_isSharedCheck_2039_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_a_2017_);
lean_inc(v_a_2016_);
lean_dec(v_x_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2039_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v___x_2021_; lean_object* v_log_2022_; uint8_t v_action_2023_; uint8_t v_wantsRebuild_2024_; lean_object* v_buildTime_2025_; lean_object* v_trace_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2036_; 
lean_inc(v_a_2017_);
v___x_2021_ = l_Lake_JobState_merge(v_a_2014_, v_a_2017_);
v_log_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc_ref(v_log_2022_);
v_action_2023_ = lean_ctor_get_uint8(v___x_2021_, sizeof(void*)*3);
v_wantsRebuild_2024_ = lean_ctor_get_uint8(v___x_2021_, sizeof(void*)*3 + 1);
v_buildTime_2025_ = lean_ctor_get(v___x_2021_, 2);
lean_inc(v_buildTime_2025_);
lean_dec_ref(v___x_2021_);
v_trace_2026_ = lean_ctor_get(v_a_2017_, 1);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_a_2017_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; lean_object* v_unused_2038_; 
v_unused_2037_ = lean_ctor_get(v_a_2017_, 2);
lean_dec(v_unused_2037_);
v_unused_2038_ = lean_ctor_get(v_a_2017_, 0);
lean_dec(v_unused_2038_);
v___x_2028_ = v_a_2017_;
v_isShared_2029_ = v_isSharedCheck_2036_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_trace_2026_);
lean_dec(v_a_2017_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2036_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 2, v_buildTime_2025_);
lean_ctor_set(v___x_2028_, 0, v_log_2022_);
v___x_2031_ = v___x_2028_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_log_2022_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v_trace_2026_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_buildTime_2025_);
v___x_2031_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*3, v_action_2023_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*3 + 1, v_wantsRebuild_2024_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 1, v___x_2031_);
v___x_2033_ = v___x_2019_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2016_);
lean_ctor_set(v_reuseFailAlloc_2034_, 1, v___x_2031_);
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
lean_object* v_a_2040_; lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2066_; 
v_a_2040_ = lean_ctor_get(v_x_2015_, 0);
v_a_2041_ = lean_ctor_get(v_x_2015_, 1);
v_isSharedCheck_2066_ = !lean_is_exclusive(v_x_2015_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2043_ = v_x_2015_;
v_isShared_2044_ = v_isSharedCheck_2066_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_inc(v_a_2040_);
lean_dec(v_x_2015_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2066_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v_log_2045_; lean_object* v___x_2046_; lean_object* v_log_2047_; uint8_t v_action_2048_; uint8_t v_wantsRebuild_2049_; lean_object* v_buildTime_2050_; lean_object* v_trace_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2063_; 
v_log_2045_ = lean_ctor_get(v_a_2014_, 0);
lean_inc_ref(v_log_2045_);
lean_inc(v_a_2041_);
v___x_2046_ = l_Lake_JobState_merge(v_a_2014_, v_a_2041_);
v_log_2047_ = lean_ctor_get(v___x_2046_, 0);
lean_inc_ref(v_log_2047_);
v_action_2048_ = lean_ctor_get_uint8(v___x_2046_, sizeof(void*)*3);
v_wantsRebuild_2049_ = lean_ctor_get_uint8(v___x_2046_, sizeof(void*)*3 + 1);
v_buildTime_2050_ = lean_ctor_get(v___x_2046_, 2);
lean_inc(v_buildTime_2050_);
lean_dec_ref(v___x_2046_);
v_trace_2051_ = lean_ctor_get(v_a_2041_, 1);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_a_2041_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; lean_object* v_unused_2065_; 
v_unused_2064_ = lean_ctor_get(v_a_2041_, 2);
lean_dec(v_unused_2064_);
v_unused_2065_ = lean_ctor_get(v_a_2041_, 0);
lean_dec(v_unused_2065_);
v___x_2053_ = v_a_2041_;
v_isShared_2054_ = v_isSharedCheck_2063_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_trace_2051_);
lean_dec(v_a_2041_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2063_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; 
v___x_2055_ = lean_array_get_size(v_log_2045_);
lean_dec_ref(v_log_2045_);
v___x_2056_ = lean_nat_add(v___x_2055_, v_a_2040_);
lean_dec(v_a_2040_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 2, v_buildTime_2050_);
lean_ctor_set(v___x_2053_, 0, v_log_2047_);
v___x_2058_ = v___x_2053_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_log_2047_);
lean_ctor_set(v_reuseFailAlloc_2062_, 1, v_trace_2051_);
lean_ctor_set(v_reuseFailAlloc_2062_, 2, v_buildTime_2050_);
v___x_2058_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
lean_object* v___x_2060_; 
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*3, v_action_2048_);
lean_ctor_set_uint8(v___x_2058_, sizeof(void*)*3 + 1, v_wantsRebuild_2049_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v___x_2058_);
lean_ctor_set(v___x_2043_, 0, v___x_2056_);
v___x_2060_ = v___x_2043_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2056_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2058_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object* v_val_2067_, lean_object* v_val_2068_, lean_object* v_a_x3f_2069_, lean_object* v___y_2070_){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2072_ = lean_get_set_stdout(v_val_2067_);
lean_dec_ref(v___x_2072_);
v___x_2073_ = lean_get_set_stderr(v_val_2068_);
lean_dec_ref(v___x_2073_);
v___x_2074_ = lean_box(0);
v___x_2075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2075_, 0, v___x_2074_);
lean_ctor_set(v___x_2075_, 1, v___y_2070_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1___boxed(lean_object* v_val_2076_, lean_object* v_val_2077_, lean_object* v_a_x3f_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lake_Job_bindM___redArg___lam__1(v_val_2076_, v_val_2077_, v_a_x3f_2078_, v___y_2079_);
lean_dec(v_a_x3f_2078_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object* v_a_2082_, lean_object* v_____r_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2091_, 0, v_a_2082_);
lean_ctor_set(v___x_2091_, 1, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2___boxed(lean_object* v_a_2092_, lean_object* v_____r_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2092_, v_____r_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3(lean_object* v_a_2102_, lean_object* v_prio_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_f_2109_, lean_object* v_x_2110_){
_start:
{
lean_object* v_a_2113_; lean_object* v_a_2114_; lean_object* v___y_2118_; uint8_t v___y_2128_; lean_object* v___y_2129_; lean_object* v___y_2130_; lean_object* v___y_2131_; uint8_t v___y_2132_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; lean_object* v___y_2136_; 
if (lean_obj_tag(v_x_2110_) == 0)
{
lean_object* v_a_2152_; lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2222_; 
v_a_2152_ = lean_ctor_get(v_x_2110_, 0);
v_a_2153_ = lean_ctor_get(v_x_2110_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_x_2110_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2155_ = v_x_2110_;
v_isShared_2156_ = v_isSharedCheck_2222_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_inc(v_a_2152_);
lean_dec(v_x_2110_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2222_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v_cancelTk_x3f_2200_; 
v_cancelTk_x3f_2200_ = lean_ctor_get(v_a_2102_, 6);
if (lean_obj_tag(v_cancelTk_x3f_2200_) == 1)
{
lean_object* v_val_2201_; uint8_t v___x_2202_; 
v_val_2201_ = lean_ctor_get(v_cancelTk_x3f_2200_, 0);
v___x_2202_ = l_IO_CancelToken_isSet(v_val_2201_);
if (v___x_2202_ == 0)
{
lean_del_object(v___x_2155_);
goto v___jp_2157_;
}
else
{
lean_object* v_log_2203_; uint8_t v_action_2204_; uint8_t v_wantsRebuild_2205_; lean_object* v_trace_2206_; lean_object* v_buildTime_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2152_);
lean_dec_ref(v_f_2109_);
lean_dec_ref(v_a_2104_);
lean_dec(v_prio_2103_);
v_log_2203_ = lean_ctor_get(v_a_2153_, 0);
v_action_2204_ = lean_ctor_get_uint8(v_a_2153_, sizeof(void*)*3);
v_wantsRebuild_2205_ = lean_ctor_get_uint8(v_a_2153_, sizeof(void*)*3 + 1);
v_trace_2206_ = lean_ctor_get(v_a_2153_, 1);
v_buildTime_2207_ = lean_ctor_get(v_a_2153_, 2);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_a_2153_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2209_ = v_a_2153_;
v_isShared_2210_ = v_isSharedCheck_2221_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_buildTime_2207_);
lean_inc(v_trace_2206_);
lean_inc(v_log_2203_);
lean_dec(v_a_2153_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2221_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2211_ = lean_array_get_size(v_log_2203_);
v___x_2212_ = lean_obj_once(&l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0, &l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0_once, _init_l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0);
v___x_2213_ = lean_array_push(v_log_2203_, v___x_2212_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2213_);
v___x_2215_ = v___x_2209_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_trace_2206_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_buildTime_2207_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, sizeof(void*)*3, v_action_2204_);
lean_ctor_set_uint8(v_reuseFailAlloc_2220_, sizeof(void*)*3 + 1, v_wantsRebuild_2205_);
v___x_2215_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2217_; 
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 1);
lean_ctor_set(v___x_2155_, 1, v___x_2215_);
lean_ctor_set(v___x_2155_, 0, v___x_2211_);
v___x_2217_ = v___x_2155_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_task_pure(v___x_2217_);
return v___x_2218_;
}
}
}
}
}
else
{
lean_del_object(v___x_2155_);
goto v___jp_2157_;
}
v___jp_2157_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v_log_2164_; uint8_t v_action_2165_; uint8_t v_wantsRebuild_2166_; lean_object* v_trace_2167_; lean_object* v_buildTime_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2199_; 
v___x_2158_ = lean_unsigned_to_nat(0u);
v___x_2159_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_2160_ = lean_st_mk_ref(v___x_2159_);
lean_inc(v___x_2160_);
v___x_2161_ = l_IO_FS_Stream_ofBuffer(v___x_2160_);
lean_inc_ref(v___x_2161_);
v___x_2162_ = lean_get_set_stdout(v___x_2161_);
v___x_2163_ = lean_get_set_stderr(v___x_2161_);
v_log_2164_ = lean_ctor_get(v_a_2153_, 0);
v_action_2165_ = lean_ctor_get_uint8(v_a_2153_, sizeof(void*)*3);
v_wantsRebuild_2166_ = lean_ctor_get_uint8(v_a_2153_, sizeof(void*)*3 + 1);
v_trace_2167_ = lean_ctor_get(v_a_2153_, 1);
v_buildTime_2168_ = lean_ctor_get(v_a_2153_, 2);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_a_2153_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2170_ = v_a_2153_;
v_isShared_2171_ = v_isSharedCheck_2199_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_buildTime_2168_);
lean_inc(v_trace_2167_);
lean_inc(v_log_2164_);
lean_dec(v_a_2153_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2199_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
lean_object* v_trace_2172_; lean_object* v___x_2174_; 
lean_inc_ref(v_a_2108_);
v_trace_2172_ = l_Lake_BuildTrace_mix(v_a_2108_, v_trace_2167_);
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 1, v_trace_2172_);
v___x_2174_ = v___x_2170_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_log_2164_);
lean_ctor_set(v_reuseFailAlloc_2198_, 1, v_trace_2172_);
lean_ctor_set(v_reuseFailAlloc_2198_, 2, v_buildTime_2168_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*3, v_action_2165_);
lean_ctor_set_uint8(v_reuseFailAlloc_2198_, sizeof(void*)*3 + 1, v_wantsRebuild_2166_);
v___x_2174_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; 
lean_inc_ref(v_a_2102_);
lean_inc(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc(v_a_2105_);
lean_inc_ref(v_a_2104_);
v___x_2175_ = lean_apply_8(v_f_2109_, v_a_2152_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2102_, v___x_2174_, lean_box(0));
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v_a_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v_a_2180_; lean_object* v___x_2181_; lean_object* v_log_2182_; uint8_t v_action_2183_; uint8_t v_wantsRebuild_2184_; lean_object* v_trace_2185_; lean_object* v_buildTime_2186_; lean_object* v_data_2187_; lean_object* v___f_2188_; uint8_t v___x_2189_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc_n(v_a_2176_, 2);
v_a_2177_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2175_, 2);
v___x_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2178_, 0, v_a_2176_);
v___x_2179_ = l_Lake_Job_bindM___redArg___lam__1(v___x_2162_, v___x_2163_, v___x_2178_, v_a_2177_);
lean_dec_ref_known(v___x_2178_, 1);
v_a_2180_ = lean_ctor_get(v___x_2179_, 1);
lean_inc(v_a_2180_);
lean_dec_ref(v___x_2179_);
v___x_2181_ = lean_st_ref_get(v___x_2160_);
lean_dec(v___x_2160_);
v_log_2182_ = lean_ctor_get(v_a_2180_, 0);
lean_inc_ref(v_log_2182_);
v_action_2183_ = lean_ctor_get_uint8(v_a_2180_, sizeof(void*)*3);
v_wantsRebuild_2184_ = lean_ctor_get_uint8(v_a_2180_, sizeof(void*)*3 + 1);
v_trace_2185_ = lean_ctor_get(v_a_2180_, 1);
lean_inc_ref(v_trace_2185_);
v_buildTime_2186_ = lean_ctor_get(v_a_2180_, 2);
lean_inc(v_buildTime_2186_);
v_data_2187_ = lean_ctor_get(v___x_2181_, 0);
lean_inc_ref(v_data_2187_);
lean_dec(v___x_2181_);
v___f_2188_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_2188_, 0, v_a_2176_);
v___x_2189_ = lean_string_validate_utf8(v_data_2187_);
if (v___x_2189_ == 0)
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec_ref(v_data_2187_);
v___x_2190_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2191_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2190_);
v___y_2128_ = v_action_2183_;
v___y_2129_ = v___f_2188_;
v___y_2130_ = v_a_2180_;
v___y_2131_ = v_trace_2185_;
v___y_2132_ = v_wantsRebuild_2184_;
v___y_2133_ = v_log_2182_;
v___y_2134_ = v_buildTime_2186_;
v___y_2135_ = v___x_2158_;
v___y_2136_ = v___x_2191_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_string_from_utf8_unchecked(v_data_2187_);
v___y_2128_ = v_action_2183_;
v___y_2129_ = v___f_2188_;
v___y_2130_ = v_a_2180_;
v___y_2131_ = v_trace_2185_;
v___y_2132_ = v_wantsRebuild_2184_;
v___y_2133_ = v_log_2182_;
v___y_2134_ = v_buildTime_2186_;
v___y_2135_ = v___x_2158_;
v___y_2136_ = v___x_2192_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v_a_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v_a_2197_; 
lean_dec(v___x_2160_);
lean_dec_ref(v_a_2104_);
lean_dec(v_prio_2103_);
v_a_2193_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2193_);
v_a_2194_ = lean_ctor_get(v___x_2175_, 1);
lean_inc(v_a_2194_);
lean_dec_ref_known(v___x_2175_, 2);
v___x_2195_ = lean_box(0);
v___x_2196_ = l_Lake_Job_bindM___redArg___lam__1(v___x_2162_, v___x_2163_, v___x_2195_, v_a_2194_);
v_a_2197_ = lean_ctor_get(v___x_2196_, 1);
lean_inc(v_a_2197_);
lean_dec_ref(v___x_2196_);
v_a_2113_ = v_a_2193_;
v_a_2114_ = v_a_2197_;
goto v___jp_2112_;
}
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2232_; 
lean_dec_ref(v_f_2109_);
lean_dec_ref(v_a_2104_);
lean_dec(v_prio_2103_);
v_a_2223_ = lean_ctor_get(v_x_2110_, 0);
v_a_2224_ = lean_ctor_get(v_x_2110_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_x_2110_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2226_ = v_x_2110_;
v_isShared_2227_ = v_isSharedCheck_2232_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_inc(v_a_2223_);
lean_dec(v_x_2110_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2232_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2223_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
lean_object* v___x_2230_; 
v___x_2230_ = lean_task_pure(v___x_2229_);
return v___x_2230_;
}
}
}
v___jp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2115_, 0, v_a_2113_);
lean_ctor_set(v___x_2115_, 1, v_a_2114_);
v___x_2116_ = lean_task_pure(v___x_2115_);
return v___x_2116_;
}
v___jp_2117_:
{
if (lean_obj_tag(v___y_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v_a_2120_; lean_object* v_task_2121_; lean_object* v___f_2122_; uint8_t v___x_2123_; lean_object* v___x_2124_; 
v_a_2119_ = lean_ctor_get(v___y_2118_, 0);
lean_inc(v_a_2119_);
v_a_2120_ = lean_ctor_get(v___y_2118_, 1);
lean_inc(v_a_2120_);
lean_dec_ref_known(v___y_2118_, 2);
v_task_2121_ = lean_ctor_get(v_a_2119_, 0);
lean_inc_ref(v_task_2121_);
lean_dec(v_a_2119_);
v___f_2122_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2122_, 0, v_a_2120_);
v___x_2123_ = 1;
v___x_2124_ = lean_task_map(v___f_2122_, v_task_2121_, v_prio_2103_, v___x_2123_);
return v___x_2124_;
}
else
{
lean_object* v_a_2125_; lean_object* v_a_2126_; 
lean_dec(v_prio_2103_);
v_a_2125_ = lean_ctor_get(v___y_2118_, 0);
lean_inc(v_a_2125_);
v_a_2126_ = lean_ctor_get(v___y_2118_, 1);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___y_2118_, 2);
v_a_2113_ = v_a_2125_;
v_a_2114_ = v_a_2126_;
goto v___jp_2112_;
}
}
v___jp_2127_:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = lean_string_utf8_byte_size(v___y_2136_);
v___x_2138_ = lean_nat_dec_eq(v___x_2137_, v___y_2135_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec_ref(v___y_2130_);
v___x_2139_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_2140_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2140_, 0, v___y_2136_);
lean_ctor_set(v___x_2140_, 1, v___y_2135_);
lean_ctor_set(v___x_2140_, 2, v___x_2137_);
v___x_2141_ = l_String_Slice_trimAscii(v___x_2140_);
v___x_2142_ = l_String_Slice_toString(v___x_2141_);
lean_dec_ref(v___x_2141_);
v___x_2143_ = lean_string_append(v___x_2139_, v___x_2142_);
lean_dec_ref(v___x_2142_);
v___x_2144_ = 1;
v___x_2145_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set_uint8(v___x_2145_, sizeof(void*)*1, v___x_2144_);
v___x_2146_ = lean_box(0);
v___x_2147_ = lean_array_push(v___y_2133_, v___x_2145_);
v___x_2148_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
lean_ctor_set(v___x_2148_, 1, v___y_2131_);
lean_ctor_set(v___x_2148_, 2, v___y_2134_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*3, v___y_2128_);
lean_ctor_set_uint8(v___x_2148_, sizeof(void*)*3 + 1, v___y_2132_);
lean_inc_ref(v_a_2102_);
lean_inc(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc(v_a_2105_);
v___x_2149_ = lean_apply_8(v___y_2129_, v___x_2146_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2102_, v___x_2148_, lean_box(0));
v___y_2118_ = v___x_2149_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
lean_dec_ref(v___y_2131_);
v___x_2150_ = lean_box(0);
lean_inc_ref(v_a_2102_);
lean_inc(v_a_2107_);
lean_inc(v_a_2106_);
lean_inc(v_a_2105_);
v___x_2151_ = lean_apply_8(v___y_2129_, v___x_2150_, v_a_2104_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2102_, v___y_2130_, lean_box(0));
v___y_2118_ = v___x_2151_;
goto v___jp_2117_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3___boxed(lean_object* v_a_2233_, lean_object* v_prio_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_f_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lake_Job_bindM___redArg___lam__3(v_a_2233_, v_prio_2234_, v_a_2235_, v_a_2236_, v_a_2237_, v_a_2238_, v_a_2239_, v_f_2240_, v_x_2241_);
lean_dec_ref(v_a_2239_);
lean_dec(v_a_2238_);
lean_dec(v_a_2237_);
lean_dec(v_a_2236_);
lean_dec_ref(v_a_2233_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg(lean_object* v_kind_2244_, lean_object* v_self_2245_, lean_object* v_f_2246_, lean_object* v_prio_2247_, uint8_t v_sync_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_){
_start:
{
lean_object* v_task_2256_; lean_object* v_caption_2257_; uint8_t v_optional_2258_; lean_object* v___x_2260_; uint8_t v_isShared_2261_; uint8_t v_isSharedCheck_2267_; 
v_task_2256_ = lean_ctor_get(v_self_2245_, 0);
v_caption_2257_ = lean_ctor_get(v_self_2245_, 2);
v_optional_2258_ = lean_ctor_get_uint8(v_self_2245_, sizeof(void*)*3);
v_isSharedCheck_2267_ = !lean_is_exclusive(v_self_2245_);
if (v_isSharedCheck_2267_ == 0)
{
lean_object* v_unused_2268_; 
v_unused_2268_ = lean_ctor_get(v_self_2245_, 1);
lean_dec(v_unused_2268_);
v___x_2260_ = v_self_2245_;
v_isShared_2261_ = v_isSharedCheck_2267_;
goto v_resetjp_2259_;
}
else
{
lean_inc(v_caption_2257_);
lean_inc(v_task_2256_);
lean_dec(v_self_2245_);
v___x_2260_ = lean_box(0);
v_isShared_2261_ = v_isSharedCheck_2267_;
goto v_resetjp_2259_;
}
v_resetjp_2259_:
{
lean_object* v___f_2262_; lean_object* v___x_2263_; lean_object* v___x_2265_; 
lean_inc_ref(v_a_2254_);
lean_inc(v_a_2252_);
lean_inc(v_a_2251_);
lean_inc(v_a_2250_);
lean_inc(v_prio_2247_);
lean_inc_ref(v_a_2253_);
v___f_2262_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__3___boxed), 10, 8);
lean_closure_set(v___f_2262_, 0, v_a_2253_);
lean_closure_set(v___f_2262_, 1, v_prio_2247_);
lean_closure_set(v___f_2262_, 2, v_a_2249_);
lean_closure_set(v___f_2262_, 3, v_a_2250_);
lean_closure_set(v___f_2262_, 4, v_a_2251_);
lean_closure_set(v___f_2262_, 5, v_a_2252_);
lean_closure_set(v___f_2262_, 6, v_a_2254_);
lean_closure_set(v___f_2262_, 7, v_f_2246_);
v___x_2263_ = lean_io_bind_task(v_task_2256_, v___f_2262_, v_prio_2247_, v_sync_2248_);
if (v_isShared_2261_ == 0)
{
lean_ctor_set(v___x_2260_, 1, v_kind_2244_);
lean_ctor_set(v___x_2260_, 0, v___x_2263_);
v___x_2265_ = v___x_2260_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v___x_2263_);
lean_ctor_set(v_reuseFailAlloc_2266_, 1, v_kind_2244_);
lean_ctor_set(v_reuseFailAlloc_2266_, 2, v_caption_2257_);
lean_ctor_set_uint8(v_reuseFailAlloc_2266_, sizeof(void*)*3, v_optional_2258_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object* v_kind_2269_, lean_object* v_self_2270_, lean_object* v_f_2271_, lean_object* v_prio_2272_, lean_object* v_sync_2273_, lean_object* v_a_2274_, lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_, lean_object* v_a_2280_){
_start:
{
uint8_t v_sync_boxed_2281_; lean_object* v_res_2282_; 
v_sync_boxed_2281_ = lean_unbox(v_sync_2273_);
v_res_2282_ = l_Lake_Job_bindM___redArg(v_kind_2269_, v_self_2270_, v_f_2271_, v_prio_2272_, v_sync_boxed_2281_, v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
lean_dec_ref(v_a_2279_);
lean_dec_ref(v_a_2278_);
lean_dec(v_a_2277_);
lean_dec(v_a_2276_);
lean_dec(v_a_2275_);
return v_res_2282_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM(lean_object* v_00_u03b2_2283_, lean_object* v_00_u03b1_2284_, lean_object* v_kind_2285_, lean_object* v_self_2286_, lean_object* v_f_2287_, lean_object* v_prio_2288_, uint8_t v_sync_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_, lean_object* v_a_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Lake_Job_bindM___redArg(v_kind_2285_, v_self_2286_, v_f_2287_, v_prio_2288_, v_sync_2289_, v_a_2290_, v_a_2291_, v_a_2292_, v_a_2293_, v_a_2294_, v_a_2295_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object* v_00_u03b2_2298_, lean_object* v_00_u03b1_2299_, lean_object* v_kind_2300_, lean_object* v_self_2301_, lean_object* v_f_2302_, lean_object* v_prio_2303_, lean_object* v_sync_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
uint8_t v_sync_boxed_2312_; lean_object* v_res_2313_; 
v_sync_boxed_2312_ = lean_unbox(v_sync_2304_);
v_res_2313_ = l_Lake_Job_bindM(v_00_u03b2_2298_, v_00_u03b1_2299_, v_kind_2300_, v_self_2301_, v_f_2302_, v_prio_2303_, v_sync_boxed_2312_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec_ref(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec(v_a_2307_);
lean_dec(v_a_2306_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object* v_f_2314_, lean_object* v_rx_2315_, lean_object* v_ry_2316_){
_start:
{
lean_object* v___x_2317_; 
v___x_2317_ = lean_apply_2(v_f_2314_, v_rx_2315_, v_ry_2316_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object* v_other_2318_, lean_object* v_f_2319_, lean_object* v_prio_2320_, uint8_t v_sync_2321_, lean_object* v_rx_2322_){
_start:
{
lean_object* v_task_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; 
v_task_2323_ = lean_ctor_get(v_other_2318_, 0);
lean_inc_ref(v_task_2323_);
lean_dec_ref(v_other_2318_);
v___f_2324_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2324_, 0, v_f_2319_);
lean_closure_set(v___f_2324_, 1, v_rx_2322_);
v___x_2325_ = lean_task_map(v___f_2324_, v_task_2323_, v_prio_2320_, v_sync_2321_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object* v_other_2326_, lean_object* v_f_2327_, lean_object* v_prio_2328_, lean_object* v_sync_2329_, lean_object* v_rx_2330_){
_start:
{
uint8_t v_sync_boxed_2331_; lean_object* v_res_2332_; 
v_sync_boxed_2331_ = lean_unbox(v_sync_2329_);
v_res_2332_ = l_Lake_Job_zipResultWith___redArg___lam__1(v_other_2326_, v_f_2327_, v_prio_2328_, v_sync_boxed_2331_, v_rx_2330_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg(lean_object* v_inst_2333_, lean_object* v_f_2334_, lean_object* v_self_2335_, lean_object* v_other_2336_, lean_object* v_prio_2337_, uint8_t v_sync_2338_){
_start:
{
lean_object* v_task_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2352_; 
v_task_2339_ = lean_ctor_get(v_self_2335_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_self_2335_);
if (v_isSharedCheck_2352_ == 0)
{
lean_object* v_unused_2353_; lean_object* v_unused_2354_; 
v_unused_2353_ = lean_ctor_get(v_self_2335_, 2);
lean_dec(v_unused_2353_);
v_unused_2354_ = lean_ctor_get(v_self_2335_, 1);
lean_dec(v_unused_2354_);
v___x_2341_ = v_self_2335_;
v_isShared_2342_ = v_isSharedCheck_2352_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_task_2339_);
lean_dec(v_self_2335_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2352_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v___f_2344_; uint8_t v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; uint8_t v___x_2348_; lean_object* v___x_2350_; 
v___x_2343_ = lean_box(v_sync_2338_);
lean_inc(v_prio_2337_);
v___f_2344_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2344_, 0, v_other_2336_);
lean_closure_set(v___f_2344_, 1, v_f_2334_);
lean_closure_set(v___f_2344_, 2, v_prio_2337_);
lean_closure_set(v___f_2344_, 3, v___x_2343_);
v___x_2345_ = 1;
v___x_2346_ = lean_task_bind(v_task_2339_, v___f_2344_, v_prio_2337_, v___x_2345_);
v___x_2347_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2348_ = 0;
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 2, v___x_2347_);
lean_ctor_set(v___x_2341_, 1, v_inst_2333_);
lean_ctor_set(v___x_2341_, 0, v___x_2346_);
v___x_2350_ = v___x_2341_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v_inst_2333_);
lean_ctor_set(v_reuseFailAlloc_2351_, 2, v___x_2347_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
lean_ctor_set_uint8(v___x_2350_, sizeof(void*)*3, v___x_2348_);
return v___x_2350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object* v_inst_2355_, lean_object* v_f_2356_, lean_object* v_self_2357_, lean_object* v_other_2358_, lean_object* v_prio_2359_, lean_object* v_sync_2360_){
_start:
{
uint8_t v_sync_boxed_2361_; lean_object* v_res_2362_; 
v_sync_boxed_2361_ = lean_unbox(v_sync_2360_);
v_res_2362_ = l_Lake_Job_zipResultWith___redArg(v_inst_2355_, v_f_2356_, v_self_2357_, v_other_2358_, v_prio_2359_, v_sync_boxed_2361_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith(lean_object* v_00_u03b3_2363_, lean_object* v_00_u03b1_2364_, lean_object* v_00_u03b2_2365_, lean_object* v_inst_2366_, lean_object* v_f_2367_, lean_object* v_self_2368_, lean_object* v_other_2369_, lean_object* v_prio_2370_, uint8_t v_sync_2371_){
_start:
{
lean_object* v_task_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2385_; 
v_task_2372_ = lean_ctor_get(v_self_2368_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v_self_2368_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; lean_object* v_unused_2387_; 
v_unused_2386_ = lean_ctor_get(v_self_2368_, 2);
lean_dec(v_unused_2386_);
v_unused_2387_ = lean_ctor_get(v_self_2368_, 1);
lean_dec(v_unused_2387_);
v___x_2374_ = v_self_2368_;
v_isShared_2375_ = v_isSharedCheck_2385_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_task_2372_);
lean_dec(v_self_2368_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2385_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___f_2377_; uint8_t v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; uint8_t v___x_2381_; lean_object* v___x_2383_; 
v___x_2376_ = lean_box(v_sync_2371_);
lean_inc(v_prio_2370_);
v___f_2377_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2377_, 0, v_other_2369_);
lean_closure_set(v___f_2377_, 1, v_f_2367_);
lean_closure_set(v___f_2377_, 2, v_prio_2370_);
lean_closure_set(v___f_2377_, 3, v___x_2376_);
v___x_2378_ = 1;
v___x_2379_ = lean_task_bind(v_task_2372_, v___f_2377_, v_prio_2370_, v___x_2378_);
v___x_2380_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2381_ = 0;
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 2, v___x_2380_);
lean_ctor_set(v___x_2374_, 1, v_inst_2366_);
lean_ctor_set(v___x_2374_, 0, v___x_2379_);
v___x_2383_ = v___x_2374_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2379_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_inst_2366_);
lean_ctor_set(v_reuseFailAlloc_2384_, 2, v___x_2380_);
v___x_2383_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_ctor_set_uint8(v___x_2383_, sizeof(void*)*3, v___x_2381_);
return v___x_2383_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object* v_00_u03b3_2388_, lean_object* v_00_u03b1_2389_, lean_object* v_00_u03b2_2390_, lean_object* v_inst_2391_, lean_object* v_f_2392_, lean_object* v_self_2393_, lean_object* v_other_2394_, lean_object* v_prio_2395_, lean_object* v_sync_2396_){
_start:
{
uint8_t v_sync_boxed_2397_; lean_object* v_res_2398_; 
v_sync_boxed_2397_ = lean_unbox(v_sync_2396_);
v_res_2398_ = l_Lake_Job_zipResultWith(v_00_u03b3_2388_, v_00_u03b1_2389_, v_00_u03b2_2390_, v_inst_2391_, v_f_2392_, v_self_2393_, v_other_2394_, v_prio_2395_, v_sync_boxed_2397_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object* v_rx_2399_, lean_object* v_f_2400_, lean_object* v_ry_2401_){
_start:
{
lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v_a_2414_; 
if (lean_obj_tag(v_rx_2399_) == 0)
{
if (lean_obj_tag(v_ry_2401_) == 0)
{
lean_object* v_a_2416_; lean_object* v_a_2417_; lean_object* v_a_2418_; lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2428_; 
v_a_2416_ = lean_ctor_get(v_rx_2399_, 0);
lean_inc(v_a_2416_);
v_a_2417_ = lean_ctor_get(v_rx_2399_, 1);
lean_inc(v_a_2417_);
lean_dec_ref_known(v_rx_2399_, 2);
v_a_2418_ = lean_ctor_get(v_ry_2401_, 0);
v_a_2419_ = lean_ctor_get(v_ry_2401_, 1);
v_isSharedCheck_2428_ = !lean_is_exclusive(v_ry_2401_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2421_ = v_ry_2401_;
v_isShared_2422_ = v_isSharedCheck_2428_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_inc(v_a_2418_);
lean_dec(v_ry_2401_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2428_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2426_; 
v___x_2423_ = lean_apply_2(v_f_2400_, v_a_2416_, v_a_2418_);
v___x_2424_ = l_Lake_JobState_merge(v_a_2417_, v_a_2419_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v___x_2424_);
lean_ctor_set(v___x_2421_, 0, v___x_2423_);
v___x_2426_ = v___x_2421_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2427_, 1, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
else
{
lean_object* v_a_2429_; 
lean_dec(v_f_2400_);
v_a_2429_ = lean_ctor_get(v_rx_2399_, 1);
lean_inc(v_a_2429_);
lean_dec_ref_known(v_rx_2399_, 2);
v_a_2414_ = v_a_2429_;
goto v___jp_2413_;
}
}
else
{
lean_dec(v_f_2400_);
if (lean_obj_tag(v_rx_2399_) == 0)
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v_rx_2399_, 1);
lean_inc(v_a_2430_);
lean_dec_ref_known(v_rx_2399_, 2);
v_a_2414_ = v_a_2430_;
goto v___jp_2413_;
}
else
{
lean_object* v_a_2431_; lean_object* v___x_2432_; 
v_a_2431_ = lean_ctor_get(v_rx_2399_, 1);
lean_inc(v_a_2431_);
lean_dec_ref_known(v_rx_2399_, 2);
v___x_2432_ = lean_unsigned_to_nat(0u);
v___y_2409_ = v_ry_2401_;
v___y_2410_ = v___x_2432_;
v___y_2411_ = v_a_2431_;
goto v___jp_2408_;
}
}
v___jp_2402_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = l_Lake_JobState_merge(v___y_2404_, v___y_2405_);
v___x_2407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___y_2403_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
return v___x_2407_;
}
v___jp_2408_:
{
lean_object* v_a_2412_; 
v_a_2412_ = lean_ctor_get(v___y_2409_, 1);
lean_inc(v_a_2412_);
lean_dec_ref(v___y_2409_);
v___y_2403_ = v___y_2410_;
v___y_2404_ = v___y_2411_;
v___y_2405_ = v_a_2412_;
goto v___jp_2402_;
}
v___jp_2413_:
{
lean_object* v___x_2415_; 
v___x_2415_ = lean_unsigned_to_nat(0u);
v___y_2409_ = v_ry_2401_;
v___y_2410_ = v___x_2415_;
v___y_2411_ = v_a_2414_;
goto v___jp_2408_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object* v_other_2433_, lean_object* v_f_2434_, lean_object* v_prio_2435_, uint8_t v_sync_2436_, lean_object* v_rx_2437_){
_start:
{
lean_object* v_task_2438_; lean_object* v___f_2439_; lean_object* v___x_2440_; 
v_task_2438_ = lean_ctor_get(v_other_2433_, 0);
lean_inc_ref(v_task_2438_);
lean_dec_ref(v_other_2433_);
v___f_2439_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2439_, 0, v_rx_2437_);
lean_closure_set(v___f_2439_, 1, v_f_2434_);
v___x_2440_ = lean_task_map(v___f_2439_, v_task_2438_, v_prio_2435_, v_sync_2436_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object* v_other_2441_, lean_object* v_f_2442_, lean_object* v_prio_2443_, lean_object* v_sync_2444_, lean_object* v_rx_2445_){
_start:
{
uint8_t v_sync_boxed_2446_; lean_object* v_res_2447_; 
v_sync_boxed_2446_ = lean_unbox(v_sync_2444_);
v_res_2447_ = l_Lake_Job_zipWith___redArg___lam__1(v_other_2441_, v_f_2442_, v_prio_2443_, v_sync_boxed_2446_, v_rx_2445_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg(lean_object* v_inst_2448_, lean_object* v_f_2449_, lean_object* v_self_2450_, lean_object* v_other_2451_, lean_object* v_prio_2452_, uint8_t v_sync_2453_){
_start:
{
lean_object* v_task_2454_; lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2467_; 
v_task_2454_ = lean_ctor_get(v_self_2450_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v_self_2450_);
if (v_isSharedCheck_2467_ == 0)
{
lean_object* v_unused_2468_; lean_object* v_unused_2469_; 
v_unused_2468_ = lean_ctor_get(v_self_2450_, 2);
lean_dec(v_unused_2468_);
v_unused_2469_ = lean_ctor_get(v_self_2450_, 1);
lean_dec(v_unused_2469_);
v___x_2456_ = v_self_2450_;
v_isShared_2457_ = v_isSharedCheck_2467_;
goto v_resetjp_2455_;
}
else
{
lean_inc(v_task_2454_);
lean_dec(v_self_2450_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2467_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___f_2459_; uint8_t v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; lean_object* v___x_2465_; 
v___x_2458_ = lean_box(v_sync_2453_);
lean_inc(v_prio_2452_);
v___f_2459_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2459_, 0, v_other_2451_);
lean_closure_set(v___f_2459_, 1, v_f_2449_);
lean_closure_set(v___f_2459_, 2, v_prio_2452_);
lean_closure_set(v___f_2459_, 3, v___x_2458_);
v___x_2460_ = 1;
v___x_2461_ = lean_task_bind(v_task_2454_, v___f_2459_, v_prio_2452_, v___x_2460_);
v___x_2462_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2463_ = 0;
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 2, v___x_2462_);
lean_ctor_set(v___x_2456_, 1, v_inst_2448_);
lean_ctor_set(v___x_2456_, 0, v___x_2461_);
v___x_2465_ = v___x_2456_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2466_, 1, v_inst_2448_);
lean_ctor_set(v_reuseFailAlloc_2466_, 2, v___x_2462_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_ctor_set_uint8(v___x_2465_, sizeof(void*)*3, v___x_2463_);
return v___x_2465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object* v_inst_2470_, lean_object* v_f_2471_, lean_object* v_self_2472_, lean_object* v_other_2473_, lean_object* v_prio_2474_, lean_object* v_sync_2475_){
_start:
{
uint8_t v_sync_boxed_2476_; lean_object* v_res_2477_; 
v_sync_boxed_2476_ = lean_unbox(v_sync_2475_);
v_res_2477_ = l_Lake_Job_zipWith___redArg(v_inst_2470_, v_f_2471_, v_self_2472_, v_other_2473_, v_prio_2474_, v_sync_boxed_2476_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__0(lean_object* v_rx_2478_, lean_object* v_f_2479_, lean_object* v_ry_2480_){
_start:
{
lean_object* v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2488_; lean_object* v___y_2489_; lean_object* v___y_2490_; lean_object* v_a_2493_; lean_object* v_rb_2494_; 
if (lean_obj_tag(v_rx_2478_) == 0)
{
if (lean_obj_tag(v_ry_2480_) == 0)
{
lean_object* v_a_2496_; lean_object* v_a_2497_; lean_object* v_a_2498_; lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2508_; 
v_a_2496_ = lean_ctor_get(v_rx_2478_, 0);
lean_inc(v_a_2496_);
v_a_2497_ = lean_ctor_get(v_rx_2478_, 1);
lean_inc(v_a_2497_);
lean_dec_ref_known(v_rx_2478_, 2);
v_a_2498_ = lean_ctor_get(v_ry_2480_, 0);
v_a_2499_ = lean_ctor_get(v_ry_2480_, 1);
v_isSharedCheck_2508_ = !lean_is_exclusive(v_ry_2480_);
if (v_isSharedCheck_2508_ == 0)
{
v___x_2501_ = v_ry_2480_;
v_isShared_2502_ = v_isSharedCheck_2508_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_inc(v_a_2498_);
lean_dec(v_ry_2480_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2508_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2506_; 
v___x_2503_ = lean_apply_2(v_f_2479_, v_a_2496_, v_a_2498_);
v___x_2504_ = l_Lake_JobState_merge(v_a_2497_, v_a_2499_);
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 1, v___x_2504_);
lean_ctor_set(v___x_2501_, 0, v___x_2503_);
v___x_2506_ = v___x_2501_;
goto v_reusejp_2505_;
}
else
{
lean_object* v_reuseFailAlloc_2507_; 
v_reuseFailAlloc_2507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2507_, 0, v___x_2503_);
lean_ctor_set(v_reuseFailAlloc_2507_, 1, v___x_2504_);
v___x_2506_ = v_reuseFailAlloc_2507_;
goto v_reusejp_2505_;
}
v_reusejp_2505_:
{
return v___x_2506_;
}
}
}
else
{
lean_object* v_a_2509_; 
lean_dec(v_f_2479_);
v_a_2509_ = lean_ctor_get(v_rx_2478_, 1);
lean_inc(v_a_2509_);
lean_dec_ref_known(v_rx_2478_, 2);
v_a_2493_ = v_a_2509_;
v_rb_2494_ = v_ry_2480_;
goto v___jp_2492_;
}
}
else
{
lean_dec(v_f_2479_);
if (lean_obj_tag(v_rx_2478_) == 0)
{
lean_object* v_a_2510_; 
v_a_2510_ = lean_ctor_get(v_rx_2478_, 1);
lean_inc(v_a_2510_);
lean_dec_ref_known(v_rx_2478_, 2);
v_a_2493_ = v_a_2510_;
v_rb_2494_ = v_ry_2480_;
goto v___jp_2492_;
}
else
{
lean_object* v_a_2511_; lean_object* v___x_2512_; 
v_a_2511_ = lean_ctor_get(v_rx_2478_, 1);
lean_inc(v_a_2511_);
lean_dec_ref_known(v_rx_2478_, 2);
v___x_2512_ = lean_unsigned_to_nat(0u);
v___y_2488_ = v_ry_2480_;
v___y_2489_ = v___x_2512_;
v___y_2490_ = v_a_2511_;
goto v___jp_2487_;
}
}
v___jp_2481_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = l_Lake_JobState_merge(v___y_2483_, v___y_2484_);
v___x_2486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___y_2482_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
return v___x_2486_;
}
v___jp_2487_:
{
lean_object* v_a_2491_; 
v_a_2491_ = lean_ctor_get(v___y_2488_, 1);
lean_inc(v_a_2491_);
lean_dec_ref(v___y_2488_);
v___y_2482_ = v___y_2489_;
v___y_2483_ = v___y_2490_;
v___y_2484_ = v_a_2491_;
goto v___jp_2481_;
}
v___jp_2492_:
{
lean_object* v___x_2495_; 
v___x_2495_ = lean_unsigned_to_nat(0u);
v___y_2488_ = v_rb_2494_;
v___y_2489_ = v___x_2495_;
v___y_2490_ = v_a_2493_;
goto v___jp_2487_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1(lean_object* v_other_2513_, lean_object* v_f_2514_, lean_object* v_prio_2515_, uint8_t v_sync_2516_, lean_object* v_rx_2517_){
_start:
{
lean_object* v_task_2518_; lean_object* v___f_2519_; lean_object* v___x_2520_; 
v_task_2518_ = lean_ctor_get(v_other_2513_, 0);
lean_inc_ref(v_task_2518_);
lean_dec_ref(v_other_2513_);
v___f_2519_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__0), 3, 2);
lean_closure_set(v___f_2519_, 0, v_rx_2517_);
lean_closure_set(v___f_2519_, 1, v_f_2514_);
v___x_2520_ = lean_task_map(v___f_2519_, v_task_2518_, v_prio_2515_, v_sync_2516_);
return v___x_2520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1___boxed(lean_object* v_other_2521_, lean_object* v_f_2522_, lean_object* v_prio_2523_, lean_object* v_sync_2524_, lean_object* v_rx_2525_){
_start:
{
uint8_t v_sync_boxed_2526_; lean_object* v_res_2527_; 
v_sync_boxed_2526_ = lean_unbox(v_sync_2524_);
v_res_2527_ = l_Lake_Job_zipWith___lam__1(v_other_2521_, v_f_2522_, v_prio_2523_, v_sync_boxed_2526_, v_rx_2525_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith(lean_object* v_00_u03b3_2528_, lean_object* v_00_u03b1_2529_, lean_object* v_00_u03b2_2530_, lean_object* v_inst_2531_, lean_object* v_f_2532_, lean_object* v_self_2533_, lean_object* v_other_2534_, lean_object* v_prio_2535_, uint8_t v_sync_2536_){
_start:
{
lean_object* v_task_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2550_; 
v_task_2537_ = lean_ctor_get(v_self_2533_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_self_2533_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; lean_object* v_unused_2552_; 
v_unused_2551_ = lean_ctor_get(v_self_2533_, 2);
lean_dec(v_unused_2551_);
v_unused_2552_ = lean_ctor_get(v_self_2533_, 1);
lean_dec(v_unused_2552_);
v___x_2539_ = v_self_2533_;
v_isShared_2540_ = v_isSharedCheck_2550_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_task_2537_);
lean_dec(v_self_2533_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2550_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___f_2542_; uint8_t v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; lean_object* v___x_2548_; 
v___x_2541_ = lean_box(v_sync_2536_);
lean_inc(v_prio_2535_);
v___f_2542_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2542_, 0, v_other_2534_);
lean_closure_set(v___f_2542_, 1, v_f_2532_);
lean_closure_set(v___f_2542_, 2, v_prio_2535_);
lean_closure_set(v___f_2542_, 3, v___x_2541_);
v___x_2543_ = 1;
v___x_2544_ = lean_task_bind(v_task_2537_, v___f_2542_, v_prio_2535_, v___x_2543_);
v___x_2545_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2546_ = 0;
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 2, v___x_2545_);
lean_ctor_set(v___x_2539_, 1, v_inst_2531_);
lean_ctor_set(v___x_2539_, 0, v___x_2544_);
v___x_2548_ = v___x_2539_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2544_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_inst_2531_);
lean_ctor_set(v_reuseFailAlloc_2549_, 2, v___x_2545_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_ctor_set_uint8(v___x_2548_, sizeof(void*)*3, v___x_2546_);
return v___x_2548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object* v_00_u03b3_2553_, lean_object* v_00_u03b1_2554_, lean_object* v_00_u03b2_2555_, lean_object* v_inst_2556_, lean_object* v_f_2557_, lean_object* v_self_2558_, lean_object* v_other_2559_, lean_object* v_prio_2560_, lean_object* v_sync_2561_){
_start:
{
uint8_t v_sync_boxed_2562_; lean_object* v_res_2563_; 
v_sync_boxed_2562_ = lean_unbox(v_sync_2561_);
v_res_2563_ = l_Lake_Job_zipWith(v_00_u03b3_2553_, v_00_u03b1_2554_, v_00_u03b2_2555_, v_inst_2556_, v_f_2557_, v_self_2558_, v_other_2559_, v_prio_2560_, v_sync_boxed_2562_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object* v___x_2564_, lean_object* v_rx_2565_, lean_object* v_ry_2566_){
_start:
{
lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v___y_2587_; lean_object* v___y_2588_; 
if (lean_obj_tag(v_rx_2565_) == 0)
{
if (lean_obj_tag(v_ry_2566_) == 0)
{
lean_object* v_a_2590_; lean_object* v_a_2591_; lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2614_; 
lean_dec(v___x_2564_);
v_a_2590_ = lean_ctor_get(v_rx_2565_, 0);
lean_inc(v_a_2590_);
v_a_2591_ = lean_ctor_get(v_rx_2565_, 1);
lean_inc(v_a_2591_);
lean_dec_ref_known(v_rx_2565_, 2);
v_a_2592_ = lean_ctor_get(v_ry_2566_, 1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_ry_2566_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v_ry_2566_, 0);
lean_dec(v_unused_2615_);
v___x_2594_ = v_ry_2566_;
v_isShared_2595_ = v_isSharedCheck_2614_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v_ry_2566_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2614_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2596_; lean_object* v_log_2597_; uint8_t v_action_2598_; uint8_t v_wantsRebuild_2599_; lean_object* v_buildTime_2600_; lean_object* v_trace_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2611_; 
lean_inc(v_a_2591_);
v___x_2596_ = l_Lake_JobState_merge(v_a_2591_, v_a_2592_);
v_log_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc_ref(v_log_2597_);
v_action_2598_ = lean_ctor_get_uint8(v___x_2596_, sizeof(void*)*3);
v_wantsRebuild_2599_ = lean_ctor_get_uint8(v___x_2596_, sizeof(void*)*3 + 1);
v_buildTime_2600_ = lean_ctor_get(v___x_2596_, 2);
lean_inc(v_buildTime_2600_);
lean_dec_ref(v___x_2596_);
v_trace_2601_ = lean_ctor_get(v_a_2591_, 1);
v_isSharedCheck_2611_ = !lean_is_exclusive(v_a_2591_);
if (v_isSharedCheck_2611_ == 0)
{
lean_object* v_unused_2612_; lean_object* v_unused_2613_; 
v_unused_2612_ = lean_ctor_get(v_a_2591_, 2);
lean_dec(v_unused_2612_);
v_unused_2613_ = lean_ctor_get(v_a_2591_, 0);
lean_dec(v_unused_2613_);
v___x_2603_ = v_a_2591_;
v_isShared_2604_ = v_isSharedCheck_2611_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_trace_2601_);
lean_dec(v_a_2591_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2611_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
lean_ctor_set(v___x_2603_, 2, v_buildTime_2600_);
lean_ctor_set(v___x_2603_, 0, v_log_2597_);
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_log_2597_);
lean_ctor_set(v_reuseFailAlloc_2610_, 1, v_trace_2601_);
lean_ctor_set(v_reuseFailAlloc_2610_, 2, v_buildTime_2600_);
v___x_2606_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
lean_object* v___x_2608_; 
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3, v_action_2598_);
lean_ctor_set_uint8(v___x_2606_, sizeof(void*)*3 + 1, v_wantsRebuild_2599_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 1, v___x_2606_);
lean_ctor_set(v___x_2594_, 0, v_a_2590_);
v___x_2608_ = v___x_2594_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_a_2590_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v___x_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
}
}
else
{
lean_object* v_a_2616_; 
v_a_2616_ = lean_ctor_get(v_rx_2565_, 1);
lean_inc(v_a_2616_);
lean_dec_ref_known(v_rx_2565_, 2);
v___y_2587_ = v_ry_2566_;
v___y_2588_ = v_a_2616_;
goto v___jp_2586_;
}
}
else
{
lean_object* v_a_2617_; 
v_a_2617_ = lean_ctor_get(v_rx_2565_, 1);
lean_inc(v_a_2617_);
lean_dec_ref(v_rx_2565_);
v___y_2587_ = v_ry_2566_;
v___y_2588_ = v_a_2617_;
goto v___jp_2586_;
}
v___jp_2567_:
{
lean_object* v___x_2570_; lean_object* v_log_2571_; uint8_t v_action_2572_; uint8_t v_wantsRebuild_2573_; lean_object* v_buildTime_2574_; lean_object* v_trace_2575_; lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2583_; 
lean_inc_ref(v___y_2568_);
v___x_2570_ = l_Lake_JobState_merge(v___y_2568_, v___y_2569_);
v_log_2571_ = lean_ctor_get(v___x_2570_, 0);
lean_inc_ref(v_log_2571_);
v_action_2572_ = lean_ctor_get_uint8(v___x_2570_, sizeof(void*)*3);
v_wantsRebuild_2573_ = lean_ctor_get_uint8(v___x_2570_, sizeof(void*)*3 + 1);
v_buildTime_2574_ = lean_ctor_get(v___x_2570_, 2);
lean_inc(v_buildTime_2574_);
lean_dec_ref(v___x_2570_);
v_trace_2575_ = lean_ctor_get(v___y_2568_, 1);
v_isSharedCheck_2583_ = !lean_is_exclusive(v___y_2568_);
if (v_isSharedCheck_2583_ == 0)
{
lean_object* v_unused_2584_; lean_object* v_unused_2585_; 
v_unused_2584_ = lean_ctor_get(v___y_2568_, 2);
lean_dec(v_unused_2584_);
v_unused_2585_ = lean_ctor_get(v___y_2568_, 0);
lean_dec(v_unused_2585_);
v___x_2577_ = v___y_2568_;
v_isShared_2578_ = v_isSharedCheck_2583_;
goto v_resetjp_2576_;
}
else
{
lean_inc(v_trace_2575_);
lean_dec(v___y_2568_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2583_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2580_; 
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 2, v_buildTime_2574_);
lean_ctor_set(v___x_2577_, 0, v_log_2571_);
v___x_2580_ = v___x_2577_;
goto v_reusejp_2579_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v_log_2571_);
lean_ctor_set(v_reuseFailAlloc_2582_, 1, v_trace_2575_);
lean_ctor_set(v_reuseFailAlloc_2582_, 2, v_buildTime_2574_);
v___x_2580_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2579_;
}
v_reusejp_2579_:
{
lean_object* v___x_2581_; 
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*3, v_action_2572_);
lean_ctor_set_uint8(v___x_2580_, sizeof(void*)*3 + 1, v_wantsRebuild_2573_);
v___x_2581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2564_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
return v___x_2581_;
}
}
}
v___jp_2586_:
{
lean_object* v_a_2589_; 
v_a_2589_ = lean_ctor_get(v___y_2587_, 1);
lean_inc(v_a_2589_);
lean_dec_ref(v___y_2587_);
v___y_2568_ = v___y_2588_;
v___y_2569_ = v_a_2589_;
goto v___jp_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1(lean_object* v_other_2618_, lean_object* v___x_2619_, uint8_t v___x_2620_, lean_object* v_rx_2621_){
_start:
{
lean_object* v_task_2622_; lean_object* v___f_2623_; lean_object* v___x_2624_; 
v_task_2622_ = lean_ctor_get(v_other_2618_, 0);
lean_inc_ref(v_task_2622_);
lean_dec_ref(v_other_2618_);
lean_inc(v___x_2619_);
v___f_2623_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2623_, 0, v___x_2619_);
lean_closure_set(v___f_2623_, 1, v_rx_2621_);
v___x_2624_ = lean_task_map(v___f_2623_, v_task_2622_, v___x_2619_, v___x_2620_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object* v_other_2625_, lean_object* v___x_2626_, lean_object* v___x_2627_, lean_object* v_rx_2628_){
_start:
{
uint8_t v___x_253__boxed_2629_; lean_object* v_res_2630_; 
v___x_253__boxed_2629_ = lean_unbox(v___x_2627_);
v_res_2630_ = l_Lake_Job_add___redArg___lam__1(v_other_2625_, v___x_2626_, v___x_253__boxed_2629_, v_rx_2628_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object* v_self_2631_, lean_object* v_other_2632_){
_start:
{
lean_object* v_task_2633_; lean_object* v_kind_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2648_; 
v_task_2633_ = lean_ctor_get(v_self_2631_, 0);
v_kind_2634_ = lean_ctor_get(v_self_2631_, 1);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_self_2631_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v_self_2631_, 2);
lean_dec(v_unused_2649_);
v___x_2636_ = v_self_2631_;
v_isShared_2637_ = v_isSharedCheck_2648_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_kind_2634_);
lean_inc(v_task_2633_);
lean_dec(v_self_2631_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2648_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2638_; uint8_t v___x_2639_; lean_object* v___x_2640_; lean_object* v___f_2641_; uint8_t v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2638_ = lean_unsigned_to_nat(0u);
v___x_2639_ = 0;
v___x_2640_ = lean_box(v___x_2639_);
v___f_2641_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2641_, 0, v_other_2632_);
lean_closure_set(v___f_2641_, 1, v___x_2638_);
lean_closure_set(v___f_2641_, 2, v___x_2640_);
v___x_2642_ = 1;
v___x_2643_ = lean_task_bind(v_task_2633_, v___f_2641_, v___x_2638_, v___x_2642_);
v___x_2644_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2637_ == 0)
{
lean_ctor_set(v___x_2636_, 2, v___x_2644_);
lean_ctor_set(v___x_2636_, 0, v___x_2643_);
v___x_2646_ = v___x_2636_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v___x_2643_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_kind_2634_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_ctor_set_uint8(v___x_2646_, sizeof(void*)*3, v___x_2639_);
return v___x_2646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object* v_00_u03b1_2650_, lean_object* v_00_u03b2_2651_, lean_object* v_self_2652_, lean_object* v_other_2653_){
_start:
{
lean_object* v___x_2654_; 
v___x_2654_ = l_Lake_Job_add___redArg(v_self_2652_, v_other_2653_);
return v___x_2654_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object* v___x_2655_, lean_object* v_rx_2656_, lean_object* v_ry_2657_){
_start:
{
lean_object* v___y_2659_; lean_object* v___y_2660_; lean_object* v___y_2664_; lean_object* v___y_2665_; 
if (lean_obj_tag(v_rx_2656_) == 0)
{
if (lean_obj_tag(v_ry_2657_) == 0)
{
lean_object* v_a_2667_; lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2677_; 
lean_dec(v___x_2655_);
v_a_2667_ = lean_ctor_get(v_rx_2656_, 1);
lean_inc(v_a_2667_);
lean_dec_ref_known(v_rx_2656_, 2);
v_a_2668_ = lean_ctor_get(v_ry_2657_, 1);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_ry_2657_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v_ry_2657_, 0);
lean_dec(v_unused_2678_);
v___x_2670_ = v_ry_2657_;
v_isShared_2671_ = v_isSharedCheck_2677_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v_ry_2657_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2677_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2675_; 
v___x_2672_ = lean_box(0);
v___x_2673_ = l_Lake_JobState_merge(v_a_2667_, v_a_2668_);
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v___x_2673_);
lean_ctor_set(v___x_2670_, 0, v___x_2672_);
v___x_2675_ = v___x_2670_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2672_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v___x_2673_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2679_; 
v_a_2679_ = lean_ctor_get(v_rx_2656_, 1);
lean_inc(v_a_2679_);
lean_dec_ref_known(v_rx_2656_, 2);
v___y_2664_ = v_ry_2657_;
v___y_2665_ = v_a_2679_;
goto v___jp_2663_;
}
}
else
{
lean_object* v_a_2680_; 
v_a_2680_ = lean_ctor_get(v_rx_2656_, 1);
lean_inc(v_a_2680_);
lean_dec_ref(v_rx_2656_);
v___y_2664_ = v_ry_2657_;
v___y_2665_ = v_a_2680_;
goto v___jp_2663_;
}
v___jp_2658_:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___x_2661_ = l_Lake_JobState_merge(v___y_2659_, v___y_2660_);
v___x_2662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2662_, 0, v___x_2655_);
lean_ctor_set(v___x_2662_, 1, v___x_2661_);
return v___x_2662_;
}
v___jp_2663_:
{
lean_object* v_a_2666_; 
v_a_2666_ = lean_ctor_get(v___y_2664_, 1);
lean_inc(v_a_2666_);
lean_dec_ref(v___y_2664_);
v___y_2659_ = v___y_2665_;
v___y_2660_ = v_a_2666_;
goto v___jp_2658_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object* v_other_2681_, lean_object* v___x_2682_, uint8_t v___x_2683_, lean_object* v_rx_2684_){
_start:
{
lean_object* v_task_2685_; lean_object* v___f_2686_; lean_object* v___x_2687_; 
v_task_2685_ = lean_ctor_get(v_other_2681_, 0);
lean_inc_ref(v_task_2685_);
lean_dec_ref(v_other_2681_);
lean_inc(v___x_2682_);
v___f_2686_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2686_, 0, v___x_2682_);
lean_closure_set(v___f_2686_, 1, v_rx_2684_);
v___x_2687_ = lean_task_map(v___f_2686_, v_task_2685_, v___x_2682_, v___x_2683_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object* v_other_2688_, lean_object* v___x_2689_, lean_object* v___x_2690_, lean_object* v_rx_2691_){
_start:
{
uint8_t v___x_142__boxed_2692_; lean_object* v_res_2693_; 
v___x_142__boxed_2692_ = lean_unbox(v___x_2690_);
v_res_2693_ = l_Lake_Job_mix___redArg___lam__1(v_other_2688_, v___x_2689_, v___x_142__boxed_2692_, v_rx_2691_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object* v_self_2694_, lean_object* v_other_2695_){
_start:
{
lean_object* v_task_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2711_; 
v_task_2696_ = lean_ctor_get(v_self_2694_, 0);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_self_2694_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; lean_object* v_unused_2713_; 
v_unused_2712_ = lean_ctor_get(v_self_2694_, 2);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_self_2694_, 1);
lean_dec(v_unused_2713_);
v___x_2698_ = v_self_2694_;
v_isShared_2699_ = v_isSharedCheck_2711_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_task_2696_);
lean_dec(v_self_2694_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2711_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___f_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; lean_object* v___x_2709_; 
v___x_2700_ = l_Lake_instDataKindUnit;
v___x_2701_ = lean_unsigned_to_nat(0u);
v___x_2702_ = 1;
v___x_2703_ = lean_box(v___x_2702_);
v___f_2704_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2704_, 0, v_other_2695_);
lean_closure_set(v___f_2704_, 1, v___x_2701_);
lean_closure_set(v___f_2704_, 2, v___x_2703_);
v___x_2705_ = lean_task_bind(v_task_2696_, v___f_2704_, v___x_2701_, v___x_2702_);
v___x_2706_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2707_ = 0;
if (v_isShared_2699_ == 0)
{
lean_ctor_set(v___x_2698_, 2, v___x_2706_);
lean_ctor_set(v___x_2698_, 1, v___x_2700_);
lean_ctor_set(v___x_2698_, 0, v___x_2705_);
v___x_2709_ = v___x_2698_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v___x_2700_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v___x_2706_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
lean_ctor_set_uint8(v___x_2709_, sizeof(void*)*3, v___x_2707_);
return v___x_2709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object* v_00_u03b1_2714_, lean_object* v_00_u03b2_2715_, lean_object* v_self_2716_, lean_object* v_other_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_Lake_Job_mix___redArg(v_self_2716_, v_other_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(lean_object* v_as_2719_, size_t v_i_2720_, size_t v_stop_2721_, lean_object* v_b_2722_){
_start:
{
uint8_t v___x_2723_; 
v___x_2723_ = lean_usize_dec_eq(v_i_2720_, v_stop_2721_);
if (v___x_2723_ == 0)
{
size_t v___x_2724_; size_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2724_ = ((size_t)1ULL);
v___x_2725_ = lean_usize_sub(v_i_2720_, v___x_2724_);
v___x_2726_ = lean_array_uget_borrowed(v_as_2719_, v___x_2725_);
lean_inc(v___x_2726_);
v___x_2727_ = l_Lake_Job_mix___redArg(v___x_2726_, v_b_2722_);
v_i_2720_ = v___x_2725_;
v_b_2722_ = v___x_2727_;
goto _start;
}
else
{
return v_b_2722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2729_, lean_object* v_i_2730_, lean_object* v_stop_2731_, lean_object* v_b_2732_){
_start:
{
size_t v_i_boxed_2733_; size_t v_stop_boxed_2734_; lean_object* v_res_2735_; 
v_i_boxed_2733_ = lean_unbox_usize(v_i_2730_);
lean_dec(v_i_2730_);
v_stop_boxed_2734_ = lean_unbox_usize(v_stop_2731_);
lean_dec(v_stop_2731_);
v_res_2735_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2729_, v_i_boxed_2733_, v_stop_boxed_2734_, v_b_2732_);
lean_dec_ref(v_as_2729_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(lean_object* v_init_2736_, lean_object* v_l_2737_){
_start:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; 
v___x_2738_ = lean_array_mk(v_l_2737_);
v___x_2739_ = lean_array_get_size(v___x_2738_);
v___x_2740_ = lean_unsigned_to_nat(0u);
v___x_2741_ = lean_nat_dec_lt(v___x_2740_, v___x_2739_);
if (v___x_2741_ == 0)
{
lean_dec_ref(v___x_2738_);
return v_init_2736_;
}
else
{
size_t v___x_2742_; size_t v___x_2743_; lean_object* v___x_2744_; 
v___x_2742_ = lean_usize_of_nat(v___x_2739_);
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v___x_2738_, v___x_2742_, v___x_2743_, v_init_2736_);
lean_dec_ref(v___x_2738_);
return v___x_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object* v_jobs_2745_, lean_object* v_traceCaption_2746_){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; uint8_t v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2747_ = lean_box(0);
v___x_2748_ = lean_box(0);
v___x_2749_ = lean_unsigned_to_nat(0u);
v___x_2750_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2751_ = 0;
v___x_2752_ = 0;
v___x_2753_ = l_Lake_BuildTrace_nil(v_traceCaption_2746_);
v___x_2754_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2754_, 0, v___x_2750_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
lean_ctor_set(v___x_2754_, 2, v___x_2749_);
lean_ctor_set_uint8(v___x_2754_, sizeof(void*)*3, v___x_2751_);
lean_ctor_set_uint8(v___x_2754_, sizeof(void*)*3 + 1, v___x_2752_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2747_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
v___x_2756_ = lean_task_pure(v___x_2755_);
v___x_2757_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2758_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2758_, 0, v___x_2756_);
lean_ctor_set(v___x_2758_, 1, v___x_2748_);
lean_ctor_set(v___x_2758_, 2, v___x_2757_);
lean_ctor_set_uint8(v___x_2758_, sizeof(void*)*3, v___x_2752_);
v___x_2759_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v___x_2758_, v_jobs_2745_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object* v_00_u03b1_2760_, lean_object* v_jobs_2761_, lean_object* v_traceCaption_2762_){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lake_Job_mixList___redArg(v_jobs_2761_, v_traceCaption_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0(lean_object* v_00_u03b1_2764_, lean_object* v_init_2765_, lean_object* v_l_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v_init_2765_, v_l_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(lean_object* v_00_u03b1_2768_, lean_object* v_as_2769_, size_t v_i_2770_, size_t v_stop_2771_, lean_object* v_b_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2769_, v_i_2770_, v_stop_2771_, v_b_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2774_, lean_object* v_as_2775_, lean_object* v_i_2776_, lean_object* v_stop_2777_, lean_object* v_b_2778_){
_start:
{
size_t v_i_boxed_2779_; size_t v_stop_boxed_2780_; lean_object* v_res_2781_; 
v_i_boxed_2779_ = lean_unbox_usize(v_i_2776_);
lean_dec(v_i_2776_);
v_stop_boxed_2780_ = lean_unbox_usize(v_stop_2777_);
lean_dec(v_stop_2777_);
v_res_2781_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(v_00_u03b1_2774_, v_as_2775_, v_i_boxed_2779_, v_stop_boxed_2780_, v_b_2778_);
lean_dec_ref(v_as_2775_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(lean_object* v_as_2782_, size_t v_i_2783_, size_t v_stop_2784_, lean_object* v_b_2785_){
_start:
{
uint8_t v___x_2786_; 
v___x_2786_ = lean_usize_dec_eq(v_i_2783_, v_stop_2784_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; size_t v___x_2789_; size_t v___x_2790_; 
v___x_2787_ = lean_array_uget_borrowed(v_as_2782_, v_i_2783_);
lean_inc(v___x_2787_);
v___x_2788_ = l_Lake_Job_mix___redArg(v_b_2785_, v___x_2787_);
v___x_2789_ = ((size_t)1ULL);
v___x_2790_ = lean_usize_add(v_i_2783_, v___x_2789_);
v_i_2783_ = v___x_2790_;
v_b_2785_ = v___x_2788_;
goto _start;
}
else
{
return v_b_2785_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg___boxed(lean_object* v_as_2792_, lean_object* v_i_2793_, lean_object* v_stop_2794_, lean_object* v_b_2795_){
_start:
{
size_t v_i_boxed_2796_; size_t v_stop_boxed_2797_; lean_object* v_res_2798_; 
v_i_boxed_2796_ = lean_unbox_usize(v_i_2793_);
lean_dec(v_i_2793_);
v_stop_boxed_2797_ = lean_unbox_usize(v_stop_2794_);
lean_dec(v_stop_2794_);
v_res_2798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2792_, v_i_boxed_2796_, v_stop_boxed_2797_, v_b_2795_);
lean_dec_ref(v_as_2792_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object* v_jobs_2799_, lean_object* v_traceCaption_2800_){
_start:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; uint8_t v___x_2805_; uint8_t v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_box(0);
v___x_2803_ = lean_unsigned_to_nat(0u);
v___x_2804_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2805_ = 0;
v___x_2806_ = 0;
v___x_2807_ = l_Lake_BuildTrace_nil(v_traceCaption_2800_);
v___x_2808_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2808_, 0, v___x_2804_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
lean_ctor_set(v___x_2808_, 2, v___x_2803_);
lean_ctor_set_uint8(v___x_2808_, sizeof(void*)*3, v___x_2805_);
lean_ctor_set_uint8(v___x_2808_, sizeof(void*)*3 + 1, v___x_2806_);
v___x_2809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2809_, 0, v___x_2801_);
lean_ctor_set(v___x_2809_, 1, v___x_2808_);
v___x_2810_ = lean_task_pure(v___x_2809_);
v___x_2811_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2812_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2812_, 0, v___x_2810_);
lean_ctor_set(v___x_2812_, 1, v___x_2802_);
lean_ctor_set(v___x_2812_, 2, v___x_2811_);
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*3, v___x_2806_);
v___x_2813_ = lean_array_get_size(v_jobs_2799_);
v___x_2814_ = lean_nat_dec_lt(v___x_2803_, v___x_2813_);
if (v___x_2814_ == 0)
{
return v___x_2812_;
}
else
{
uint8_t v___x_2815_; 
v___x_2815_ = lean_nat_dec_le(v___x_2813_, v___x_2813_);
if (v___x_2815_ == 0)
{
if (v___x_2814_ == 0)
{
return v___x_2812_;
}
else
{
size_t v___x_2816_; size_t v___x_2817_; lean_object* v___x_2818_; 
v___x_2816_ = ((size_t)0ULL);
v___x_2817_ = lean_usize_of_nat(v___x_2813_);
v___x_2818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2799_, v___x_2816_, v___x_2817_, v___x_2812_);
return v___x_2818_;
}
}
else
{
size_t v___x_2819_; size_t v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = ((size_t)0ULL);
v___x_2820_ = lean_usize_of_nat(v___x_2813_);
v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2799_, v___x_2819_, v___x_2820_, v___x_2812_);
return v___x_2821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object* v_jobs_2822_, lean_object* v_traceCaption_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_Lake_Job_mixArray___redArg(v_jobs_2822_, v_traceCaption_2823_);
lean_dec_ref(v_jobs_2822_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object* v_00_u03b1_2825_, lean_object* v_jobs_2826_, lean_object* v_traceCaption_2827_){
_start:
{
lean_object* v___x_2828_; 
v___x_2828_ = l_Lake_Job_mixArray___redArg(v_jobs_2826_, v_traceCaption_2827_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object* v_00_u03b1_2829_, lean_object* v_jobs_2830_, lean_object* v_traceCaption_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l_Lake_Job_mixArray(v_00_u03b1_2829_, v_jobs_2830_, v_traceCaption_2831_);
lean_dec_ref(v_jobs_2830_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_object* v_00_u03b1_2833_, lean_object* v_as_2834_, size_t v_i_2835_, size_t v_stop_2836_, lean_object* v_b_2837_){
_start:
{
lean_object* v___x_2838_; 
v___x_2838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2834_, v_i_2835_, v_stop_2836_, v_b_2837_);
return v___x_2838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(lean_object* v_00_u03b1_2839_, lean_object* v_as_2840_, lean_object* v_i_2841_, lean_object* v_stop_2842_, lean_object* v_b_2843_){
_start:
{
size_t v_i_boxed_2844_; size_t v_stop_boxed_2845_; lean_object* v_res_2846_; 
v_i_boxed_2844_ = lean_unbox_usize(v_i_2841_);
lean_dec(v_i_2841_);
v_stop_boxed_2845_ = lean_unbox_usize(v_stop_2842_);
lean_dec(v_stop_2842_);
v_res_2846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(v_00_u03b1_2839_, v_as_2840_, v_i_boxed_2844_, v_stop_boxed_2845_, v_b_2843_);
lean_dec_ref(v_as_2840_);
return v_res_2846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object* v___x_2847_, lean_object* v_rx_2848_, lean_object* v_ry_2849_){
_start:
{
lean_object* v___y_2851_; lean_object* v___y_2852_; lean_object* v___y_2856_; lean_object* v___y_2857_; 
if (lean_obj_tag(v_rx_2848_) == 0)
{
if (lean_obj_tag(v_ry_2849_) == 0)
{
lean_object* v_a_2859_; lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2877_; 
lean_dec(v___x_2847_);
v_a_2859_ = lean_ctor_get(v_rx_2848_, 0);
v_a_2860_ = lean_ctor_get(v_rx_2848_, 1);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_rx_2848_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2862_ = v_rx_2848_;
v_isShared_2863_ = v_isSharedCheck_2877_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_inc(v_a_2859_);
lean_dec(v_rx_2848_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2877_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v_a_2864_; lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2876_; 
v_a_2864_ = lean_ctor_get(v_ry_2849_, 0);
v_a_2865_ = lean_ctor_get(v_ry_2849_, 1);
v_isSharedCheck_2876_ = !lean_is_exclusive(v_ry_2849_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2867_ = v_ry_2849_;
v_isShared_2868_ = v_isSharedCheck_2876_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_inc(v_a_2864_);
lean_dec(v_ry_2849_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2876_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2863_ == 0)
{
lean_ctor_set_tag(v___x_2862_, 1);
lean_ctor_set(v___x_2862_, 1, v_a_2864_);
v___x_2870_ = v___x_2862_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2859_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_a_2864_);
v___x_2870_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2871_ = l_Lake_JobState_merge(v_a_2860_, v_a_2865_);
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v___x_2871_);
lean_ctor_set(v___x_2867_, 0, v___x_2870_);
v___x_2873_ = v___x_2867_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2874_, 1, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
else
{
lean_object* v_a_2878_; 
v_a_2878_ = lean_ctor_get(v_rx_2848_, 1);
lean_inc(v_a_2878_);
lean_dec_ref_known(v_rx_2848_, 2);
v___y_2856_ = v_ry_2849_;
v___y_2857_ = v_a_2878_;
goto v___jp_2855_;
}
}
else
{
lean_object* v_a_2879_; 
v_a_2879_ = lean_ctor_get(v_rx_2848_, 1);
lean_inc(v_a_2879_);
lean_dec_ref(v_rx_2848_);
v___y_2856_ = v_ry_2849_;
v___y_2857_ = v_a_2879_;
goto v___jp_2855_;
}
v___jp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = l_Lake_JobState_merge(v___y_2851_, v___y_2852_);
v___x_2854_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2847_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
return v___x_2854_;
}
v___jp_2855_:
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___y_2856_, 1);
lean_inc(v_a_2858_);
lean_dec_ref(v___y_2856_);
v___y_2851_ = v___y_2857_;
v___y_2852_ = v_a_2858_;
goto v___jp_2850_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object* v_b_2880_, lean_object* v___x_2881_, uint8_t v___x_2882_, lean_object* v_rx_2883_){
_start:
{
lean_object* v_task_2884_; lean_object* v___f_2885_; lean_object* v___x_2886_; 
v_task_2884_ = lean_ctor_get(v_b_2880_, 0);
lean_inc_ref(v_task_2884_);
lean_dec_ref(v_b_2880_);
lean_inc(v___x_2881_);
v___f_2885_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2885_, 0, v___x_2881_);
lean_closure_set(v___f_2885_, 1, v_rx_2883_);
v___x_2886_ = lean_task_map(v___f_2885_, v_task_2884_, v___x_2881_, v___x_2882_);
return v___x_2886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_b_2887_, lean_object* v___x_2888_, lean_object* v___x_2889_, lean_object* v_rx_2890_){
_start:
{
uint8_t v___x_478__boxed_2891_; lean_object* v_res_2892_; 
v___x_478__boxed_2891_ = lean_unbox(v___x_2889_);
v_res_2892_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_2887_, v___x_2888_, v___x_478__boxed_2891_, v_rx_2890_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(lean_object* v_as_2893_, size_t v_i_2894_, size_t v_stop_2895_, lean_object* v_b_2896_){
_start:
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_usize_dec_eq(v_i_2894_, v_stop_2895_);
if (v___x_2897_ == 0)
{
size_t v___x_2898_; size_t v___x_2899_; lean_object* v___x_2900_; lean_object* v_task_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2916_; 
v___x_2898_ = ((size_t)1ULL);
v___x_2899_ = lean_usize_sub(v_i_2894_, v___x_2898_);
v___x_2900_ = lean_array_uget(v_as_2893_, v___x_2899_);
v_task_2901_ = lean_ctor_get(v___x_2900_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2900_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; lean_object* v_unused_2918_; 
v_unused_2917_ = lean_ctor_get(v___x_2900_, 2);
lean_dec(v_unused_2917_);
v_unused_2918_ = lean_ctor_get(v___x_2900_, 1);
lean_dec(v_unused_2918_);
v___x_2903_ = v___x_2900_;
v_isShared_2904_ = v_isSharedCheck_2916_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_task_2901_);
lean_dec(v___x_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2916_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; lean_object* v___x_2908_; lean_object* v___f_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_unsigned_to_nat(0u);
v___x_2907_ = 1;
v___x_2908_ = lean_box(v___x_2907_);
v___f_2909_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2909_, 0, v_b_2896_);
lean_closure_set(v___f_2909_, 1, v___x_2906_);
lean_closure_set(v___f_2909_, 2, v___x_2908_);
v___x_2910_ = lean_task_bind(v_task_2901_, v___f_2909_, v___x_2906_, v___x_2907_);
v___x_2911_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 2, v___x_2911_);
lean_ctor_set(v___x_2903_, 1, v___x_2905_);
lean_ctor_set(v___x_2903_, 0, v___x_2910_);
v___x_2913_ = v___x_2903_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v___x_2905_);
lean_ctor_set(v_reuseFailAlloc_2915_, 2, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_ctor_set_uint8(v___x_2913_, sizeof(void*)*3, v___x_2897_);
v_i_2894_ = v___x_2899_;
v_b_2896_ = v___x_2913_;
goto _start;
}
}
}
else
{
return v_b_2896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2919_, lean_object* v_i_2920_, lean_object* v_stop_2921_, lean_object* v_b_2922_){
_start:
{
size_t v_i_boxed_2923_; size_t v_stop_boxed_2924_; lean_object* v_res_2925_; 
v_i_boxed_2923_ = lean_unbox_usize(v_i_2920_);
lean_dec(v_i_2920_);
v_stop_boxed_2924_ = lean_unbox_usize(v_stop_2921_);
lean_dec(v_stop_2921_);
v_res_2925_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_2919_, v_i_boxed_2923_, v_stop_boxed_2924_, v_b_2922_);
lean_dec_ref(v_as_2919_);
return v_res_2925_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(lean_object* v_init_2926_, lean_object* v_l_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; uint8_t v___x_2931_; 
v___x_2928_ = lean_array_mk(v_l_2927_);
v___x_2929_ = lean_array_get_size(v___x_2928_);
v___x_2930_ = lean_unsigned_to_nat(0u);
v___x_2931_ = lean_nat_dec_lt(v___x_2930_, v___x_2929_);
if (v___x_2931_ == 0)
{
lean_dec_ref(v___x_2928_);
return v_init_2926_;
}
else
{
size_t v___x_2932_; size_t v___x_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_usize_of_nat(v___x_2929_);
v___x_2933_ = ((size_t)0ULL);
v___x_2934_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v___x_2928_, v___x_2932_, v___x_2933_, v_init_2926_);
lean_dec_ref(v___x_2928_);
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object* v_jobs_2935_, lean_object* v_traceCaption_2936_){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; uint8_t v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2937_ = lean_box(0);
v___x_2938_ = lean_box(0);
v___x_2939_ = lean_unsigned_to_nat(0u);
v___x_2940_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2941_ = 0;
v___x_2942_ = 0;
v___x_2943_ = l_Lake_BuildTrace_nil(v_traceCaption_2936_);
v___x_2944_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2944_, 0, v___x_2940_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
lean_ctor_set(v___x_2944_, 2, v___x_2939_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*3, v___x_2941_);
lean_ctor_set_uint8(v___x_2944_, sizeof(void*)*3 + 1, v___x_2942_);
v___x_2945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2945_, 0, v___x_2937_);
lean_ctor_set(v___x_2945_, 1, v___x_2944_);
v___x_2946_ = lean_task_pure(v___x_2945_);
v___x_2947_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2948_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2948_, 0, v___x_2946_);
lean_ctor_set(v___x_2948_, 1, v___x_2938_);
lean_ctor_set(v___x_2948_, 2, v___x_2947_);
lean_ctor_set_uint8(v___x_2948_, sizeof(void*)*3, v___x_2942_);
v___x_2949_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v___x_2948_, v_jobs_2935_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object* v_00_u03b1_2950_, lean_object* v_jobs_2951_, lean_object* v_traceCaption_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lake_Job_collectList___redArg(v_jobs_2951_, v_traceCaption_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0(lean_object* v_00_u03b1_2954_, lean_object* v_init_2955_, lean_object* v_l_2956_){
_start:
{
lean_object* v___x_2957_; 
v___x_2957_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v_init_2955_, v_l_2956_);
return v___x_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_object* v_00_u03b1_2958_, lean_object* v_as_2959_, size_t v_i_2960_, size_t v_stop_2961_, lean_object* v_b_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_2959_, v_i_2960_, v_stop_2961_, v_b_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2964_, lean_object* v_as_2965_, lean_object* v_i_2966_, lean_object* v_stop_2967_, lean_object* v_b_2968_){
_start:
{
size_t v_i_boxed_2969_; size_t v_stop_boxed_2970_; lean_object* v_res_2971_; 
v_i_boxed_2969_ = lean_unbox_usize(v_i_2966_);
lean_dec(v_i_2966_);
v_stop_boxed_2970_ = lean_unbox_usize(v_stop_2967_);
lean_dec(v_stop_2967_);
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(v_00_u03b1_2964_, v_as_2965_, v_i_boxed_2969_, v_stop_boxed_2970_, v_b_2968_);
lean_dec_ref(v_as_2965_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object* v___x_2972_, lean_object* v_rx_2973_, lean_object* v_ry_2974_){
_start:
{
lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2981_; lean_object* v___y_2982_; 
if (lean_obj_tag(v_rx_2973_) == 0)
{
if (lean_obj_tag(v_ry_2974_) == 0)
{
lean_object* v_a_2984_; lean_object* v_a_2985_; lean_object* v_a_2986_; lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2996_; 
lean_dec(v___x_2972_);
v_a_2984_ = lean_ctor_get(v_rx_2973_, 0);
lean_inc(v_a_2984_);
v_a_2985_ = lean_ctor_get(v_rx_2973_, 1);
lean_inc(v_a_2985_);
lean_dec_ref_known(v_rx_2973_, 2);
v_a_2986_ = lean_ctor_get(v_ry_2974_, 0);
v_a_2987_ = lean_ctor_get(v_ry_2974_, 1);
v_isSharedCheck_2996_ = !lean_is_exclusive(v_ry_2974_);
if (v_isSharedCheck_2996_ == 0)
{
v___x_2989_ = v_ry_2974_;
v_isShared_2990_ = v_isSharedCheck_2996_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_inc(v_a_2986_);
lean_dec(v_ry_2974_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2996_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2994_; 
v___x_2991_ = lean_array_push(v_a_2984_, v_a_2986_);
v___x_2992_ = l_Lake_JobState_merge(v_a_2985_, v_a_2987_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 1, v___x_2992_);
lean_ctor_set(v___x_2989_, 0, v___x_2991_);
v___x_2994_ = v___x_2989_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2991_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
return v___x_2994_;
}
}
}
else
{
lean_object* v_a_2997_; 
v_a_2997_ = lean_ctor_get(v_rx_2973_, 1);
lean_inc(v_a_2997_);
lean_dec_ref_known(v_rx_2973_, 2);
v___y_2981_ = v_ry_2974_;
v___y_2982_ = v_a_2997_;
goto v___jp_2980_;
}
}
else
{
lean_object* v_a_2998_; 
v_a_2998_ = lean_ctor_get(v_rx_2973_, 1);
lean_inc(v_a_2998_);
lean_dec_ref(v_rx_2973_);
v___y_2981_ = v_ry_2974_;
v___y_2982_ = v_a_2998_;
goto v___jp_2980_;
}
v___jp_2975_:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = l_Lake_JobState_merge(v___y_2976_, v___y_2977_);
v___x_2979_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2972_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
return v___x_2979_;
}
v___jp_2980_:
{
lean_object* v_a_2983_; 
v_a_2983_ = lean_ctor_get(v___y_2981_, 1);
lean_inc(v_a_2983_);
lean_dec_ref(v___y_2981_);
v___y_2976_ = v___y_2982_;
v___y_2977_ = v_a_2983_;
goto v___jp_2975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object* v___x_2999_, lean_object* v___x_3000_, uint8_t v___x_3001_, lean_object* v_rx_3002_){
_start:
{
lean_object* v_task_3003_; lean_object* v___f_3004_; lean_object* v___x_3005_; 
v_task_3003_ = lean_ctor_get(v___x_2999_, 0);
lean_inc_ref(v_task_3003_);
lean_dec_ref(v___x_2999_);
lean_inc(v___x_3000_);
v___f_3004_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3004_, 0, v___x_3000_);
lean_closure_set(v___f_3004_, 1, v_rx_3002_);
v___x_3005_ = lean_task_map(v___f_3004_, v_task_3003_, v___x_3000_, v___x_3001_);
return v___x_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object* v___x_3006_, lean_object* v___x_3007_, lean_object* v___x_3008_, lean_object* v_rx_3009_){
_start:
{
uint8_t v___x_414__boxed_3010_; lean_object* v_res_3011_; 
v___x_414__boxed_3010_ = lean_unbox(v___x_3008_);
v_res_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_3006_, v___x_3007_, v___x_414__boxed_3010_, v_rx_3009_);
return v_res_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(lean_object* v_as_3012_, size_t v_i_3013_, size_t v_stop_3014_, lean_object* v_b_3015_){
_start:
{
uint8_t v___x_3016_; 
v___x_3016_ = lean_usize_dec_eq(v_i_3013_, v_stop_3014_);
if (v___x_3016_ == 0)
{
lean_object* v_task_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3035_; 
v_task_3017_ = lean_ctor_get(v_b_3015_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_b_3015_);
if (v_isSharedCheck_3035_ == 0)
{
lean_object* v_unused_3036_; lean_object* v_unused_3037_; 
v_unused_3036_ = lean_ctor_get(v_b_3015_, 2);
lean_dec(v_unused_3036_);
v_unused_3037_ = lean_ctor_get(v_b_3015_, 1);
lean_dec(v_unused_3037_);
v___x_3019_ = v_b_3015_;
v_isShared_3020_ = v_isSharedCheck_3035_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_task_3017_);
lean_dec(v_b_3015_);
v___x_3019_ = lean_box(0);
v_isShared_3020_ = v_isSharedCheck_3035_;
goto v_resetjp_3018_;
}
v_resetjp_3018_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; uint8_t v___x_3024_; lean_object* v___x_3025_; lean_object* v___f_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3030_; 
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_array_uget_borrowed(v_as_3012_, v_i_3013_);
v___x_3023_ = lean_unsigned_to_nat(0u);
v___x_3024_ = 1;
v___x_3025_ = lean_box(v___x_3024_);
lean_inc(v___x_3022_);
v___f_3026_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3026_, 0, v___x_3022_);
lean_closure_set(v___f_3026_, 1, v___x_3023_);
lean_closure_set(v___f_3026_, 2, v___x_3025_);
v___x_3027_ = lean_task_bind(v_task_3017_, v___f_3026_, v___x_3023_, v___x_3024_);
v___x_3028_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_3020_ == 0)
{
lean_ctor_set(v___x_3019_, 2, v___x_3028_);
lean_ctor_set(v___x_3019_, 1, v___x_3021_);
lean_ctor_set(v___x_3019_, 0, v___x_3027_);
v___x_3030_ = v___x_3019_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v___x_3021_);
lean_ctor_set(v_reuseFailAlloc_3034_, 2, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
size_t v___x_3031_; size_t v___x_3032_; 
lean_ctor_set_uint8(v___x_3030_, sizeof(void*)*3, v___x_3016_);
v___x_3031_ = ((size_t)1ULL);
v___x_3032_ = lean_usize_add(v_i_3013_, v___x_3031_);
v_i_3013_ = v___x_3032_;
v_b_3015_ = v___x_3030_;
goto _start;
}
}
}
else
{
return v_b_3015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(lean_object* v_as_3038_, lean_object* v_i_3039_, lean_object* v_stop_3040_, lean_object* v_b_3041_){
_start:
{
size_t v_i_boxed_3042_; size_t v_stop_boxed_3043_; lean_object* v_res_3044_; 
v_i_boxed_3042_ = lean_unbox_usize(v_i_3039_);
lean_dec(v_i_3039_);
v_stop_boxed_3043_ = lean_unbox_usize(v_stop_3040_);
lean_dec(v_stop_3040_);
v_res_3044_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3038_, v_i_boxed_3042_, v_stop_boxed_3043_, v_b_3041_);
lean_dec_ref(v_as_3038_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object* v_jobs_3045_, lean_object* v_traceCaption_3046_){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; uint8_t v___x_3052_; uint8_t v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; uint8_t v___x_3060_; 
v___x_3047_ = lean_array_get_size(v_jobs_3045_);
v___x_3048_ = lean_mk_empty_array_with_capacity(v___x_3047_);
v___x_3049_ = lean_box(0);
v___x_3050_ = lean_unsigned_to_nat(0u);
v___x_3051_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3052_ = 0;
v___x_3053_ = 0;
v___x_3054_ = l_Lake_BuildTrace_nil(v_traceCaption_3046_);
v___x_3055_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3055_, 0, v___x_3051_);
lean_ctor_set(v___x_3055_, 1, v___x_3054_);
lean_ctor_set(v___x_3055_, 2, v___x_3050_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*3, v___x_3052_);
lean_ctor_set_uint8(v___x_3055_, sizeof(void*)*3 + 1, v___x_3053_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3048_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = lean_task_pure(v___x_3056_);
v___x_3058_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3059_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3059_, 0, v___x_3057_);
lean_ctor_set(v___x_3059_, 1, v___x_3049_);
lean_ctor_set(v___x_3059_, 2, v___x_3058_);
lean_ctor_set_uint8(v___x_3059_, sizeof(void*)*3, v___x_3053_);
v___x_3060_ = lean_nat_dec_lt(v___x_3050_, v___x_3047_);
if (v___x_3060_ == 0)
{
return v___x_3059_;
}
else
{
uint8_t v___x_3061_; 
v___x_3061_ = lean_nat_dec_le(v___x_3047_, v___x_3047_);
if (v___x_3061_ == 0)
{
if (v___x_3060_ == 0)
{
return v___x_3059_;
}
else
{
size_t v___x_3062_; size_t v___x_3063_; lean_object* v___x_3064_; 
v___x_3062_ = ((size_t)0ULL);
v___x_3063_ = lean_usize_of_nat(v___x_3047_);
v___x_3064_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_3045_, v___x_3062_, v___x_3063_, v___x_3059_);
return v___x_3064_;
}
}
else
{
size_t v___x_3065_; size_t v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = ((size_t)0ULL);
v___x_3066_ = lean_usize_of_nat(v___x_3047_);
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_3045_, v___x_3065_, v___x_3066_, v___x_3059_);
return v___x_3067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object* v_jobs_3068_, lean_object* v_traceCaption_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Lake_Job_collectArray___redArg(v_jobs_3068_, v_traceCaption_3069_);
lean_dec_ref(v_jobs_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object* v_00_u03b1_3071_, lean_object* v_jobs_3072_, lean_object* v_traceCaption_3073_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lake_Job_collectArray___redArg(v_jobs_3072_, v_traceCaption_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object* v_00_u03b1_3075_, lean_object* v_jobs_3076_, lean_object* v_traceCaption_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Lake_Job_collectArray(v_00_u03b1_3075_, v_jobs_3076_, v_traceCaption_3077_);
lean_dec_ref(v_jobs_3076_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_object* v_00_u03b1_3079_, lean_object* v_as_3080_, size_t v_i_3081_, size_t v_stop_3082_, lean_object* v_b_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3080_, v_i_3081_, v_stop_3082_, v_b_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(lean_object* v_00_u03b1_3085_, lean_object* v_as_3086_, lean_object* v_i_3087_, lean_object* v_stop_3088_, lean_object* v_b_3089_){
_start:
{
size_t v_i_boxed_3090_; size_t v_stop_boxed_3091_; lean_object* v_res_3092_; 
v_i_boxed_3090_ = lean_unbox_usize(v_i_3087_);
lean_dec(v_i_3087_);
v_stop_boxed_3091_ = lean_unbox_usize(v_stop_3088_);
lean_dec(v_stop_3088_);
v_res_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(v_00_u03b1_3085_, v_as_3086_, v_i_boxed_3090_, v_stop_boxed_3091_, v_b_3089_);
lean_dec_ref(v_as_3086_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(lean_object* v_00_u03b1_3093_, lean_object* v_inst_3094_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = lean_box(0);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0(lean_object* v___x_3096_, lean_object* v_rx_3097_, lean_object* v_i_3098_, lean_object* v_ry_3099_){
_start:
{
lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3106_; lean_object* v___y_3107_; 
if (lean_obj_tag(v_rx_3097_) == 0)
{
if (lean_obj_tag(v_ry_3099_) == 0)
{
lean_object* v_a_3109_; lean_object* v_a_3110_; lean_object* v_a_3111_; lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v___x_3096_);
v_a_3109_ = lean_ctor_get(v_rx_3097_, 0);
lean_inc(v_a_3109_);
v_a_3110_ = lean_ctor_get(v_rx_3097_, 1);
lean_inc(v_a_3110_);
lean_dec_ref_known(v_rx_3097_, 2);
v_a_3111_ = lean_ctor_get(v_ry_3099_, 0);
v_a_3112_ = lean_ctor_get(v_ry_3099_, 1);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_ry_3099_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3114_ = v_ry_3099_;
v_isShared_3115_ = v_isSharedCheck_3121_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_inc(v_a_3111_);
lean_dec(v_ry_3099_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3121_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3119_; 
v___x_3116_ = lean_array_fset(v_a_3109_, v_i_3098_, v_a_3111_);
v___x_3117_ = l_Lake_JobState_merge(v_a_3110_, v_a_3112_);
if (v_isShared_3115_ == 0)
{
lean_ctor_set(v___x_3114_, 1, v___x_3117_);
lean_ctor_set(v___x_3114_, 0, v___x_3116_);
v___x_3119_ = v___x_3114_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3116_);
lean_ctor_set(v_reuseFailAlloc_3120_, 1, v___x_3117_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
else
{
lean_object* v_a_3122_; 
v_a_3122_ = lean_ctor_get(v_rx_3097_, 1);
lean_inc(v_a_3122_);
lean_dec_ref_known(v_rx_3097_, 2);
v___y_3106_ = v_ry_3099_;
v___y_3107_ = v_a_3122_;
goto v___jp_3105_;
}
}
else
{
lean_object* v_a_3123_; 
v_a_3123_ = lean_ctor_get(v_rx_3097_, 1);
lean_inc(v_a_3123_);
lean_dec_ref(v_rx_3097_);
v___y_3106_ = v_ry_3099_;
v___y_3107_ = v_a_3123_;
goto v___jp_3105_;
}
v___jp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = l_Lake_JobState_merge(v___y_3101_, v___y_3102_);
v___x_3104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3096_);
lean_ctor_set(v___x_3104_, 1, v___x_3103_);
return v___x_3104_;
}
v___jp_3105_:
{
lean_object* v_a_3108_; 
v_a_3108_ = lean_ctor_get(v___y_3106_, 1);
lean_inc(v_a_3108_);
lean_dec_ref(v___y_3106_);
v___y_3101_ = v___y_3107_;
v___y_3102_ = v_a_3108_;
goto v___jp_3100_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0___boxed(lean_object* v___x_3124_, lean_object* v_rx_3125_, lean_object* v_i_3126_, lean_object* v_ry_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_Lake_Job_collectVector___redArg___lam__0(v___x_3124_, v_rx_3125_, v_i_3126_, v_ry_3127_);
lean_dec(v_i_3126_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1(lean_object* v___x_3129_, lean_object* v___x_3130_, lean_object* v_i_3131_, uint8_t v___x_3132_, lean_object* v_rx_3133_){
_start:
{
lean_object* v_task_3134_; lean_object* v___f_3135_; lean_object* v___x_3136_; 
v_task_3134_ = lean_ctor_get(v___x_3129_, 0);
lean_inc_ref(v_task_3134_);
lean_dec_ref(v___x_3129_);
lean_inc(v___x_3130_);
v___f_3135_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3135_, 0, v___x_3130_);
lean_closure_set(v___f_3135_, 1, v_rx_3133_);
lean_closure_set(v___f_3135_, 2, v_i_3131_);
v___x_3136_ = lean_task_map(v___f_3135_, v_task_3134_, v___x_3130_, v___x_3132_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1___boxed(lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v_i_3139_, lean_object* v___x_3140_, lean_object* v_rx_3141_){
_start:
{
uint8_t v___x_191__boxed_3142_; lean_object* v_res_3143_; 
v___x_191__boxed_3142_ = lean_unbox(v___x_3140_);
v_res_3143_ = l_Lake_Job_collectVector___redArg___lam__1(v___x_3137_, v___x_3138_, v_i_3139_, v___x_191__boxed_3142_, v_rx_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2(lean_object* v_jobs_3144_, lean_object* v___x_3145_, lean_object* v_i_3146_, lean_object* v_h_3147_, lean_object* v_job_3148_){
_start:
{
lean_object* v_task_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3164_; 
v_task_3149_ = lean_ctor_get(v_job_3148_, 0);
v_isSharedCheck_3164_ = !lean_is_exclusive(v_job_3148_);
if (v_isSharedCheck_3164_ == 0)
{
lean_object* v_unused_3165_; lean_object* v_unused_3166_; 
v_unused_3165_ = lean_ctor_get(v_job_3148_, 2);
lean_dec(v_unused_3165_);
v_unused_3166_ = lean_ctor_get(v_job_3148_, 1);
lean_dec(v_unused_3166_);
v___x_3151_ = v_job_3148_;
v_isShared_3152_ = v_isSharedCheck_3164_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_task_3149_);
lean_dec(v_job_3148_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3164_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3162_; 
v___x_3153_ = lean_array_fget_borrowed(v_jobs_3144_, v_i_3146_);
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = 1;
v___x_3156_ = lean_box(v___x_3155_);
lean_inc(v___x_3153_);
v___f_3157_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3157_, 0, v___x_3153_);
lean_closure_set(v___f_3157_, 1, v___x_3154_);
lean_closure_set(v___f_3157_, 2, v_i_3146_);
lean_closure_set(v___f_3157_, 3, v___x_3156_);
v___x_3158_ = lean_task_bind(v_task_3149_, v___f_3157_, v___x_3154_, v___x_3155_);
v___x_3159_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3160_ = 0;
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 2, v___x_3159_);
lean_ctor_set(v___x_3151_, 1, v___x_3145_);
lean_ctor_set(v___x_3151_, 0, v___x_3158_);
v___x_3162_ = v___x_3151_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v___x_3145_);
lean_ctor_set(v_reuseFailAlloc_3163_, 2, v___x_3159_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
lean_ctor_set_uint8(v___x_3162_, sizeof(void*)*3, v___x_3160_);
return v___x_3162_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2___boxed(lean_object* v_jobs_3167_, lean_object* v___x_3168_, lean_object* v_i_3169_, lean_object* v_h_3170_, lean_object* v_job_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_Lake_Job_collectVector___redArg___lam__2(v_jobs_3167_, v___x_3168_, v_i_3169_, v_h_3170_, v_job_3171_);
lean_dec_ref(v_jobs_3167_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg(lean_object* v_n_3173_, lean_object* v_jobs_3174_, lean_object* v_traceCaption_3175_){
_start:
{
lean_object* v_placeholder_3176_; lean_object* v___x_3177_; lean_object* v___f_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; uint8_t v___x_3182_; uint8_t v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; 
v_placeholder_3176_ = lean_box(0);
v___x_3177_ = lean_box(0);
v___f_3178_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3178_, 0, v_jobs_3174_);
lean_closure_set(v___f_3178_, 1, v___x_3177_);
lean_inc_n(v_n_3173_, 2);
v___x_3179_ = lean_mk_array(v_n_3173_, v_placeholder_3176_);
v___x_3180_ = lean_unsigned_to_nat(0u);
v___x_3181_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3182_ = 0;
v___x_3183_ = 0;
v___x_3184_ = l_Lake_BuildTrace_nil(v_traceCaption_3175_);
v___x_3185_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3185_, 0, v___x_3181_);
lean_ctor_set(v___x_3185_, 1, v___x_3184_);
lean_ctor_set(v___x_3185_, 2, v___x_3180_);
lean_ctor_set_uint8(v___x_3185_, sizeof(void*)*3, v___x_3182_);
lean_ctor_set_uint8(v___x_3185_, sizeof(void*)*3 + 1, v___x_3183_);
v___x_3186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3179_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_task_pure(v___x_3186_);
v___x_3188_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3189_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3189_, 0, v___x_3187_);
lean_ctor_set(v___x_3189_, 1, v___x_3177_);
lean_ctor_set(v___x_3189_, 2, v___x_3188_);
lean_ctor_set_uint8(v___x_3189_, sizeof(void*)*3, v___x_3183_);
v___x_3190_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3173_, v___f_3178_, v_n_3173_, lean_box(0), v___x_3189_);
lean_dec(v_n_3173_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector(lean_object* v_n_3191_, lean_object* v_00_u03b1_3192_, lean_object* v_inst_3193_, lean_object* v_jobs_3194_, lean_object* v_traceCaption_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Lake_Job_collectVector___redArg(v_n_3191_, v_jobs_3194_, v_traceCaption_3195_);
return v___x_3196_;
}
}
lean_object* runtime_initialize_Lake_Build_Fetch(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instMonadStateOfJobStateJobM = _init_l_Lake_instMonadStateOfJobStateJobM();
lean_mark_persistent(l_Lake_instMonadStateOfJobStateJobM);
l_Lake_instAlternativeJobM = _init_l_Lake_instAlternativeJobM();
lean_mark_persistent(l_Lake_instAlternativeJobM);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Build_Job_Monad(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Build_Fetch(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Job_Monad(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Fetch(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Build_Job_Monad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Build_Job_Monad(builtin);
}
#ifdef __cplusplus
}
#endif
