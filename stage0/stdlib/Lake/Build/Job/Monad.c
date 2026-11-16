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
lean_object* lean_io_wait(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
uint8_t l_IO_CancelToken_isSet(lean_object*);
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
lean_object* lean_io_map_task(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instMonadLift___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lake_instMonadStateOfJobStateJobM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_instMonadStateOfJobStateJobM___closed__3 = (const lean_object*)&l_Lake_instMonadStateOfJobStateJobM___closed__3_value;
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
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "canceled after earlier build failure"};
static const lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0 = (const lean_object*)&l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0_value;
static const lean_ctor_object l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1 = (const lean_object*)&l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1_value;
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
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg();
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg___boxed(lean_object*);
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
lean_inc_ref(v_a_5_);
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
lean_dec_ref(v_a_14_);
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
lean_inc_ref(v_a_24_);
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
lean_dec_ref(v_a_34_);
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
lean_object* v___x_82_; lean_object* v_get_83_; lean_object* v_set_84_; lean_object* v_modifyGet_85_; lean_object* v___x_86_; lean_object* v___f_87_; lean_object* v___f_88_; lean_object* v___f_89_; lean_object* v___x_90_; lean_object* v___f_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_82_ = lean_obj_once(&l_Lake_instMonadStateOfJobStateJobM___closed__1, &l_Lake_instMonadStateOfJobStateJobM___closed__1_once, _init_l_Lake_instMonadStateOfJobStateJobM___closed__1);
v_get_83_ = lean_ctor_get(v___x_82_, 0);
v_set_84_ = lean_ctor_get(v___x_82_, 1);
v_modifyGet_85_ = lean_ctor_get(v___x_82_, 2);
v___x_86_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__2));
v___f_87_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__3));
lean_inc(v_set_84_);
v___f_88_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_88_, 0, v_set_84_);
lean_closure_set(v___f_88_, 1, v___f_87_);
lean_inc(v_modifyGet_85_);
v___f_89_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_89_, 0, v_modifyGet_85_);
lean_closure_set(v___f_89_, 1, v___f_87_);
lean_inc(v_get_83_);
v___x_90_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_90_, 0, lean_box(0));
lean_closure_set(v___x_90_, 1, v_get_83_);
v___f_91_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_91_, 0, v___f_88_);
lean_closure_set(v___f_91_, 1, v___f_87_);
v___f_92_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_92_, 0, v___f_89_);
lean_closure_set(v___f_92_, 1, v___f_87_);
v___x_93_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_93_, 0, lean_box(0));
lean_closure_set(v___x_93_, 1, v___x_90_);
v___f_94_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_94_, 0, v___f_91_);
lean_closure_set(v___f_94_, 1, v___f_87_);
v___f_95_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_95_, 0, v___f_92_);
lean_closure_set(v___f_95_, 1, v___f_87_);
v___x_96_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_96_, 0, lean_box(0));
lean_closure_set(v___x_96_, 1, v___x_93_);
v___f_97_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_97_, 0, v___f_94_);
lean_closure_set(v___f_97_, 1, v___f_87_);
v___f_98_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_98_, 0, v___f_95_);
lean_closure_set(v___f_98_, 1, v___f_87_);
v___x_99_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_99_, 0, lean_box(0));
lean_closure_set(v___x_99_, 1, v___x_96_);
v___f_100_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_100_, 0, v___f_97_);
lean_closure_set(v___f_100_, 1, v___x_86_);
v___f_101_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_101_, 0, v___f_98_);
lean_closure_set(v___f_101_, 1, v___x_86_);
v___x_102_ = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(v___x_102_, 0, lean_box(0));
lean_closure_set(v___x_102_, 1, lean_box(0));
lean_closure_set(v___x_102_, 2, lean_box(0));
lean_closure_set(v___x_102_, 3, v___x_99_);
v___x_103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___f_100_);
lean_ctor_set(v___x_103_, 2, v___f_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0(lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_){
_start:
{
lean_object* v_log_111_; lean_object* v___x_112_; 
v_log_111_ = lean_ctor_get(v___y_109_, 0);
lean_inc_ref(v_log_111_);
v___x_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_112_, 0, v_log_111_);
lean_ctor_set(v___x_112_, 1, v___y_109_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0___boxed(lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lake_instMonadStateOfLogJobM___lam__0(v___y_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec_ref(v___y_116_);
lean_dec(v___y_115_);
lean_dec(v___y_114_);
lean_dec_ref(v___y_113_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1(lean_object* v_log_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
uint8_t v_action_129_; uint8_t v_wantsRebuild_130_; uint8_t v_canceled_131_; lean_object* v_trace_132_; lean_object* v_buildTime_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_142_; 
v_action_129_ = lean_ctor_get_uint8(v___y_127_, sizeof(void*)*3);
v_wantsRebuild_130_ = lean_ctor_get_uint8(v___y_127_, sizeof(void*)*3 + 1);
v_canceled_131_ = lean_ctor_get_uint8(v___y_127_, sizeof(void*)*3 + 2);
v_trace_132_ = lean_ctor_get(v___y_127_, 1);
v_buildTime_133_ = lean_ctor_get(v___y_127_, 2);
v_isSharedCheck_142_ = !lean_is_exclusive(v___y_127_);
if (v_isSharedCheck_142_ == 0)
{
lean_object* v_unused_143_; 
v_unused_143_ = lean_ctor_get(v___y_127_, 0);
lean_dec(v_unused_143_);
v___x_135_ = v___y_127_;
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_buildTime_133_);
lean_inc(v_trace_132_);
lean_dec(v___y_127_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_142_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_137_ = lean_box(0);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 0, v_log_121_);
v___x_139_ = v___x_135_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_log_121_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_trace_132_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_buildTime_133_);
lean_ctor_set_uint8(v_reuseFailAlloc_141_, sizeof(void*)*3, v_action_129_);
lean_ctor_set_uint8(v_reuseFailAlloc_141_, sizeof(void*)*3 + 1, v_wantsRebuild_130_);
lean_ctor_set_uint8(v_reuseFailAlloc_141_, sizeof(void*)*3 + 2, v_canceled_131_);
v___x_139_ = v_reuseFailAlloc_141_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; 
v___x_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_137_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
return v___x_140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1___boxed(lean_object* v_log_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Lake_instMonadStateOfLogJobM___lam__1(v_log_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_);
lean_dec_ref(v___y_149_);
lean_dec_ref(v___y_148_);
lean_dec(v___y_147_);
lean_dec(v___y_146_);
lean_dec_ref(v___y_145_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2(lean_object* v_00_u03b1_153_, lean_object* v_f_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_){
_start:
{
lean_object* v_log_162_; uint8_t v_action_163_; uint8_t v_wantsRebuild_164_; uint8_t v_canceled_165_; lean_object* v_trace_166_; lean_object* v_buildTime_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_184_; 
v_log_162_ = lean_ctor_get(v___y_160_, 0);
v_action_163_ = lean_ctor_get_uint8(v___y_160_, sizeof(void*)*3);
v_wantsRebuild_164_ = lean_ctor_get_uint8(v___y_160_, sizeof(void*)*3 + 1);
v_canceled_165_ = lean_ctor_get_uint8(v___y_160_, sizeof(void*)*3 + 2);
v_trace_166_ = lean_ctor_get(v___y_160_, 1);
v_buildTime_167_ = lean_ctor_get(v___y_160_, 2);
v_isSharedCheck_184_ = !lean_is_exclusive(v___y_160_);
if (v_isSharedCheck_184_ == 0)
{
v___x_169_ = v___y_160_;
v_isShared_170_ = v_isSharedCheck_184_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_buildTime_167_);
lean_inc(v_trace_166_);
lean_inc(v_log_162_);
lean_dec(v___y_160_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_184_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v_fst_172_; lean_object* v_snd_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_183_; 
v___x_171_ = lean_apply_1(v_f_154_, v_log_162_);
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
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_snd_173_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_trace_166_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_buildTime_167_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*3, v_action_163_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*3 + 1, v_wantsRebuild_164_);
lean_ctor_set_uint8(v_reuseFailAlloc_182_, sizeof(void*)*3 + 2, v_canceled_165_);
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
lean_dec_ref(v___y_190_);
lean_dec(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_194_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0(lean_object* v_00_u03b1_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_log_215_; uint8_t v_action_216_; uint8_t v_wantsRebuild_217_; uint8_t v_canceled_218_; lean_object* v_trace_219_; lean_object* v_buildTime_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_232_; 
v_log_215_ = lean_ctor_get(v___y_213_, 0);
v_action_216_ = lean_ctor_get_uint8(v___y_213_, sizeof(void*)*3);
v_wantsRebuild_217_ = lean_ctor_get_uint8(v___y_213_, sizeof(void*)*3 + 1);
v_canceled_218_ = lean_ctor_get_uint8(v___y_213_, sizeof(void*)*3 + 2);
v_trace_219_ = lean_ctor_get(v___y_213_, 1);
v_buildTime_220_ = lean_ctor_get(v___y_213_, 2);
v_isSharedCheck_232_ = !lean_is_exclusive(v___y_213_);
if (v_isSharedCheck_232_ == 0)
{
v___x_222_ = v___y_213_;
v_isShared_223_ = v_isSharedCheck_232_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_buildTime_220_);
lean_inc(v_trace_219_);
lean_inc(v_log_215_);
lean_dec(v___y_213_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_232_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
uint8_t v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_224_ = 3;
v___x_225_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_225_, 0, v___y_207_);
lean_ctor_set_uint8(v___x_225_, sizeof(void*)*1, v___x_224_);
v___x_226_ = lean_array_get_size(v_log_215_);
v___x_227_ = lean_array_push(v_log_215_, v___x_225_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v___x_227_);
v___x_229_ = v___x_222_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_231_, 1, v_trace_219_);
lean_ctor_set(v_reuseFailAlloc_231_, 2, v_buildTime_220_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*3, v_action_216_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*3 + 1, v_wantsRebuild_217_);
lean_ctor_set_uint8(v_reuseFailAlloc_231_, sizeof(void*)*3 + 2, v_canceled_218_);
v___x_229_ = v_reuseFailAlloc_231_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
lean_object* v___x_230_; 
v___x_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_226_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0___boxed(lean_object* v_00_u03b1_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lake_instMonadErrorJobM___lam__0(v_00_u03b1_233_, v___y_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
lean_dec_ref(v___y_239_);
lean_dec_ref(v___y_238_);
lean_dec(v___y_237_);
lean_dec(v___y_236_);
lean_dec_ref(v___y_235_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0(lean_object* v_00_u03b1_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_log_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_log_253_ = lean_ctor_get(v___y_251_, 0);
v___x_254_ = lean_array_get_size(v_log_253_);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___y_251_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0___boxed(lean_object* v_00_u03b1_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_Lake_instAlternativeJobM___lam__0(v_00_u03b1_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec(v___y_258_);
lean_dec_ref(v___y_257_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1(lean_object* v_00_u03b1_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v___x_275_; 
lean_inc_ref(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc(v___y_270_);
lean_inc(v___y_269_);
lean_inc_ref(v___y_268_);
v___x_275_ = lean_apply_7(v___y_266_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, lean_box(0));
if (lean_obj_tag(v___x_275_) == 0)
{
lean_dec_ref(v___y_268_);
lean_dec_ref(v___y_267_);
return v___x_275_;
}
else
{
lean_object* v_a_276_; lean_object* v_a_277_; lean_object* v_log_278_; uint8_t v_action_279_; uint8_t v_wantsRebuild_280_; uint8_t v_canceled_281_; lean_object* v_trace_282_; lean_object* v_buildTime_283_; lean_object* v___x_285_; uint8_t v_isShared_286_; uint8_t v_isSharedCheck_293_; 
v_a_276_ = lean_ctor_get(v___x_275_, 1);
lean_inc(v_a_276_);
v_a_277_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_a_277_);
lean_dec_ref_known(v___x_275_, 2);
v_log_278_ = lean_ctor_get(v_a_276_, 0);
v_action_279_ = lean_ctor_get_uint8(v_a_276_, sizeof(void*)*3);
v_wantsRebuild_280_ = lean_ctor_get_uint8(v_a_276_, sizeof(void*)*3 + 1);
v_canceled_281_ = lean_ctor_get_uint8(v_a_276_, sizeof(void*)*3 + 2);
v_trace_282_ = lean_ctor_get(v_a_276_, 1);
v_buildTime_283_ = lean_ctor_get(v_a_276_, 2);
v_isSharedCheck_293_ = !lean_is_exclusive(v_a_276_);
if (v_isSharedCheck_293_ == 0)
{
v___x_285_ = v_a_276_;
v_isShared_286_ = v_isSharedCheck_293_;
goto v_resetjp_284_;
}
else
{
lean_inc(v_buildTime_283_);
lean_inc(v_trace_282_);
lean_inc(v_log_278_);
lean_dec(v_a_276_);
v___x_285_ = lean_box(0);
v_isShared_286_ = v_isSharedCheck_293_;
goto v_resetjp_284_;
}
v_resetjp_284_:
{
lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_287_ = l_Array_shrink___redArg(v_log_278_, v_a_277_);
lean_dec(v_a_277_);
if (v_isShared_286_ == 0)
{
lean_ctor_set(v___x_285_, 0, v___x_287_);
v___x_289_ = v___x_285_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_292_; 
v_reuseFailAlloc_292_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_292_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_292_, 1, v_trace_282_);
lean_ctor_set(v_reuseFailAlloc_292_, 2, v_buildTime_283_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*3, v_action_279_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*3 + 1, v_wantsRebuild_280_);
lean_ctor_set_uint8(v_reuseFailAlloc_292_, sizeof(void*)*3 + 2, v_canceled_281_);
v___x_289_ = v_reuseFailAlloc_292_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_290_ = lean_box(0);
lean_inc_ref(v___y_272_);
lean_inc_ref(v___y_271_);
lean_inc(v___y_270_);
lean_inc(v___y_269_);
v___x_291_ = lean_apply_8(v___y_267_, v___x_290_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___x_289_, lean_box(0));
return v___x_291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1___boxed(lean_object* v_00_u03b1_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lake_instAlternativeJobM___lam__1(v_00_u03b1_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec(v___y_298_);
return v_res_304_;
}
}
static lean_object* _init_l_Lake_instAlternativeJobM(void){
_start:
{
lean_object* v___x_307_; lean_object* v_toApplicative_308_; lean_object* v_toBind_309_; lean_object* v_toFunctor_310_; lean_object* v_toPure_311_; lean_object* v___f_312_; lean_object* v___f_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___x_316_; lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_toApplicative_325_; lean_object* v___f_326_; lean_object* v___f_327_; lean_object* v___x_328_; 
v___x_307_ = l_instMonadBaseIO;
v_toApplicative_308_ = lean_ctor_get(v___x_307_, 0);
v_toBind_309_ = lean_ctor_get(v___x_307_, 1);
v_toFunctor_310_ = lean_ctor_get(v_toApplicative_308_, 0);
v_toPure_311_ = lean_ctor_get(v_toApplicative_308_, 1);
lean_inc_n(v_toBind_309_, 3);
lean_inc_n(v_toPure_311_, 5);
v___f_312_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_312_, 0, v_toPure_311_);
lean_closure_set(v___f_312_, 1, v_toBind_309_);
v___f_313_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_313_, 0, v_toPure_311_);
lean_closure_set(v___f_313_, 1, v_toBind_309_);
lean_inc_ref(v___f_312_);
v___f_314_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_314_, 0, v_toPure_311_);
lean_closure_set(v___f_314_, 1, v___f_312_);
lean_inc_ref_n(v_toFunctor_310_, 2);
v___f_315_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_315_, 0, v_toFunctor_310_);
lean_closure_set(v___f_315_, 1, v_toPure_311_);
lean_closure_set(v___f_315_, 2, v_toBind_309_);
v___x_316_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_310_);
v___f_317_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_317_, 0, v_toPure_311_);
v___x_318_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_318_, 0, v___x_316_);
lean_ctor_set(v___x_318_, 1, v___f_317_);
lean_ctor_set(v___x_318_, 2, v___f_315_);
lean_ctor_set(v___x_318_, 3, v___f_314_);
lean_ctor_set(v___x_318_, 4, v___f_313_);
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___f_312_);
v___x_320_ = l_ReaderT_instMonad___redArg(v___x_319_);
v___x_321_ = l_ReaderT_instMonad___redArg(v___x_320_);
v___x_322_ = l_ReaderT_instMonad___redArg(v___x_321_);
v___x_323_ = l_ReaderT_instMonad___redArg(v___x_322_);
v___x_324_ = l_Lake_EquipT_instMonad___redArg(v___x_323_);
v_toApplicative_325_ = lean_ctor_get(v___x_324_, 0);
lean_inc_ref(v_toApplicative_325_);
lean_dec_ref(v___x_324_);
v___f_326_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__0));
v___f_327_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__1));
v___x_328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_328_, 0, v_toApplicative_325_);
lean_ctor_set(v___x_328_, 1, v___f_326_);
lean_ctor_set(v___x_328_, 2, v___f_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0(lean_object* v_00_u03b1_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_log_338_; uint8_t v_action_339_; uint8_t v_wantsRebuild_340_; uint8_t v_canceled_341_; lean_object* v_trace_342_; lean_object* v_buildTime_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_372_; 
v_log_338_ = lean_ctor_get(v___y_336_, 0);
v_action_339_ = lean_ctor_get_uint8(v___y_336_, sizeof(void*)*3);
v_wantsRebuild_340_ = lean_ctor_get_uint8(v___y_336_, sizeof(void*)*3 + 1);
v_canceled_341_ = lean_ctor_get_uint8(v___y_336_, sizeof(void*)*3 + 2);
v_trace_342_ = lean_ctor_get(v___y_336_, 1);
v_buildTime_343_ = lean_ctor_get(v___y_336_, 2);
v_isSharedCheck_372_ = !lean_is_exclusive(v___y_336_);
if (v_isSharedCheck_372_ == 0)
{
v___x_345_ = v___y_336_;
v_isShared_346_ = v_isSharedCheck_372_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_buildTime_343_);
lean_inc(v_trace_342_);
lean_inc(v_log_338_);
lean_dec(v___y_336_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_372_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_347_; 
v___x_347_ = lean_apply_2(v___y_330_, v_log_338_, lean_box(0));
if (lean_obj_tag(v___x_347_) == 0)
{
lean_object* v_a_348_; lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_359_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_a_349_ = lean_ctor_get(v___x_347_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_359_ == 0)
{
v___x_351_ = v___x_347_;
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_359_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v_a_349_);
v___x_354_ = v___x_345_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_349_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_trace_342_);
lean_ctor_set(v_reuseFailAlloc_358_, 2, v_buildTime_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*3, v_action_339_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*3 + 1, v_wantsRebuild_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_358_, sizeof(void*)*3 + 2, v_canceled_341_);
v___x_354_ = v_reuseFailAlloc_358_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
lean_object* v___x_356_; 
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v___x_354_);
v___x_356_ = v___x_351_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_348_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_354_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_a_360_; lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_a_360_ = lean_ctor_get(v___x_347_, 0);
v_a_361_ = lean_ctor_get(v___x_347_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_371_ == 0)
{
v___x_363_ = v___x_347_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_inc(v_a_360_);
lean_dec(v___x_347_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v_a_361_);
v___x_366_ = v___x_345_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_361_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_trace_342_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_buildTime_343_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3, v_action_339_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3 + 1, v_wantsRebuild_340_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3 + 2, v_canceled_341_);
v___x_366_ = v_reuseFailAlloc_370_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
lean_object* v___x_368_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 1, v___x_366_);
v___x_368_ = v___x_363_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_360_);
lean_ctor_set(v_reuseFailAlloc_369_, 1, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(lean_object* v_00_u03b1_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lake_instMonadLiftLogIOJobM___lam__0(v_00_u03b1_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_);
lean_dec_ref(v___y_379_);
lean_dec_ref(v___y_378_);
lean_dec(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_382_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg(uint8_t v_action_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_log_388_; uint8_t v_action_389_; uint8_t v_wantsRebuild_390_; uint8_t v_canceled_391_; lean_object* v_trace_392_; lean_object* v_buildTime_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_403_; 
v_log_388_ = lean_ctor_get(v_a_386_, 0);
v_action_389_ = lean_ctor_get_uint8(v_a_386_, sizeof(void*)*3);
v_wantsRebuild_390_ = lean_ctor_get_uint8(v_a_386_, sizeof(void*)*3 + 1);
v_canceled_391_ = lean_ctor_get_uint8(v_a_386_, sizeof(void*)*3 + 2);
v_trace_392_ = lean_ctor_get(v_a_386_, 1);
v_buildTime_393_ = lean_ctor_get(v_a_386_, 2);
v_isSharedCheck_403_ = !lean_is_exclusive(v_a_386_);
if (v_isSharedCheck_403_ == 0)
{
v___x_395_ = v_a_386_;
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_buildTime_393_);
lean_inc(v_trace_392_);
lean_inc(v_log_388_);
lean_dec(v_a_386_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_403_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; uint8_t v___x_398_; lean_object* v___x_400_; 
v___x_397_ = lean_box(0);
v___x_398_ = l_Lake_JobAction_merge(v_action_389_, v_action_385_);
if (v_isShared_396_ == 0)
{
v___x_400_ = v___x_395_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v_log_388_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_trace_392_);
lean_ctor_set(v_reuseFailAlloc_402_, 2, v_buildTime_393_);
lean_ctor_set_uint8(v_reuseFailAlloc_402_, sizeof(void*)*3 + 1, v_wantsRebuild_390_);
lean_ctor_set_uint8(v_reuseFailAlloc_402_, sizeof(void*)*3 + 2, v_canceled_391_);
v___x_400_ = v_reuseFailAlloc_402_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; 
lean_ctor_set_uint8(v___x_400_, sizeof(void*)*3, v___x_398_);
v___x_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_397_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg___boxed(lean_object* v_action_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
uint8_t v_action_boxed_407_; lean_object* v_res_408_; 
v_action_boxed_407_ = lean_unbox(v_action_404_);
v_res_408_ = l_Lake_updateAction___redArg(v_action_boxed_407_, v_a_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction(uint8_t v_action_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_log_417_; uint8_t v_action_418_; uint8_t v_wantsRebuild_419_; uint8_t v_canceled_420_; lean_object* v_trace_421_; lean_object* v_buildTime_422_; lean_object* v___x_424_; uint8_t v_isShared_425_; uint8_t v_isSharedCheck_432_; 
v_log_417_ = lean_ctor_get(v_a_415_, 0);
v_action_418_ = lean_ctor_get_uint8(v_a_415_, sizeof(void*)*3);
v_wantsRebuild_419_ = lean_ctor_get_uint8(v_a_415_, sizeof(void*)*3 + 1);
v_canceled_420_ = lean_ctor_get_uint8(v_a_415_, sizeof(void*)*3 + 2);
v_trace_421_ = lean_ctor_get(v_a_415_, 1);
v_buildTime_422_ = lean_ctor_get(v_a_415_, 2);
v_isSharedCheck_432_ = !lean_is_exclusive(v_a_415_);
if (v_isSharedCheck_432_ == 0)
{
v___x_424_ = v_a_415_;
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
else
{
lean_inc(v_buildTime_422_);
lean_inc(v_trace_421_);
lean_inc(v_log_417_);
lean_dec(v_a_415_);
v___x_424_ = lean_box(0);
v_isShared_425_ = v_isSharedCheck_432_;
goto v_resetjp_423_;
}
v_resetjp_423_:
{
lean_object* v___x_426_; uint8_t v___x_427_; lean_object* v___x_429_; 
v___x_426_ = lean_box(0);
v___x_427_ = l_Lake_JobAction_merge(v_action_418_, v_action_409_);
if (v_isShared_425_ == 0)
{
v___x_429_ = v___x_424_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_log_417_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_trace_421_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_buildTime_422_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*3 + 1, v_wantsRebuild_419_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*3 + 2, v_canceled_420_);
v___x_429_ = v_reuseFailAlloc_431_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; 
lean_ctor_set_uint8(v___x_429_, sizeof(void*)*3, v___x_427_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_426_);
lean_ctor_set(v___x_430_, 1, v___x_429_);
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___boxed(lean_object* v_action_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_){
_start:
{
uint8_t v_action_boxed_441_; lean_object* v_res_442_; 
v_action_boxed_441_ = lean_unbox(v_action_433_);
v_res_442_ = l_Lake_updateAction(v_action_boxed_441_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_);
lean_dec_ref(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg(lean_object* v_a_443_){
_start:
{
lean_object* v_trace_445_; lean_object* v___x_446_; 
v_trace_445_ = lean_ctor_get(v_a_443_, 1);
lean_inc_ref(v_trace_445_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v_trace_445_);
lean_ctor_set(v___x_446_, 1, v_a_443_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg___boxed(lean_object* v_a_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lake_getTrace___redArg(v_a_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace(lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_trace_457_; lean_object* v___x_458_; 
v_trace_457_ = lean_ctor_get(v_a_455_, 1);
lean_inc_ref(v_trace_457_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_trace_457_);
lean_ctor_set(v___x_458_, 1, v_a_455_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___boxed(lean_object* v_a_459_, lean_object* v_a_460_, lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lake_getTrace(v_a_459_, v_a_460_, v_a_461_, v_a_462_, v_a_463_, v_a_464_);
lean_dec_ref(v_a_463_);
lean_dec_ref(v_a_462_);
lean_dec(v_a_461_);
lean_dec(v_a_460_);
lean_dec_ref(v_a_459_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg(lean_object* v_trace_467_, lean_object* v_a_468_){
_start:
{
lean_object* v_log_470_; uint8_t v_action_471_; uint8_t v_wantsRebuild_472_; uint8_t v_canceled_473_; lean_object* v_buildTime_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_483_; 
v_log_470_ = lean_ctor_get(v_a_468_, 0);
v_action_471_ = lean_ctor_get_uint8(v_a_468_, sizeof(void*)*3);
v_wantsRebuild_472_ = lean_ctor_get_uint8(v_a_468_, sizeof(void*)*3 + 1);
v_canceled_473_ = lean_ctor_get_uint8(v_a_468_, sizeof(void*)*3 + 2);
v_buildTime_474_ = lean_ctor_get(v_a_468_, 2);
v_isSharedCheck_483_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_483_ == 0)
{
lean_object* v_unused_484_; 
v_unused_484_ = lean_ctor_get(v_a_468_, 1);
lean_dec(v_unused_484_);
v___x_476_ = v_a_468_;
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_buildTime_474_);
lean_inc(v_log_470_);
lean_dec(v_a_468_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_483_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_478_; lean_object* v___x_480_; 
v___x_478_ = lean_box(0);
if (v_isShared_477_ == 0)
{
lean_ctor_set(v___x_476_, 1, v_trace_467_);
v___x_480_ = v___x_476_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_log_470_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v_trace_467_);
lean_ctor_set(v_reuseFailAlloc_482_, 2, v_buildTime_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*3, v_action_471_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*3 + 1, v_wantsRebuild_472_);
lean_ctor_set_uint8(v_reuseFailAlloc_482_, sizeof(void*)*3 + 2, v_canceled_473_);
v___x_480_ = v_reuseFailAlloc_482_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
lean_object* v___x_481_; 
v___x_481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_478_);
lean_ctor_set(v___x_481_, 1, v___x_480_);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg___boxed(lean_object* v_trace_485_, lean_object* v_a_486_, lean_object* v_a_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lake_setTrace___redArg(v_trace_485_, v_a_486_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace(lean_object* v_trace_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_log_497_; uint8_t v_action_498_; uint8_t v_wantsRebuild_499_; uint8_t v_canceled_500_; lean_object* v_buildTime_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_510_; 
v_log_497_ = lean_ctor_get(v_a_495_, 0);
v_action_498_ = lean_ctor_get_uint8(v_a_495_, sizeof(void*)*3);
v_wantsRebuild_499_ = lean_ctor_get_uint8(v_a_495_, sizeof(void*)*3 + 1);
v_canceled_500_ = lean_ctor_get_uint8(v_a_495_, sizeof(void*)*3 + 2);
v_buildTime_501_ = lean_ctor_get(v_a_495_, 2);
v_isSharedCheck_510_ = !lean_is_exclusive(v_a_495_);
if (v_isSharedCheck_510_ == 0)
{
lean_object* v_unused_511_; 
v_unused_511_ = lean_ctor_get(v_a_495_, 1);
lean_dec(v_unused_511_);
v___x_503_ = v_a_495_;
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_buildTime_501_);
lean_inc(v_log_497_);
lean_dec(v_a_495_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_510_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_505_ = lean_box(0);
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 1, v_trace_489_);
v___x_507_ = v___x_503_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v_log_497_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_trace_489_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_buildTime_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_509_, sizeof(void*)*3, v_action_498_);
lean_ctor_set_uint8(v_reuseFailAlloc_509_, sizeof(void*)*3 + 1, v_wantsRebuild_499_);
lean_ctor_set_uint8(v_reuseFailAlloc_509_, sizeof(void*)*3 + 2, v_canceled_500_);
v___x_507_ = v_reuseFailAlloc_509_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
lean_object* v___x_508_; 
v___x_508_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_508_, 0, v___x_505_);
lean_ctor_set(v___x_508_, 1, v___x_507_);
return v___x_508_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___boxed(lean_object* v_trace_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lake_setTrace(v_trace_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_);
lean_dec_ref(v_a_517_);
lean_dec_ref(v_a_516_);
lean_dec(v_a_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg(lean_object* v_caption_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_log_524_; uint8_t v_action_525_; uint8_t v_wantsRebuild_526_; uint8_t v_canceled_527_; lean_object* v_buildTime_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_538_; 
v_log_524_ = lean_ctor_get(v_a_522_, 0);
v_action_525_ = lean_ctor_get_uint8(v_a_522_, sizeof(void*)*3);
v_wantsRebuild_526_ = lean_ctor_get_uint8(v_a_522_, sizeof(void*)*3 + 1);
v_canceled_527_ = lean_ctor_get_uint8(v_a_522_, sizeof(void*)*3 + 2);
v_buildTime_528_ = lean_ctor_get(v_a_522_, 2);
v_isSharedCheck_538_ = !lean_is_exclusive(v_a_522_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v_a_522_, 1);
lean_dec(v_unused_539_);
v___x_530_ = v_a_522_;
v_isShared_531_ = v_isSharedCheck_538_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_buildTime_528_);
lean_inc(v_log_524_);
lean_dec(v_a_522_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_538_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_535_; 
v___x_532_ = l_Lake_BuildTrace_nil(v_caption_521_);
v___x_533_ = lean_box(0);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 1, v___x_532_);
v___x_535_ = v___x_530_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_log_524_);
lean_ctor_set(v_reuseFailAlloc_537_, 1, v___x_532_);
lean_ctor_set(v_reuseFailAlloc_537_, 2, v_buildTime_528_);
lean_ctor_set_uint8(v_reuseFailAlloc_537_, sizeof(void*)*3, v_action_525_);
lean_ctor_set_uint8(v_reuseFailAlloc_537_, sizeof(void*)*3 + 1, v_wantsRebuild_526_);
lean_ctor_set_uint8(v_reuseFailAlloc_537_, sizeof(void*)*3 + 2, v_canceled_527_);
v___x_535_ = v_reuseFailAlloc_537_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_533_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg___boxed(lean_object* v_caption_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_Lake_newTrace___redArg(v_caption_540_, v_a_541_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace(lean_object* v_caption_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_){
_start:
{
lean_object* v_log_552_; uint8_t v_action_553_; uint8_t v_wantsRebuild_554_; uint8_t v_canceled_555_; lean_object* v_buildTime_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_566_; 
v_log_552_ = lean_ctor_get(v_a_550_, 0);
v_action_553_ = lean_ctor_get_uint8(v_a_550_, sizeof(void*)*3);
v_wantsRebuild_554_ = lean_ctor_get_uint8(v_a_550_, sizeof(void*)*3 + 1);
v_canceled_555_ = lean_ctor_get_uint8(v_a_550_, sizeof(void*)*3 + 2);
v_buildTime_556_ = lean_ctor_get(v_a_550_, 2);
v_isSharedCheck_566_ = !lean_is_exclusive(v_a_550_);
if (v_isSharedCheck_566_ == 0)
{
lean_object* v_unused_567_; 
v_unused_567_ = lean_ctor_get(v_a_550_, 1);
lean_dec(v_unused_567_);
v___x_558_ = v_a_550_;
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_buildTime_556_);
lean_inc(v_log_552_);
lean_dec(v_a_550_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_566_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_560_ = l_Lake_BuildTrace_nil(v_caption_544_);
v___x_561_ = lean_box(0);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 1, v___x_560_);
v___x_563_ = v___x_558_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_log_552_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v___x_560_);
lean_ctor_set(v_reuseFailAlloc_565_, 2, v_buildTime_556_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, sizeof(void*)*3, v_action_553_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, sizeof(void*)*3 + 1, v_wantsRebuild_554_);
lean_ctor_set_uint8(v_reuseFailAlloc_565_, sizeof(void*)*3 + 2, v_canceled_555_);
v___x_563_ = v_reuseFailAlloc_565_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_561_);
lean_ctor_set(v___x_564_, 1, v___x_563_);
return v___x_564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___boxed(lean_object* v_caption_568_, lean_object* v_a_569_, lean_object* v_a_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Lake_newTrace(v_caption_568_, v_a_569_, v_a_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_);
lean_dec_ref(v_a_573_);
lean_dec_ref(v_a_572_);
lean_dec(v_a_571_);
lean_dec(v_a_570_);
lean_dec_ref(v_a_569_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg(lean_object* v_f_577_, lean_object* v_a_578_){
_start:
{
lean_object* v_log_580_; uint8_t v_action_581_; uint8_t v_wantsRebuild_582_; uint8_t v_canceled_583_; lean_object* v_trace_584_; lean_object* v_buildTime_585_; lean_object* v___x_587_; uint8_t v_isShared_588_; uint8_t v_isSharedCheck_595_; 
v_log_580_ = lean_ctor_get(v_a_578_, 0);
v_action_581_ = lean_ctor_get_uint8(v_a_578_, sizeof(void*)*3);
v_wantsRebuild_582_ = lean_ctor_get_uint8(v_a_578_, sizeof(void*)*3 + 1);
v_canceled_583_ = lean_ctor_get_uint8(v_a_578_, sizeof(void*)*3 + 2);
v_trace_584_ = lean_ctor_get(v_a_578_, 1);
v_buildTime_585_ = lean_ctor_get(v_a_578_, 2);
v_isSharedCheck_595_ = !lean_is_exclusive(v_a_578_);
if (v_isSharedCheck_595_ == 0)
{
v___x_587_ = v_a_578_;
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
else
{
lean_inc(v_buildTime_585_);
lean_inc(v_trace_584_);
lean_inc(v_log_580_);
lean_dec(v_a_578_);
v___x_587_ = lean_box(0);
v_isShared_588_ = v_isSharedCheck_595_;
goto v_resetjp_586_;
}
v_resetjp_586_:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_592_; 
v___x_589_ = lean_box(0);
v___x_590_ = lean_apply_1(v_f_577_, v_trace_584_);
if (v_isShared_588_ == 0)
{
lean_ctor_set(v___x_587_, 1, v___x_590_);
v___x_592_ = v___x_587_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_log_580_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v___x_590_);
lean_ctor_set(v_reuseFailAlloc_594_, 2, v_buildTime_585_);
lean_ctor_set_uint8(v_reuseFailAlloc_594_, sizeof(void*)*3, v_action_581_);
lean_ctor_set_uint8(v_reuseFailAlloc_594_, sizeof(void*)*3 + 1, v_wantsRebuild_582_);
lean_ctor_set_uint8(v_reuseFailAlloc_594_, sizeof(void*)*3 + 2, v_canceled_583_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_589_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
return v___x_593_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg___boxed(lean_object* v_f_596_, lean_object* v_a_597_, lean_object* v_a_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lake_modifyTrace___redArg(v_f_596_, v_a_597_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace(lean_object* v_f_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_){
_start:
{
lean_object* v_log_608_; uint8_t v_action_609_; uint8_t v_wantsRebuild_610_; uint8_t v_canceled_611_; lean_object* v_trace_612_; lean_object* v_buildTime_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_623_; 
v_log_608_ = lean_ctor_get(v_a_606_, 0);
v_action_609_ = lean_ctor_get_uint8(v_a_606_, sizeof(void*)*3);
v_wantsRebuild_610_ = lean_ctor_get_uint8(v_a_606_, sizeof(void*)*3 + 1);
v_canceled_611_ = lean_ctor_get_uint8(v_a_606_, sizeof(void*)*3 + 2);
v_trace_612_ = lean_ctor_get(v_a_606_, 1);
v_buildTime_613_ = lean_ctor_get(v_a_606_, 2);
v_isSharedCheck_623_ = !lean_is_exclusive(v_a_606_);
if (v_isSharedCheck_623_ == 0)
{
v___x_615_ = v_a_606_;
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_buildTime_613_);
lean_inc(v_trace_612_);
lean_inc(v_log_608_);
lean_dec(v_a_606_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_623_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_617_ = lean_box(0);
v___x_618_ = lean_apply_1(v_f_600_, v_trace_612_);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 1, v___x_618_);
v___x_620_ = v___x_615_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_log_608_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_buildTime_613_);
lean_ctor_set_uint8(v_reuseFailAlloc_622_, sizeof(void*)*3, v_action_609_);
lean_ctor_set_uint8(v_reuseFailAlloc_622_, sizeof(void*)*3 + 1, v_wantsRebuild_610_);
lean_ctor_set_uint8(v_reuseFailAlloc_622_, sizeof(void*)*3 + 2, v_canceled_611_);
v___x_620_ = v_reuseFailAlloc_622_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
lean_object* v___x_621_; 
v___x_621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_617_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
return v___x_621_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___boxed(lean_object* v_f_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lake_modifyTrace(v_f_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
lean_dec_ref(v_a_629_);
lean_dec_ref(v_a_628_);
lean_dec(v_a_627_);
lean_dec(v_a_626_);
lean_dec_ref(v_a_625_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg(lean_object* v_caption_633_, lean_object* v_a_634_){
_start:
{
lean_object* v_trace_636_; lean_object* v_log_637_; uint8_t v_action_638_; uint8_t v_wantsRebuild_639_; uint8_t v_canceled_640_; lean_object* v_buildTime_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_661_; 
v_trace_636_ = lean_ctor_get(v_a_634_, 1);
v_log_637_ = lean_ctor_get(v_a_634_, 0);
v_action_638_ = lean_ctor_get_uint8(v_a_634_, sizeof(void*)*3);
v_wantsRebuild_639_ = lean_ctor_get_uint8(v_a_634_, sizeof(void*)*3 + 1);
v_canceled_640_ = lean_ctor_get_uint8(v_a_634_, sizeof(void*)*3 + 2);
v_buildTime_641_ = lean_ctor_get(v_a_634_, 2);
v_isSharedCheck_661_ = !lean_is_exclusive(v_a_634_);
if (v_isSharedCheck_661_ == 0)
{
v___x_643_ = v_a_634_;
v_isShared_644_ = v_isSharedCheck_661_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_buildTime_641_);
lean_inc(v_trace_636_);
lean_inc(v_log_637_);
lean_dec(v_a_634_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_661_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v_inputs_645_; uint64_t v_hash_646_; lean_object* v_mtime_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_659_; 
v_inputs_645_ = lean_ctor_get(v_trace_636_, 1);
v_hash_646_ = lean_ctor_get_uint64(v_trace_636_, sizeof(void*)*3);
v_mtime_647_ = lean_ctor_get(v_trace_636_, 2);
v_isSharedCheck_659_ = !lean_is_exclusive(v_trace_636_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v_trace_636_, 0);
lean_dec(v_unused_660_);
v___x_649_ = v_trace_636_;
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_mtime_647_);
lean_inc(v_inputs_645_);
lean_dec(v_trace_636_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_659_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_651_ = lean_box(0);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v_caption_633_);
v___x_653_ = v___x_649_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_caption_633_);
lean_ctor_set(v_reuseFailAlloc_658_, 1, v_inputs_645_);
lean_ctor_set(v_reuseFailAlloc_658_, 2, v_mtime_647_);
lean_ctor_set_uint64(v_reuseFailAlloc_658_, sizeof(void*)*3, v_hash_646_);
v___x_653_ = v_reuseFailAlloc_658_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
lean_object* v___x_655_; 
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_653_);
v___x_655_ = v___x_643_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_log_637_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v___x_653_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_buildTime_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_657_, sizeof(void*)*3, v_action_638_);
lean_ctor_set_uint8(v_reuseFailAlloc_657_, sizeof(void*)*3 + 1, v_wantsRebuild_639_);
lean_ctor_set_uint8(v_reuseFailAlloc_657_, sizeof(void*)*3 + 2, v_canceled_640_);
v___x_655_ = v_reuseFailAlloc_657_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_656_; 
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_651_);
lean_ctor_set(v___x_656_, 1, v___x_655_);
return v___x_656_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg___boxed(lean_object* v_caption_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lake_setTraceCaption___redArg(v_caption_662_, v_a_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption(lean_object* v_caption_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_){
_start:
{
lean_object* v_trace_674_; lean_object* v_log_675_; uint8_t v_action_676_; uint8_t v_wantsRebuild_677_; uint8_t v_canceled_678_; lean_object* v_buildTime_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_699_; 
v_trace_674_ = lean_ctor_get(v_a_672_, 1);
v_log_675_ = lean_ctor_get(v_a_672_, 0);
v_action_676_ = lean_ctor_get_uint8(v_a_672_, sizeof(void*)*3);
v_wantsRebuild_677_ = lean_ctor_get_uint8(v_a_672_, sizeof(void*)*3 + 1);
v_canceled_678_ = lean_ctor_get_uint8(v_a_672_, sizeof(void*)*3 + 2);
v_buildTime_679_ = lean_ctor_get(v_a_672_, 2);
v_isSharedCheck_699_ = !lean_is_exclusive(v_a_672_);
if (v_isSharedCheck_699_ == 0)
{
v___x_681_ = v_a_672_;
v_isShared_682_ = v_isSharedCheck_699_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_buildTime_679_);
lean_inc(v_trace_674_);
lean_inc(v_log_675_);
lean_dec(v_a_672_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_699_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v_inputs_683_; uint64_t v_hash_684_; lean_object* v_mtime_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_697_; 
v_inputs_683_ = lean_ctor_get(v_trace_674_, 1);
v_hash_684_ = lean_ctor_get_uint64(v_trace_674_, sizeof(void*)*3);
v_mtime_685_ = lean_ctor_get(v_trace_674_, 2);
v_isSharedCheck_697_ = !lean_is_exclusive(v_trace_674_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_trace_674_, 0);
lean_dec(v_unused_698_);
v___x_687_ = v_trace_674_;
v_isShared_688_ = v_isSharedCheck_697_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_mtime_685_);
lean_inc(v_inputs_683_);
lean_dec(v_trace_674_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_697_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_689_; lean_object* v___x_691_; 
v___x_689_ = lean_box(0);
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v_caption_666_);
v___x_691_ = v___x_687_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_696_; 
v_reuseFailAlloc_696_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_696_, 0, v_caption_666_);
lean_ctor_set(v_reuseFailAlloc_696_, 1, v_inputs_683_);
lean_ctor_set(v_reuseFailAlloc_696_, 2, v_mtime_685_);
lean_ctor_set_uint64(v_reuseFailAlloc_696_, sizeof(void*)*3, v_hash_684_);
v___x_691_ = v_reuseFailAlloc_696_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 1, v___x_691_);
v___x_693_ = v___x_681_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_log_675_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v___x_691_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_buildTime_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*3, v_action_676_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*3 + 1, v_wantsRebuild_677_);
lean_ctor_set_uint8(v_reuseFailAlloc_695_, sizeof(void*)*3 + 2, v_canceled_678_);
v___x_693_ = v_reuseFailAlloc_695_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_694_; 
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_689_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
return v___x_694_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___boxed(lean_object* v_caption_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lake_setTraceCaption(v_caption_700_, v_a_701_, v_a_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_);
lean_dec_ref(v_a_705_);
lean_dec_ref(v_a_704_);
lean_dec(v_a_703_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
return v_res_708_;
}
}
static lean_object* _init_l_Lake_takeTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = ((lean_object*)(l_Lake_takeTrace___redArg___closed__0));
v___x_711_ = l_Lake_BuildTrace_nil(v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg(lean_object* v_a_712_){
_start:
{
lean_object* v_log_714_; uint8_t v_action_715_; uint8_t v_wantsRebuild_716_; uint8_t v_canceled_717_; lean_object* v_trace_718_; lean_object* v_buildTime_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_728_; 
v_log_714_ = lean_ctor_get(v_a_712_, 0);
v_action_715_ = lean_ctor_get_uint8(v_a_712_, sizeof(void*)*3);
v_wantsRebuild_716_ = lean_ctor_get_uint8(v_a_712_, sizeof(void*)*3 + 1);
v_canceled_717_ = lean_ctor_get_uint8(v_a_712_, sizeof(void*)*3 + 2);
v_trace_718_ = lean_ctor_get(v_a_712_, 1);
v_buildTime_719_ = lean_ctor_get(v_a_712_, 2);
v_isSharedCheck_728_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_728_ == 0)
{
v___x_721_ = v_a_712_;
v_isShared_722_ = v_isSharedCheck_728_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_buildTime_719_);
lean_inc(v_trace_718_);
lean_inc(v_log_714_);
lean_dec(v_a_712_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_728_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_722_ == 0)
{
lean_ctor_set(v___x_721_, 1, v___x_723_);
v___x_725_ = v___x_721_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_log_714_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v___x_723_);
lean_ctor_set(v_reuseFailAlloc_727_, 2, v_buildTime_719_);
lean_ctor_set_uint8(v_reuseFailAlloc_727_, sizeof(void*)*3, v_action_715_);
lean_ctor_set_uint8(v_reuseFailAlloc_727_, sizeof(void*)*3 + 1, v_wantsRebuild_716_);
lean_ctor_set_uint8(v_reuseFailAlloc_727_, sizeof(void*)*3 + 2, v_canceled_717_);
v___x_725_ = v_reuseFailAlloc_727_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; 
v___x_726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_726_, 0, v_trace_718_);
lean_ctor_set(v___x_726_, 1, v___x_725_);
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg___boxed(lean_object* v_a_729_, lean_object* v_a_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lake_takeTrace___redArg(v_a_729_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace(lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_log_739_; uint8_t v_action_740_; uint8_t v_wantsRebuild_741_; uint8_t v_canceled_742_; lean_object* v_trace_743_; lean_object* v_buildTime_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_753_; 
v_log_739_ = lean_ctor_get(v_a_737_, 0);
v_action_740_ = lean_ctor_get_uint8(v_a_737_, sizeof(void*)*3);
v_wantsRebuild_741_ = lean_ctor_get_uint8(v_a_737_, sizeof(void*)*3 + 1);
v_canceled_742_ = lean_ctor_get_uint8(v_a_737_, sizeof(void*)*3 + 2);
v_trace_743_ = lean_ctor_get(v_a_737_, 1);
v_buildTime_744_ = lean_ctor_get(v_a_737_, 2);
v_isSharedCheck_753_ = !lean_is_exclusive(v_a_737_);
if (v_isSharedCheck_753_ == 0)
{
v___x_746_ = v_a_737_;
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_buildTime_744_);
lean_inc(v_trace_743_);
lean_inc(v_log_739_);
lean_dec(v_a_737_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_753_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 1, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_log_739_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_buildTime_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*3, v_action_740_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*3 + 1, v_wantsRebuild_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*3 + 2, v_canceled_742_);
v___x_750_ = v_reuseFailAlloc_752_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
lean_object* v___x_751_; 
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v_trace_743_);
lean_ctor_set(v___x_751_, 1, v___x_750_);
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___boxed(lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lake_takeTrace(v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
lean_dec_ref(v_a_758_);
lean_dec_ref(v_a_757_);
lean_dec(v_a_756_);
lean_dec(v_a_755_);
lean_dec_ref(v_a_754_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg(lean_object* v_trace_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_log_765_; uint8_t v_action_766_; uint8_t v_wantsRebuild_767_; uint8_t v_canceled_768_; lean_object* v_trace_769_; lean_object* v_buildTime_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_778_; 
v_log_765_ = lean_ctor_get(v_a_763_, 0);
v_action_766_ = lean_ctor_get_uint8(v_a_763_, sizeof(void*)*3);
v_wantsRebuild_767_ = lean_ctor_get_uint8(v_a_763_, sizeof(void*)*3 + 1);
v_canceled_768_ = lean_ctor_get_uint8(v_a_763_, sizeof(void*)*3 + 2);
v_trace_769_ = lean_ctor_get(v_a_763_, 1);
v_buildTime_770_ = lean_ctor_get(v_a_763_, 2);
v_isSharedCheck_778_ = !lean_is_exclusive(v_a_763_);
if (v_isSharedCheck_778_ == 0)
{
v___x_772_ = v_a_763_;
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_buildTime_770_);
lean_inc(v_trace_769_);
lean_inc(v_log_765_);
lean_dec(v_a_763_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_778_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_775_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_trace_762_);
v___x_775_ = v___x_772_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_log_765_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_trace_762_);
lean_ctor_set(v_reuseFailAlloc_777_, 2, v_buildTime_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*3, v_action_766_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*3 + 1, v_wantsRebuild_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_777_, sizeof(void*)*3 + 2, v_canceled_768_);
v___x_775_ = v_reuseFailAlloc_777_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
lean_object* v___x_776_; 
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v_trace_769_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
return v___x_776_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg___boxed(lean_object* v_trace_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lake_swapTrace___redArg(v_trace_779_, v_a_780_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace(lean_object* v_trace_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_){
_start:
{
lean_object* v_log_791_; uint8_t v_action_792_; uint8_t v_wantsRebuild_793_; uint8_t v_canceled_794_; lean_object* v_trace_795_; lean_object* v_buildTime_796_; lean_object* v___x_798_; uint8_t v_isShared_799_; uint8_t v_isSharedCheck_804_; 
v_log_791_ = lean_ctor_get(v_a_789_, 0);
v_action_792_ = lean_ctor_get_uint8(v_a_789_, sizeof(void*)*3);
v_wantsRebuild_793_ = lean_ctor_get_uint8(v_a_789_, sizeof(void*)*3 + 1);
v_canceled_794_ = lean_ctor_get_uint8(v_a_789_, sizeof(void*)*3 + 2);
v_trace_795_ = lean_ctor_get(v_a_789_, 1);
v_buildTime_796_ = lean_ctor_get(v_a_789_, 2);
v_isSharedCheck_804_ = !lean_is_exclusive(v_a_789_);
if (v_isSharedCheck_804_ == 0)
{
v___x_798_ = v_a_789_;
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
else
{
lean_inc(v_buildTime_796_);
lean_inc(v_trace_795_);
lean_inc(v_log_791_);
lean_dec(v_a_789_);
v___x_798_ = lean_box(0);
v_isShared_799_ = v_isSharedCheck_804_;
goto v_resetjp_797_;
}
v_resetjp_797_:
{
lean_object* v___x_801_; 
if (v_isShared_799_ == 0)
{
lean_ctor_set(v___x_798_, 1, v_trace_783_);
v___x_801_ = v___x_798_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_log_791_);
lean_ctor_set(v_reuseFailAlloc_803_, 1, v_trace_783_);
lean_ctor_set(v_reuseFailAlloc_803_, 2, v_buildTime_796_);
lean_ctor_set_uint8(v_reuseFailAlloc_803_, sizeof(void*)*3, v_action_792_);
lean_ctor_set_uint8(v_reuseFailAlloc_803_, sizeof(void*)*3 + 1, v_wantsRebuild_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_803_, sizeof(void*)*3 + 2, v_canceled_794_);
v___x_801_ = v_reuseFailAlloc_803_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; 
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v_trace_795_);
lean_ctor_set(v___x_802_, 1, v___x_801_);
return v___x_802_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___boxed(lean_object* v_trace_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lake_swapTrace(v_trace_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec_ref(v_a_809_);
lean_dec(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg(lean_object* v_trace_814_, lean_object* v_a_815_){
_start:
{
lean_object* v_log_817_; uint8_t v_action_818_; uint8_t v_wantsRebuild_819_; uint8_t v_canceled_820_; lean_object* v_trace_821_; lean_object* v_buildTime_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_832_; 
v_log_817_ = lean_ctor_get(v_a_815_, 0);
v_action_818_ = lean_ctor_get_uint8(v_a_815_, sizeof(void*)*3);
v_wantsRebuild_819_ = lean_ctor_get_uint8(v_a_815_, sizeof(void*)*3 + 1);
v_canceled_820_ = lean_ctor_get_uint8(v_a_815_, sizeof(void*)*3 + 2);
v_trace_821_ = lean_ctor_get(v_a_815_, 1);
v_buildTime_822_ = lean_ctor_get(v_a_815_, 2);
v_isSharedCheck_832_ = !lean_is_exclusive(v_a_815_);
if (v_isSharedCheck_832_ == 0)
{
v___x_824_ = v_a_815_;
v_isShared_825_ = v_isSharedCheck_832_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_buildTime_822_);
lean_inc(v_trace_821_);
lean_inc(v_log_817_);
lean_dec(v_a_815_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_832_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_826_ = lean_box(0);
v___x_827_ = l_Lake_BuildTrace_mix(v_trace_821_, v_trace_814_);
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v___x_827_);
v___x_829_ = v___x_824_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_log_817_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v___x_827_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_buildTime_822_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*3, v_action_818_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*3 + 1, v_wantsRebuild_819_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*3 + 2, v_canceled_820_);
v___x_829_ = v_reuseFailAlloc_831_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_826_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg___boxed(lean_object* v_trace_833_, lean_object* v_a_834_, lean_object* v_a_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lake_addTrace___redArg(v_trace_833_, v_a_834_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace(lean_object* v_trace_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_log_845_; uint8_t v_action_846_; uint8_t v_wantsRebuild_847_; uint8_t v_canceled_848_; lean_object* v_trace_849_; lean_object* v_buildTime_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_860_; 
v_log_845_ = lean_ctor_get(v_a_843_, 0);
v_action_846_ = lean_ctor_get_uint8(v_a_843_, sizeof(void*)*3);
v_wantsRebuild_847_ = lean_ctor_get_uint8(v_a_843_, sizeof(void*)*3 + 1);
v_canceled_848_ = lean_ctor_get_uint8(v_a_843_, sizeof(void*)*3 + 2);
v_trace_849_ = lean_ctor_get(v_a_843_, 1);
v_buildTime_850_ = lean_ctor_get(v_a_843_, 2);
v_isSharedCheck_860_ = !lean_is_exclusive(v_a_843_);
if (v_isSharedCheck_860_ == 0)
{
v___x_852_ = v_a_843_;
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_buildTime_850_);
lean_inc(v_trace_849_);
lean_inc(v_log_845_);
lean_dec(v_a_843_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_854_ = lean_box(0);
v___x_855_ = l_Lake_BuildTrace_mix(v_trace_849_, v_trace_837_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_855_);
v___x_857_ = v___x_852_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_log_845_);
lean_ctor_set(v_reuseFailAlloc_859_, 1, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_859_, 2, v_buildTime_850_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*3, v_action_846_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*3 + 1, v_wantsRebuild_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_859_, sizeof(void*)*3 + 2, v_canceled_848_);
v___x_857_ = v_reuseFailAlloc_859_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; 
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_854_);
lean_ctor_set(v___x_858_, 1, v___x_857_);
return v___x_858_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___boxed(lean_object* v_trace_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lake_addTrace(v_trace_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec(v_a_863_);
lean_dec_ref(v_a_862_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg(lean_object* v_caption_870_, lean_object* v_x_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_log_879_; uint8_t v_action_880_; uint8_t v_wantsRebuild_881_; uint8_t v_canceled_882_; lean_object* v_trace_883_; lean_object* v_buildTime_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_916_; 
v_log_879_ = lean_ctor_get(v_a_877_, 0);
v_action_880_ = lean_ctor_get_uint8(v_a_877_, sizeof(void*)*3);
v_wantsRebuild_881_ = lean_ctor_get_uint8(v_a_877_, sizeof(void*)*3 + 1);
v_canceled_882_ = lean_ctor_get_uint8(v_a_877_, sizeof(void*)*3 + 2);
v_trace_883_ = lean_ctor_get(v_a_877_, 1);
v_buildTime_884_ = lean_ctor_get(v_a_877_, 2);
v_isSharedCheck_916_ = !lean_is_exclusive(v_a_877_);
if (v_isSharedCheck_916_ == 0)
{
v___x_886_ = v_a_877_;
v_isShared_887_ = v_isSharedCheck_916_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_buildTime_884_);
lean_inc(v_trace_883_);
lean_inc(v_log_879_);
lean_dec(v_a_877_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_916_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_888_ = l_Lake_BuildTrace_nil(v_caption_870_);
if (v_isShared_887_ == 0)
{
lean_ctor_set(v___x_886_, 1, v___x_888_);
v___x_890_ = v___x_886_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_log_879_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_buildTime_884_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3, v_action_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3 + 1, v_wantsRebuild_881_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3 + 2, v_canceled_882_);
v___x_890_ = v_reuseFailAlloc_915_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
lean_object* v___x_891_; 
lean_inc_ref(v_a_876_);
lean_inc_ref(v_a_875_);
lean_inc(v_a_874_);
lean_inc(v_a_873_);
v___x_891_ = lean_apply_7(v_x_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v___x_890_, lean_box(0));
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v_a_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_914_; 
v_a_892_ = lean_ctor_get(v___x_891_, 1);
v_a_893_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_914_ == 0)
{
v___x_895_ = v___x_891_;
v_isShared_896_ = v_isSharedCheck_914_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_a_892_);
lean_inc(v_a_893_);
lean_dec(v___x_891_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_914_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v_log_897_; uint8_t v_action_898_; uint8_t v_wantsRebuild_899_; uint8_t v_canceled_900_; lean_object* v_trace_901_; lean_object* v_buildTime_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_913_; 
v_log_897_ = lean_ctor_get(v_a_892_, 0);
v_action_898_ = lean_ctor_get_uint8(v_a_892_, sizeof(void*)*3);
v_wantsRebuild_899_ = lean_ctor_get_uint8(v_a_892_, sizeof(void*)*3 + 1);
v_canceled_900_ = lean_ctor_get_uint8(v_a_892_, sizeof(void*)*3 + 2);
v_trace_901_ = lean_ctor_get(v_a_892_, 1);
v_buildTime_902_ = lean_ctor_get(v_a_892_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_892_);
if (v_isSharedCheck_913_ == 0)
{
v___x_904_ = v_a_892_;
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_buildTime_902_);
lean_inc(v_trace_901_);
lean_inc(v_log_897_);
lean_dec(v_a_892_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = l_Lake_BuildTrace_mix(v_trace_883_, v_trace_901_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_log_897_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_buildTime_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3, v_action_898_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 1, v_wantsRebuild_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 2, v_canceled_900_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v___x_908_);
v___x_910_ = v___x_895_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_893_);
lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_908_);
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
else
{
lean_dec_ref(v_trace_883_);
return v___x_891_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg___boxed(lean_object* v_caption_917_, lean_object* v_x_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lake_addSubTrace___redArg(v_caption_917_, v_x_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec_ref(v_a_922_);
lean_dec(v_a_921_);
lean_dec(v_a_920_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace(lean_object* v_00_u03b1_927_, lean_object* v_caption_928_, lean_object* v_x_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_log_937_; uint8_t v_action_938_; uint8_t v_wantsRebuild_939_; uint8_t v_canceled_940_; lean_object* v_trace_941_; lean_object* v_buildTime_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_974_; 
v_log_937_ = lean_ctor_get(v_a_935_, 0);
v_action_938_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*3);
v_wantsRebuild_939_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*3 + 1);
v_canceled_940_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*3 + 2);
v_trace_941_ = lean_ctor_get(v_a_935_, 1);
v_buildTime_942_ = lean_ctor_get(v_a_935_, 2);
v_isSharedCheck_974_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_974_ == 0)
{
v___x_944_ = v_a_935_;
v_isShared_945_ = v_isSharedCheck_974_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_buildTime_942_);
lean_inc(v_trace_941_);
lean_inc(v_log_937_);
lean_dec(v_a_935_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_974_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_946_ = l_Lake_BuildTrace_nil(v_caption_928_);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 1, v___x_946_);
v___x_948_ = v___x_944_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_log_937_);
lean_ctor_set(v_reuseFailAlloc_973_, 1, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_973_, 2, v_buildTime_942_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3, v_action_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 1, v_wantsRebuild_939_);
lean_ctor_set_uint8(v_reuseFailAlloc_973_, sizeof(void*)*3 + 2, v_canceled_940_);
v___x_948_ = v_reuseFailAlloc_973_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
lean_object* v___x_949_; 
lean_inc_ref(v_a_934_);
lean_inc_ref(v_a_933_);
lean_inc(v_a_932_);
lean_inc(v_a_931_);
v___x_949_ = lean_apply_7(v_x_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v___x_948_, lean_box(0));
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_972_; 
v_a_950_ = lean_ctor_get(v___x_949_, 1);
v_a_951_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_972_ == 0)
{
v___x_953_ = v___x_949_;
v_isShared_954_ = v_isSharedCheck_972_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_950_);
lean_inc(v_a_951_);
lean_dec(v___x_949_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_972_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v_log_955_; uint8_t v_action_956_; uint8_t v_wantsRebuild_957_; uint8_t v_canceled_958_; lean_object* v_trace_959_; lean_object* v_buildTime_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_971_; 
v_log_955_ = lean_ctor_get(v_a_950_, 0);
v_action_956_ = lean_ctor_get_uint8(v_a_950_, sizeof(void*)*3);
v_wantsRebuild_957_ = lean_ctor_get_uint8(v_a_950_, sizeof(void*)*3 + 1);
v_canceled_958_ = lean_ctor_get_uint8(v_a_950_, sizeof(void*)*3 + 2);
v_trace_959_ = lean_ctor_get(v_a_950_, 1);
v_buildTime_960_ = lean_ctor_get(v_a_950_, 2);
v_isSharedCheck_971_ = !lean_is_exclusive(v_a_950_);
if (v_isSharedCheck_971_ == 0)
{
v___x_962_ = v_a_950_;
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_buildTime_960_);
lean_inc(v_trace_959_);
lean_inc(v_log_955_);
lean_dec(v_a_950_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_971_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_964_; lean_object* v___x_966_; 
v___x_964_ = l_Lake_BuildTrace_mix(v_trace_941_, v_trace_959_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_964_);
v___x_966_ = v___x_962_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v_log_955_);
lean_ctor_set(v_reuseFailAlloc_970_, 1, v___x_964_);
lean_ctor_set(v_reuseFailAlloc_970_, 2, v_buildTime_960_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*3, v_action_956_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*3 + 1, v_wantsRebuild_957_);
lean_ctor_set_uint8(v_reuseFailAlloc_970_, sizeof(void*)*3 + 2, v_canceled_958_);
v___x_966_ = v_reuseFailAlloc_970_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
lean_object* v___x_968_; 
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 1, v___x_966_);
v___x_968_ = v___x_953_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_a_951_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
else
{
lean_dec_ref(v_trace_941_);
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___boxed(lean_object* v_00_u03b1_975_, lean_object* v_caption_976_, lean_object* v_x_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Lake_addSubTrace(v_00_u03b1_975_, v_caption_976_, v_x_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
lean_dec_ref(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec(v_a_979_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg(lean_object* v_f_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___x_994_; 
lean_inc_ref(v_a_992_);
lean_inc_ref(v_a_991_);
lean_inc_ref(v_a_990_);
lean_inc(v_a_989_);
lean_inc(v_a_988_);
v___x_994_ = lean_apply_7(v_f_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, lean_box(0));
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg___boxed(lean_object* v_f_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lake_SpawnM_ofFn___redArg(v_f_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec_ref(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec(v_a_997_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn(lean_object* v_00_u03b1_1004_, lean_object* v_f_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_){
_start:
{
lean_object* v___x_1013_; 
lean_inc_ref(v_a_1011_);
lean_inc_ref(v_a_1010_);
lean_inc_ref(v_a_1009_);
lean_inc(v_a_1008_);
lean_inc(v_a_1007_);
v___x_1013_ = lean_apply_7(v_f_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, lean_box(0));
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_f_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lake_SpawnM_ofFn(v_00_u03b1_1014_, v_f_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_);
lean_dec_ref(v_a_1021_);
lean_dec_ref(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec(v_a_1017_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg(lean_object* v_self_1024_, lean_object* v_fetch_1025_, lean_object* v_pkg_x3f_1026_, lean_object* v_stack_1027_, lean_object* v_store_1028_, lean_object* v_ctx_1029_, lean_object* v_s_1030_){
_start:
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_apply_7(v_self_1024_, v_fetch_1025_, v_pkg_x3f_1026_, v_stack_1027_, v_store_1028_, v_ctx_1029_, v_s_1030_, lean_box(0));
return v___x_1032_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg___boxed(lean_object* v_self_1033_, lean_object* v_fetch_1034_, lean_object* v_pkg_x3f_1035_, lean_object* v_stack_1036_, lean_object* v_store_1037_, lean_object* v_ctx_1038_, lean_object* v_s_1039_, lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lake_SpawnM_toFn___redArg(v_self_1033_, v_fetch_1034_, v_pkg_x3f_1035_, v_stack_1036_, v_store_1037_, v_ctx_1038_, v_s_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn(lean_object* v_00_u03b1_1042_, lean_object* v_self_1043_, lean_object* v_fetch_1044_, lean_object* v_pkg_x3f_1045_, lean_object* v_stack_1046_, lean_object* v_store_1047_, lean_object* v_ctx_1048_, lean_object* v_s_1049_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_apply_7(v_self_1043_, v_fetch_1044_, v_pkg_x3f_1045_, v_stack_1046_, v_store_1047_, v_ctx_1048_, v_s_1049_, lean_box(0));
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___boxed(lean_object* v_00_u03b1_1052_, lean_object* v_self_1053_, lean_object* v_fetch_1054_, lean_object* v_pkg_x3f_1055_, lean_object* v_stack_1056_, lean_object* v_store_1057_, lean_object* v_ctx_1058_, lean_object* v_s_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Lake_SpawnM_toFn(v_00_u03b1_1052_, v_self_1053_, v_fetch_1054_, v_pkg_x3f_1055_, v_stack_1056_, v_store_1057_, v_ctx_1058_, v_s_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg(lean_object* v_x_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v_trace_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v_trace_1070_ = lean_ctor_get(v_a_1068_, 1);
lean_inc_ref(v_trace_1070_);
lean_inc_ref(v_a_1067_);
lean_inc_ref(v_a_1066_);
lean_inc(v_a_1065_);
lean_inc(v_a_1064_);
v___x_1071_ = lean_apply_7(v_x_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_trace_1070_, lean_box(0));
v___x_1072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v_a_1068_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg___boxed(lean_object* v_x_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lake_JobM_runSpawnM___redArg(v_x_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec(v_a_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM(lean_object* v_00_u03b1_1082_, lean_object* v_x_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_trace_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v_trace_1091_ = lean_ctor_get(v_a_1089_, 1);
lean_inc_ref(v_trace_1091_);
lean_inc_ref(v_a_1088_);
lean_inc_ref(v_a_1087_);
lean_inc(v_a_1086_);
lean_inc(v_a_1085_);
v___x_1092_ = lean_apply_7(v_x_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_trace_1091_, lean_box(0));
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v_a_1089_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___boxed(lean_object* v_00_u03b1_1094_, lean_object* v_x_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lake_JobM_runSpawnM(v_00_u03b1_1094_, v_x_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_);
lean_dec_ref(v_a_1100_);
lean_dec_ref(v_a_1099_);
lean_dec(v_a_1098_);
lean_dec(v_a_1097_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg(lean_object* v_x_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_){
_start:
{
uint8_t v___x_1114_; uint8_t v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1114_ = 0;
v___x_1115_ = 0;
v___x_1116_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1117_ = lean_unsigned_to_nat(0u);
v___x_1118_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1118_, 0, v_a_1112_);
lean_ctor_set(v___x_1118_, 1, v___x_1116_);
lean_ctor_set(v___x_1118_, 2, v___x_1117_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*3, v___x_1114_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*3 + 1, v___x_1115_);
lean_ctor_set_uint8(v___x_1118_, sizeof(void*)*3 + 2, v___x_1115_);
lean_inc_ref(v_a_1111_);
lean_inc_ref(v_a_1110_);
lean_inc(v_a_1109_);
lean_inc(v_a_1108_);
v___x_1119_ = lean_apply_7(v_x_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v___x_1118_, lean_box(0));
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1129_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 1);
v_a_1121_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1123_ = v___x_1119_;
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1120_);
lean_inc(v_a_1121_);
lean_dec(v___x_1119_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1129_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v_log_1125_; lean_object* v___x_1127_; 
v_log_1125_ = lean_ctor_get(v_a_1120_, 0);
lean_inc_ref(v_log_1125_);
lean_dec(v_a_1120_);
if (v_isShared_1124_ == 0)
{
lean_ctor_set(v___x_1123_, 1, v_log_1125_);
v___x_1127_ = v___x_1123_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1121_);
lean_ctor_set(v_reuseFailAlloc_1128_, 1, v_log_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1139_; 
v_a_1130_ = lean_ctor_get(v___x_1119_, 1);
v_a_1131_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1133_ = v___x_1119_;
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1130_);
lean_inc(v_a_1131_);
lean_dec(v___x_1119_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1139_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_log_1135_; lean_object* v___x_1137_; 
v_log_1135_ = lean_ctor_get(v_a_1130_, 0);
lean_inc_ref(v_log_1135_);
lean_dec(v_a_1130_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v_log_1135_);
v___x_1137_ = v___x_1133_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1131_);
lean_ctor_set(v_reuseFailAlloc_1138_, 1, v_log_1135_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg___boxed(lean_object* v_x_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lake_FetchM_runJobM___redArg(v_x_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_);
lean_dec_ref(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1142_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM(lean_object* v_00_u03b1_1149_, lean_object* v_x_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
uint8_t v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1158_ = 0;
v___x_1159_ = 0;
v___x_1160_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1162_, 0, v_a_1156_);
lean_ctor_set(v___x_1162_, 1, v___x_1160_);
lean_ctor_set(v___x_1162_, 2, v___x_1161_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*3, v___x_1158_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*3 + 1, v___x_1159_);
lean_ctor_set_uint8(v___x_1162_, sizeof(void*)*3 + 2, v___x_1159_);
lean_inc_ref(v_a_1155_);
lean_inc_ref(v_a_1154_);
lean_inc(v_a_1153_);
lean_inc(v_a_1152_);
v___x_1163_ = lean_apply_7(v_x_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v___x_1162_, lean_box(0));
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1173_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 1);
v_a_1165_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1167_ = v___x_1163_;
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1164_);
lean_inc(v_a_1165_);
lean_dec(v___x_1163_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1173_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_log_1169_; lean_object* v___x_1171_; 
v_log_1169_ = lean_ctor_get(v_a_1164_, 0);
lean_inc_ref(v_log_1169_);
lean_dec(v_a_1164_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v_log_1169_);
v___x_1171_ = v___x_1167_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1165_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v_log_1169_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
else
{
lean_object* v_a_1174_; lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1183_; 
v_a_1174_ = lean_ctor_get(v___x_1163_, 1);
v_a_1175_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1183_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1183_ == 0)
{
v___x_1177_ = v___x_1163_;
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1174_);
lean_inc(v_a_1175_);
lean_dec(v___x_1163_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1183_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v_log_1179_; lean_object* v___x_1181_; 
v_log_1179_ = lean_ctor_get(v_a_1174_, 0);
lean_inc_ref(v_log_1179_);
lean_dec(v_a_1174_);
if (v_isShared_1178_ == 0)
{
lean_ctor_set(v___x_1177_, 1, v_log_1179_);
v___x_1181_ = v___x_1177_;
goto v_reusejp_1180_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1175_);
lean_ctor_set(v_reuseFailAlloc_1182_, 1, v_log_1179_);
v___x_1181_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1180_;
}
v_reusejp_1180_:
{
return v___x_1181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_x_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lake_FetchM_runJobM(v_00_u03b1_1184_, v_x_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_);
lean_dec_ref(v_a_1190_);
lean_dec_ref(v_a_1189_);
lean_dec(v_a_1188_);
lean_dec(v_a_1187_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg(lean_object* v_x_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v_log_1204_; uint8_t v_action_1205_; uint8_t v_wantsRebuild_1206_; uint8_t v_canceled_1207_; lean_object* v_trace_1208_; lean_object* v_buildTime_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1238_; 
v_log_1204_ = lean_ctor_get(v_a_1202_, 0);
v_action_1205_ = lean_ctor_get_uint8(v_a_1202_, sizeof(void*)*3);
v_wantsRebuild_1206_ = lean_ctor_get_uint8(v_a_1202_, sizeof(void*)*3 + 1);
v_canceled_1207_ = lean_ctor_get_uint8(v_a_1202_, sizeof(void*)*3 + 2);
v_trace_1208_ = lean_ctor_get(v_a_1202_, 1);
v_buildTime_1209_ = lean_ctor_get(v_a_1202_, 2);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_a_1202_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1211_ = v_a_1202_;
v_isShared_1212_ = v_isSharedCheck_1238_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_buildTime_1209_);
lean_inc(v_trace_1208_);
lean_inc(v_log_1204_);
lean_dec(v_a_1202_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1238_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; 
lean_inc_ref(v_a_1201_);
lean_inc_ref(v_a_1200_);
lean_inc(v_a_1199_);
lean_inc(v_a_1198_);
v___x_1213_ = lean_apply_7(v_x_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_log_1204_, lean_box(0));
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1225_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_a_1215_ = lean_ctor_get(v___x_1213_, 1);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1217_ = v___x_1213_;
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1225_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_a_1215_);
v___x_1220_ = v___x_1211_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1215_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_trace_1208_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_buildTime_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1224_, sizeof(void*)*3, v_action_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1224_, sizeof(void*)*3 + 1, v_wantsRebuild_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1224_, sizeof(void*)*3 + 2, v_canceled_1207_);
v___x_1220_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
lean_object* v___x_1222_; 
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v___x_1220_);
v___x_1222_ = v___x_1217_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1214_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v_a_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1237_; 
v_a_1226_ = lean_ctor_get(v___x_1213_, 0);
v_a_1227_ = lean_ctor_get(v___x_1213_, 1);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1229_ = v___x_1213_;
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_a_1227_);
lean_inc(v_a_1226_);
lean_dec(v___x_1213_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1237_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1232_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_a_1227_);
v___x_1232_ = v___x_1211_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1227_);
lean_ctor_set(v_reuseFailAlloc_1236_, 1, v_trace_1208_);
lean_ctor_set(v_reuseFailAlloc_1236_, 2, v_buildTime_1209_);
lean_ctor_set_uint8(v_reuseFailAlloc_1236_, sizeof(void*)*3, v_action_1205_);
lean_ctor_set_uint8(v_reuseFailAlloc_1236_, sizeof(void*)*3 + 1, v_wantsRebuild_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1236_, sizeof(void*)*3 + 2, v_canceled_1207_);
v___x_1232_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1234_; 
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 1, v___x_1232_);
v___x_1234_ = v___x_1229_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1226_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v___x_1232_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg___boxed(lean_object* v_x_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lake_JobM_runFetchM___redArg(v_x_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
lean_dec_ref(v_a_1244_);
lean_dec_ref(v_a_1243_);
lean_dec(v_a_1242_);
lean_dec(v_a_1241_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM(lean_object* v_00_u03b1_1248_, lean_object* v_x_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_log_1257_; uint8_t v_action_1258_; uint8_t v_wantsRebuild_1259_; uint8_t v_canceled_1260_; lean_object* v_trace_1261_; lean_object* v_buildTime_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1291_; 
v_log_1257_ = lean_ctor_get(v_a_1255_, 0);
v_action_1258_ = lean_ctor_get_uint8(v_a_1255_, sizeof(void*)*3);
v_wantsRebuild_1259_ = lean_ctor_get_uint8(v_a_1255_, sizeof(void*)*3 + 1);
v_canceled_1260_ = lean_ctor_get_uint8(v_a_1255_, sizeof(void*)*3 + 2);
v_trace_1261_ = lean_ctor_get(v_a_1255_, 1);
v_buildTime_1262_ = lean_ctor_get(v_a_1255_, 2);
v_isSharedCheck_1291_ = !lean_is_exclusive(v_a_1255_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1264_ = v_a_1255_;
v_isShared_1265_ = v_isSharedCheck_1291_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_buildTime_1262_);
lean_inc(v_trace_1261_);
lean_inc(v_log_1257_);
lean_dec(v_a_1255_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1291_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; 
lean_inc_ref(v_a_1254_);
lean_inc_ref(v_a_1253_);
lean_inc(v_a_1252_);
lean_inc(v_a_1251_);
v___x_1266_ = lean_apply_7(v_x_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_log_1257_, lean_box(0));
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1278_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_a_1268_ = lean_ctor_get(v___x_1266_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1270_ = v___x_1266_;
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_a_1268_);
v___x_1273_ = v___x_1264_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1268_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_trace_1261_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_buildTime_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*3, v_action_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*3 + 1, v_wantsRebuild_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*3 + 2, v_canceled_1260_);
v___x_1273_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1275_; 
if (v_isShared_1271_ == 0)
{
lean_ctor_set(v___x_1270_, 1, v___x_1273_);
v___x_1275_ = v___x_1270_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1267_);
lean_ctor_set(v_reuseFailAlloc_1276_, 1, v___x_1273_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
else
{
lean_object* v_a_1279_; lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1290_; 
v_a_1279_ = lean_ctor_get(v___x_1266_, 0);
v_a_1280_ = lean_ctor_get(v___x_1266_, 1);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1282_ = v___x_1266_;
v_isShared_1283_ = v_isSharedCheck_1290_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_inc(v_a_1279_);
lean_dec(v___x_1266_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1290_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v_a_1280_);
v___x_1285_ = v___x_1264_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1280_);
lean_ctor_set(v_reuseFailAlloc_1289_, 1, v_trace_1261_);
lean_ctor_set(v_reuseFailAlloc_1289_, 2, v_buildTime_1262_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*3, v_action_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*3 + 1, v_wantsRebuild_1259_);
lean_ctor_set_uint8(v_reuseFailAlloc_1289_, sizeof(void*)*3 + 2, v_canceled_1260_);
v___x_1285_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
lean_object* v___x_1287_; 
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 1, v___x_1285_);
v___x_1287_ = v___x_1282_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1279_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_x_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v_res_1301_; 
v_res_1301_ = l_Lake_JobM_runFetchM(v_00_u03b1_1292_, v_x_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
lean_dec_ref(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec(v_a_1295_);
return v_res_1301_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0(lean_object* v_inst_1304_, lean_object* v_caption_1305_, uint8_t v_optional_1306_, lean_object* v_toPure_1307_, lean_object* v_____do__lift_1308_){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1309_, 0, v_____do__lift_1308_);
lean_ctor_set(v___x_1309_, 1, v_inst_1304_);
lean_ctor_set(v___x_1309_, 2, v_caption_1305_);
lean_ctor_set_uint8(v___x_1309_, sizeof(void*)*3, v_optional_1306_);
v___x_1310_ = lean_apply_2(v_toPure_1307_, lean_box(0), v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0___boxed(lean_object* v_inst_1311_, lean_object* v_caption_1312_, lean_object* v_optional_1313_, lean_object* v_toPure_1314_, lean_object* v_____do__lift_1315_){
_start:
{
uint8_t v_optional_boxed_1316_; lean_object* v_res_1317_; 
v_optional_boxed_1316_ = lean_unbox(v_optional_1313_);
v_res_1317_ = l_Lake_Job_bindTask___redArg___lam__0(v_inst_1311_, v_caption_1312_, v_optional_boxed_1316_, v_toPure_1314_, v_____do__lift_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg(lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_f_1320_, lean_object* v_self_1321_){
_start:
{
lean_object* v_toApplicative_1322_; lean_object* v_toBind_1323_; lean_object* v_task_1324_; lean_object* v_caption_1325_; uint8_t v_optional_1326_; lean_object* v_toPure_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___f_1330_; lean_object* v___x_1331_; 
v_toApplicative_1322_ = lean_ctor_get(v_inst_1318_, 0);
lean_inc_ref(v_toApplicative_1322_);
v_toBind_1323_ = lean_ctor_get(v_inst_1318_, 1);
lean_inc(v_toBind_1323_);
lean_dec_ref(v_inst_1318_);
v_task_1324_ = lean_ctor_get(v_self_1321_, 0);
lean_inc_ref(v_task_1324_);
v_caption_1325_ = lean_ctor_get(v_self_1321_, 2);
lean_inc_ref(v_caption_1325_);
v_optional_1326_ = lean_ctor_get_uint8(v_self_1321_, sizeof(void*)*3);
lean_dec_ref(v_self_1321_);
v_toPure_1327_ = lean_ctor_get(v_toApplicative_1322_, 1);
lean_inc(v_toPure_1327_);
lean_dec_ref(v_toApplicative_1322_);
v___x_1328_ = lean_apply_1(v_f_1320_, v_task_1324_);
v___x_1329_ = lean_box(v_optional_1326_);
v___f_1330_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1330_, 0, v_inst_1319_);
lean_closure_set(v___f_1330_, 1, v_caption_1325_);
lean_closure_set(v___f_1330_, 2, v___x_1329_);
lean_closure_set(v___f_1330_, 3, v_toPure_1327_);
v___x_1331_ = lean_apply_4(v_toBind_1323_, lean_box(0), lean_box(0), v___x_1328_, v___f_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask(lean_object* v_m_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_00_u03b1_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_f_1337_, lean_object* v_self_1338_){
_start:
{
lean_object* v_toApplicative_1339_; lean_object* v_toBind_1340_; lean_object* v_task_1341_; lean_object* v_caption_1342_; uint8_t v_optional_1343_; lean_object* v_toPure_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; 
v_toApplicative_1339_ = lean_ctor_get(v_inst_1335_, 0);
lean_inc_ref(v_toApplicative_1339_);
v_toBind_1340_ = lean_ctor_get(v_inst_1335_, 1);
lean_inc(v_toBind_1340_);
lean_dec_ref(v_inst_1335_);
v_task_1341_ = lean_ctor_get(v_self_1338_, 0);
lean_inc_ref(v_task_1341_);
v_caption_1342_ = lean_ctor_get(v_self_1338_, 2);
lean_inc_ref(v_caption_1342_);
v_optional_1343_ = lean_ctor_get_uint8(v_self_1338_, sizeof(void*)*3);
lean_dec_ref(v_self_1338_);
v_toPure_1344_ = lean_ctor_get(v_toApplicative_1339_, 1);
lean_inc(v_toPure_1344_);
lean_dec_ref(v_toApplicative_1339_);
v___x_1345_ = lean_apply_1(v_f_1337_, v_task_1341_);
v___x_1346_ = lean_box(v_optional_1343_);
v___f_1347_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1347_, 0, v_inst_1336_);
lean_closure_set(v___f_1347_, 1, v_caption_1342_);
lean_closure_set(v___f_1347_, 2, v___x_1346_);
lean_closure_set(v___f_1347_, 3, v_toPure_1344_);
v___x_1348_ = lean_apply_4(v_toBind_1340_, lean_box(0), lean_box(0), v___x_1345_, v___f_1347_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Job_sync_spec__0(lean_object* v_msg_1350_){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_1352_ = lean_panic_fn_borrowed(v___x_1351_, v_msg_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0(lean_object* v_val_1353_, lean_object* v_val_1354_, lean_object* v_a_x3f_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1358_ = lean_get_set_stdout(v_val_1353_);
lean_dec_ref(v___x_1358_);
v___x_1359_ = lean_box(0);
v___x_1360_ = lean_get_set_stderr(v_val_1354_);
lean_dec_ref(v___x_1360_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1359_);
lean_ctor_set(v___x_1361_, 1, v___y_1356_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0___boxed(lean_object* v_val_1362_, lean_object* v_val_1363_, lean_object* v_a_x3f_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lake_Job_sync___redArg___lam__0(v_val_1362_, v_val_1363_, v_a_x3f_1364_, v___y_1365_);
lean_dec(v_a_x3f_1364_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1(lean_object* v_a_1368_, lean_object* v_____r_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; 
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_a_1368_);
lean_ctor_set(v___x_1377_, 1, v___y_1375_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1___boxed(lean_object* v_a_1378_, lean_object* v_____r_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_Lake_Job_sync___redArg___lam__1(v_a_1378_, v_____r_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
return v_res_1387_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__0(void){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = l_ByteArray_empty;
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___x_1388_);
return v___x_1390_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__2(void){
_start:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; uint8_t v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1395_ = 0;
v___x_1396_ = 0;
v___x_1397_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1398_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1398_, 0, v___x_1397_);
lean_ctor_set(v___x_1398_, 1, v___x_1394_);
lean_ctor_set(v___x_1398_, 2, v___x_1393_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*3, v___x_1396_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*3 + 1, v___x_1395_);
lean_ctor_set_uint8(v___x_1398_, sizeof(void*)*3 + 2, v___x_1395_);
return v___x_1398_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__7(void){
_start:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1403_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__6));
v___x_1404_ = lean_unsigned_to_nat(46u);
v___x_1405_ = lean_unsigned_to_nat(193u);
v___x_1406_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__5));
v___x_1407_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__4));
v___x_1408_ = l_mkPanicMessageWithDecl(v___x_1407_, v___x_1406_, v___x_1405_, v___x_1404_, v___x_1403_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg(lean_object* v_inst_1409_, lean_object* v_act_1410_, lean_object* v_caption_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_){
_start:
{
lean_object* v_val_1419_; lean_object* v_a_1424_; lean_object* v_a_1425_; lean_object* v___y_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1431_ = lean_st_mk_ref(v___x_1430_);
lean_inc(v___x_1431_);
v___x_1432_ = l_IO_FS_Stream_ofBuffer(v___x_1431_);
lean_inc_ref(v___x_1432_);
v___x_1433_ = lean_get_set_stdout(v___x_1432_);
v___x_1434_ = lean_get_set_stderr(v___x_1432_);
v___x_1435_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__2, &l_Lake_Job_sync___redArg___closed__2_once, _init_l_Lake_Job_sync___redArg___closed__2);
lean_inc_ref(v_a_1416_);
lean_inc_ref(v_a_1415_);
lean_inc(v_a_1414_);
lean_inc(v_a_1413_);
lean_inc_ref(v_a_1412_);
v___x_1436_ = lean_apply_7(v_act_1410_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v___x_1435_, lean_box(0));
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_object* v_a_1437_; lean_object* v_a_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_a_1441_; lean_object* v_log_1442_; uint8_t v_action_1443_; uint8_t v_wantsRebuild_1444_; uint8_t v_canceled_1445_; lean_object* v_trace_1446_; lean_object* v_buildTime_1447_; lean_object* v___x_1448_; lean_object* v___y_1450_; lean_object* v_data_1475_; uint8_t v___x_1476_; 
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
lean_inc_n(v_a_1437_, 2);
v_a_1438_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_a_1438_);
lean_dec_ref_known(v___x_1436_, 2);
v___x_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1439_, 0, v_a_1437_);
v___x_1440_ = l_Lake_Job_sync___redArg___lam__0(v___x_1433_, v___x_1434_, v___x_1439_, v_a_1438_);
lean_dec_ref_known(v___x_1439_, 1);
v_a_1441_ = lean_ctor_get(v___x_1440_, 1);
lean_inc(v_a_1441_);
lean_dec_ref(v___x_1440_);
v_log_1442_ = lean_ctor_get(v_a_1441_, 0);
v_action_1443_ = lean_ctor_get_uint8(v_a_1441_, sizeof(void*)*3);
v_wantsRebuild_1444_ = lean_ctor_get_uint8(v_a_1441_, sizeof(void*)*3 + 1);
v_canceled_1445_ = lean_ctor_get_uint8(v_a_1441_, sizeof(void*)*3 + 2);
v_trace_1446_ = lean_ctor_get(v_a_1441_, 1);
v_buildTime_1447_ = lean_ctor_get(v_a_1441_, 2);
v___x_1448_ = lean_st_ref_get(v___x_1431_);
lean_dec(v___x_1431_);
v_data_1475_ = lean_ctor_get(v___x_1448_, 0);
lean_inc_ref(v_data_1475_);
lean_dec(v___x_1448_);
v___x_1476_ = lean_string_validate_utf8(v_data_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec_ref(v_data_1475_);
v___x_1477_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1478_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1477_);
v___y_1450_ = v___x_1478_;
goto v___jp_1449_;
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_string_from_utf8_unchecked(v_data_1475_);
v___y_1450_ = v___x_1479_;
goto v___jp_1449_;
}
v___jp_1449_:
{
lean_object* v___x_1451_; uint8_t v___x_1452_; 
v___x_1451_ = lean_string_utf8_byte_size(v___y_1450_);
v___x_1452_ = lean_nat_dec_eq(v___x_1451_, v___x_1429_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1469_; 
lean_inc(v_buildTime_1447_);
lean_inc_ref(v_trace_1446_);
lean_inc_ref(v_log_1442_);
v_isSharedCheck_1469_ = !lean_is_exclusive(v_a_1441_);
if (v_isSharedCheck_1469_ == 0)
{
lean_object* v_unused_1470_; lean_object* v_unused_1471_; lean_object* v_unused_1472_; 
v_unused_1470_ = lean_ctor_get(v_a_1441_, 2);
lean_dec(v_unused_1470_);
v_unused_1471_ = lean_ctor_get(v_a_1441_, 1);
lean_dec(v_unused_1471_);
v_unused_1472_ = lean_ctor_get(v_a_1441_, 0);
lean_dec(v_unused_1472_);
v___x_1454_ = v_a_1441_;
v_isShared_1455_ = v_isSharedCheck_1469_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v_a_1441_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1469_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; uint8_t v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; 
v___x_1456_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1457_, 0, v___y_1450_);
lean_ctor_set(v___x_1457_, 1, v___x_1429_);
lean_ctor_set(v___x_1457_, 2, v___x_1451_);
v___x_1458_ = l_String_Slice_trimAscii(v___x_1457_);
v___x_1459_ = l_String_Slice_toString(v___x_1458_);
lean_dec_ref(v___x_1458_);
v___x_1460_ = lean_string_append(v___x_1456_, v___x_1459_);
lean_dec_ref(v___x_1459_);
v___x_1461_ = 1;
v___x_1462_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1462_, 0, v___x_1460_);
lean_ctor_set_uint8(v___x_1462_, sizeof(void*)*1, v___x_1461_);
v___x_1463_ = lean_box(0);
v___x_1464_ = lean_array_push(v_log_1442_, v___x_1462_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1464_);
v___x_1466_ = v___x_1454_;
goto v_reusejp_1465_;
}
else
{
lean_object* v_reuseFailAlloc_1468_; 
v_reuseFailAlloc_1468_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1468_, 0, v___x_1464_);
lean_ctor_set(v_reuseFailAlloc_1468_, 1, v_trace_1446_);
lean_ctor_set(v_reuseFailAlloc_1468_, 2, v_buildTime_1447_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*3, v_action_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*3 + 1, v_wantsRebuild_1444_);
lean_ctor_set_uint8(v_reuseFailAlloc_1468_, sizeof(void*)*3 + 2, v_canceled_1445_);
v___x_1466_ = v_reuseFailAlloc_1468_;
goto v_reusejp_1465_;
}
v_reusejp_1465_:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Lake_Job_sync___redArg___lam__1(v_a_1437_, v___x_1463_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v___x_1466_);
lean_dec_ref(v_a_1412_);
v___y_1428_ = v___x_1467_;
goto v___jp_1427_;
}
}
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec_ref(v___y_1450_);
v___x_1473_ = lean_box(0);
v___x_1474_ = l_Lake_Job_sync___redArg___lam__1(v_a_1437_, v___x_1473_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1441_);
lean_dec_ref(v_a_1412_);
v___y_1428_ = v___x_1474_;
goto v___jp_1427_;
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v_a_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v_a_1484_; 
lean_dec(v___x_1431_);
lean_dec_ref(v_a_1412_);
v_a_1480_ = lean_ctor_get(v___x_1436_, 0);
lean_inc(v_a_1480_);
v_a_1481_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_a_1481_);
lean_dec_ref_known(v___x_1436_, 2);
v___x_1482_ = lean_box(0);
v___x_1483_ = l_Lake_Job_sync___redArg___lam__0(v___x_1433_, v___x_1434_, v___x_1482_, v_a_1481_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 1);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v_a_1424_ = v_a_1480_;
v_a_1425_ = v_a_1484_;
goto v___jp_1423_;
}
v___jp_1418_:
{
lean_object* v___x_1420_; uint8_t v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = lean_task_pure(v_val_1419_);
v___x_1421_ = 0;
v___x_1422_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v_inst_1409_);
lean_ctor_set(v___x_1422_, 2, v_caption_1411_);
lean_ctor_set_uint8(v___x_1422_, sizeof(void*)*3, v___x_1421_);
return v___x_1422_;
}
v___jp_1423_:
{
lean_object* v___x_1426_; 
v___x_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1426_, 0, v_a_1424_);
lean_ctor_set(v___x_1426_, 1, v_a_1425_);
v_val_1419_ = v___x_1426_;
goto v___jp_1418_;
}
v___jp_1427_:
{
v_val_1419_ = v___y_1428_;
goto v___jp_1418_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___boxed(lean_object* v_inst_1485_, lean_object* v_act_1486_, lean_object* v_caption_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_res_1494_; 
v_res_1494_ = l_Lake_Job_sync___redArg(v_inst_1485_, v_act_1486_, v_caption_1487_, v_a_1488_, v_a_1489_, v_a_1490_, v_a_1491_, v_a_1492_);
lean_dec_ref(v_a_1492_);
lean_dec_ref(v_a_1491_);
lean_dec(v_a_1490_);
lean_dec(v_a_1489_);
return v_res_1494_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync(lean_object* v_00_u03b1_1495_, lean_object* v_inst_1496_, lean_object* v_act_1497_, lean_object* v_caption_1498_, lean_object* v_a_1499_, lean_object* v_a_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lake_Job_sync___redArg(v_inst_1496_, v_act_1497_, v_caption_1498_, v_a_1499_, v_a_1500_, v_a_1501_, v_a_1502_, v_a_1503_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___boxed(lean_object* v_00_u03b1_1507_, lean_object* v_inst_1508_, lean_object* v_act_1509_, lean_object* v_caption_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lake_Job_sync(v_00_u03b1_1507_, v_inst_1508_, v_act_1509_, v_caption_1510_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
lean_dec_ref(v_a_1516_);
lean_dec_ref(v_a_1515_);
lean_dec_ref(v_a_1514_);
lean_dec(v_a_1513_);
lean_dec(v_a_1512_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1(lean_object* v___x_1519_, lean_object* v___x_1520_, uint8_t v___x_1521_, uint8_t v___x_1522_, lean_object* v___x_1523_, lean_object* v___x_1524_, lean_object* v_act_1525_, lean_object* v_a_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_){
_start:
{
lean_object* v_a_1533_; lean_object* v_a_1534_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1536_ = lean_st_mk_ref(v___x_1519_);
lean_inc(v___x_1536_);
v___x_1537_ = l_IO_FS_Stream_ofBuffer(v___x_1536_);
lean_inc_ref(v___x_1537_);
v___x_1538_ = lean_get_set_stdout(v___x_1537_);
v___x_1539_ = lean_get_set_stderr(v___x_1537_);
lean_inc(v___x_1524_);
v___x_1540_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1540_, 0, v___x_1520_);
lean_ctor_set(v___x_1540_, 1, v___x_1523_);
lean_ctor_set(v___x_1540_, 2, v___x_1524_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*3, v___x_1521_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*3 + 1, v___x_1522_);
lean_ctor_set_uint8(v___x_1540_, sizeof(void*)*3 + 2, v___x_1522_);
lean_inc_ref(v_a_1530_);
lean_inc_ref(v_a_1529_);
lean_inc(v_a_1528_);
lean_inc(v_a_1527_);
v___x_1541_ = lean_apply_7(v_act_1525_, v_a_1526_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v___x_1540_, lean_box(0));
if (lean_obj_tag(v___x_1541_) == 0)
{
lean_object* v_a_1542_; lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1589_; 
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_a_1543_ = lean_ctor_get(v___x_1541_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1545_ = v___x_1541_;
v_isShared_1546_ = v_isSharedCheck_1589_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1589_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___y_1548_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v_a_1554_; lean_object* v_log_1555_; uint8_t v_action_1556_; uint8_t v_wantsRebuild_1557_; uint8_t v_canceled_1558_; lean_object* v_trace_1559_; lean_object* v_buildTime_1560_; lean_object* v___x_1561_; lean_object* v___y_1563_; lean_object* v_data_1584_; uint8_t v___x_1585_; 
lean_inc(v_a_1542_);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_a_1542_);
v___x_1553_ = l_Lake_Job_sync___redArg___lam__0(v___x_1538_, v___x_1539_, v___x_1552_, v_a_1543_);
lean_dec_ref_known(v___x_1552_, 1);
v_a_1554_ = lean_ctor_get(v___x_1553_, 1);
lean_inc(v_a_1554_);
lean_dec_ref(v___x_1553_);
v_log_1555_ = lean_ctor_get(v_a_1554_, 0);
v_action_1556_ = lean_ctor_get_uint8(v_a_1554_, sizeof(void*)*3);
v_wantsRebuild_1557_ = lean_ctor_get_uint8(v_a_1554_, sizeof(void*)*3 + 1);
v_canceled_1558_ = lean_ctor_get_uint8(v_a_1554_, sizeof(void*)*3 + 2);
v_trace_1559_ = lean_ctor_get(v_a_1554_, 1);
v_buildTime_1560_ = lean_ctor_get(v_a_1554_, 2);
v___x_1561_ = lean_st_ref_get(v___x_1536_);
lean_dec(v___x_1536_);
v_data_1584_ = lean_ctor_get(v___x_1561_, 0);
lean_inc_ref(v_data_1584_);
lean_dec(v___x_1561_);
v___x_1585_ = lean_string_validate_utf8(v_data_1584_);
if (v___x_1585_ == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
lean_dec_ref(v_data_1584_);
v___x_1586_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1587_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1586_);
v___y_1563_ = v___x_1587_;
goto v___jp_1562_;
}
else
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_string_from_utf8_unchecked(v_data_1584_);
v___y_1563_ = v___x_1588_;
goto v___jp_1562_;
}
v___jp_1547_:
{
lean_object* v___x_1550_; 
if (v_isShared_1546_ == 0)
{
lean_ctor_set(v___x_1545_, 1, v___y_1548_);
v___x_1550_ = v___x_1545_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v_a_1542_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___y_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
v___jp_1562_:
{
lean_object* v___x_1564_; uint8_t v___x_1565_; 
v___x_1564_ = lean_string_utf8_byte_size(v___y_1563_);
v___x_1565_ = lean_nat_dec_eq(v___x_1564_, v___x_1524_);
if (v___x_1565_ == 0)
{
lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1580_; 
lean_inc(v_buildTime_1560_);
lean_inc_ref(v_trace_1559_);
lean_inc_ref(v_log_1555_);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_a_1554_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; 
v_unused_1581_ = lean_ctor_get(v_a_1554_, 2);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_a_1554_, 1);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_a_1554_, 0);
lean_dec(v_unused_1583_);
v___x_1567_ = v_a_1554_;
v_isShared_1568_ = v_isSharedCheck_1580_;
goto v_resetjp_1566_;
}
else
{
lean_dec(v_a_1554_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1580_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1569_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1570_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1570_, 0, v___y_1563_);
lean_ctor_set(v___x_1570_, 1, v___x_1524_);
lean_ctor_set(v___x_1570_, 2, v___x_1564_);
v___x_1571_ = l_String_Slice_trimAscii(v___x_1570_);
v___x_1572_ = l_String_Slice_toString(v___x_1571_);
lean_dec_ref(v___x_1571_);
v___x_1573_ = lean_string_append(v___x_1569_, v___x_1572_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = 1;
v___x_1575_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set_uint8(v___x_1575_, sizeof(void*)*1, v___x_1574_);
v___x_1576_ = lean_array_push(v_log_1555_, v___x_1575_);
if (v_isShared_1568_ == 0)
{
lean_ctor_set(v___x_1567_, 0, v___x_1576_);
v___x_1578_ = v___x_1567_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_trace_1559_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_buildTime_1560_);
lean_ctor_set_uint8(v_reuseFailAlloc_1579_, sizeof(void*)*3, v_action_1556_);
lean_ctor_set_uint8(v_reuseFailAlloc_1579_, sizeof(void*)*3 + 1, v_wantsRebuild_1557_);
lean_ctor_set_uint8(v_reuseFailAlloc_1579_, sizeof(void*)*3 + 2, v_canceled_1558_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
v___y_1548_ = v___x_1578_;
goto v___jp_1547_;
}
}
}
else
{
lean_dec_ref(v___y_1563_);
lean_dec(v___x_1524_);
v___y_1548_ = v_a_1554_;
goto v___jp_1547_;
}
}
}
}
else
{
lean_object* v_a_1590_; lean_object* v_a_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v_a_1594_; 
lean_dec(v___x_1536_);
lean_dec(v___x_1524_);
v_a_1590_ = lean_ctor_get(v___x_1541_, 0);
lean_inc(v_a_1590_);
v_a_1591_ = lean_ctor_get(v___x_1541_, 1);
lean_inc(v_a_1591_);
lean_dec_ref_known(v___x_1541_, 2);
v___x_1592_ = lean_box(0);
v___x_1593_ = l_Lake_Job_sync___redArg___lam__0(v___x_1538_, v___x_1539_, v___x_1592_, v_a_1591_);
v_a_1594_ = lean_ctor_get(v___x_1593_, 1);
lean_inc(v_a_1594_);
lean_dec_ref(v___x_1593_);
v_a_1533_ = v_a_1590_;
v_a_1534_ = v_a_1594_;
goto v___jp_1532_;
}
v___jp_1532_:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1535_, 0, v_a_1533_);
lean_ctor_set(v___x_1535_, 1, v_a_1534_);
return v___x_1535_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1___boxed(lean_object* v___x_1595_, lean_object* v___x_1596_, lean_object* v___x_1597_, lean_object* v___x_1598_, lean_object* v___x_1599_, lean_object* v___x_1600_, lean_object* v_act_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v___y_1607_){
_start:
{
uint8_t v___x_28483__boxed_1608_; uint8_t v___x_28484__boxed_1609_; lean_object* v_res_1610_; 
v___x_28483__boxed_1608_ = lean_unbox(v___x_1597_);
v___x_28484__boxed_1609_ = lean_unbox(v___x_1598_);
v_res_1610_ = l_Lake_Job_async___redArg___lam__1(v___x_1595_, v___x_1596_, v___x_28483__boxed_1608_, v___x_28484__boxed_1609_, v___x_1599_, v___x_1600_, v_act_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_);
lean_dec_ref(v_a_1606_);
lean_dec_ref(v_a_1605_);
lean_dec(v_a_1604_);
lean_dec(v_a_1603_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg(lean_object* v_inst_1611_, lean_object* v_act_1612_, lean_object* v_prio_1613_, lean_object* v_caption_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___f_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1623_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1624_ = 0;
v___x_1625_ = 0;
v___x_1626_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1627_ = lean_box(v___x_1624_);
v___x_1628_ = lean_box(v___x_1625_);
lean_inc_ref(v_a_1619_);
lean_inc_ref(v_a_1618_);
lean_inc(v_a_1617_);
lean_inc(v_a_1616_);
v___f_1629_ = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__1___boxed), 13, 12);
lean_closure_set(v___f_1629_, 0, v___x_1622_);
lean_closure_set(v___f_1629_, 1, v___x_1623_);
lean_closure_set(v___f_1629_, 2, v___x_1627_);
lean_closure_set(v___f_1629_, 3, v___x_1628_);
lean_closure_set(v___f_1629_, 4, v___x_1626_);
lean_closure_set(v___f_1629_, 5, v___x_1621_);
lean_closure_set(v___f_1629_, 6, v_act_1612_);
lean_closure_set(v___f_1629_, 7, v_a_1615_);
lean_closure_set(v___f_1629_, 8, v_a_1616_);
lean_closure_set(v___f_1629_, 9, v_a_1617_);
lean_closure_set(v___f_1629_, 10, v_a_1618_);
lean_closure_set(v___f_1629_, 11, v_a_1619_);
v___x_1630_ = lean_io_as_task(v___f_1629_, v_prio_1613_);
v___x_1631_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
lean_ctor_set(v___x_1631_, 1, v_inst_1611_);
lean_ctor_set(v___x_1631_, 2, v_caption_1614_);
lean_ctor_set_uint8(v___x_1631_, sizeof(void*)*3, v___x_1625_);
return v___x_1631_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___boxed(lean_object* v_inst_1632_, lean_object* v_act_1633_, lean_object* v_prio_1634_, lean_object* v_caption_1635_, lean_object* v_a_1636_, lean_object* v_a_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Lake_Job_async___redArg(v_inst_1632_, v_act_1633_, v_prio_1634_, v_caption_1635_, v_a_1636_, v_a_1637_, v_a_1638_, v_a_1639_, v_a_1640_);
lean_dec_ref(v_a_1640_);
lean_dec_ref(v_a_1639_);
lean_dec(v_a_1638_);
lean_dec(v_a_1637_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async(lean_object* v_00_u03b1_1643_, lean_object* v_inst_1644_, lean_object* v_act_1645_, lean_object* v_prio_1646_, lean_object* v_caption_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lake_Job_async___redArg(v_inst_1644_, v_act_1645_, v_prio_1646_, v_caption_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___boxed(lean_object* v_00_u03b1_1656_, lean_object* v_inst_1657_, lean_object* v_act_1658_, lean_object* v_prio_1659_, lean_object* v_caption_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lake_Job_async(v_00_u03b1_1656_, v_inst_1657_, v_act_1658_, v_prio_1659_, v_caption_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
lean_dec_ref(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec_ref(v_a_1664_);
lean_dec(v_a_1663_);
lean_dec(v_a_1662_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg(lean_object* v_self_1669_){
_start:
{
lean_object* v_task_1671_; lean_object* v___x_1672_; 
v_task_1671_ = lean_ctor_get(v_self_1669_, 0);
lean_inc_ref(v_task_1671_);
lean_dec_ref(v_self_1669_);
v___x_1672_ = lean_io_wait(v_task_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg___boxed(lean_object* v_self_1673_, lean_object* v_a_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lake_Job_wait___redArg(v_self_1673_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait(lean_object* v_00_u03b1_1676_, lean_object* v_self_1677_){
_start:
{
lean_object* v_task_1679_; lean_object* v___x_1680_; 
v_task_1679_ = lean_ctor_get(v_self_1677_, 0);
lean_inc_ref(v_task_1679_);
lean_dec_ref(v_self_1677_);
v___x_1680_ = lean_io_wait(v_task_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___boxed(lean_object* v_00_u03b1_1681_, lean_object* v_self_1682_, lean_object* v_a_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lake_Job_wait(v_00_u03b1_1681_, v_self_1682_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg(lean_object* v_self_1685_){
_start:
{
lean_object* v_task_1687_; lean_object* v___x_1688_; 
v_task_1687_ = lean_ctor_get(v_self_1685_, 0);
lean_inc_ref(v_task_1687_);
lean_dec_ref(v_self_1685_);
v___x_1688_ = lean_io_wait(v_task_1687_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 2);
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v_a_1689_);
return v___x_1690_;
}
else
{
lean_object* v___x_1691_; 
lean_dec_ref_known(v___x_1688_, 2);
v___x_1691_ = lean_box(0);
return v___x_1691_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg___boxed(lean_object* v_self_1692_, lean_object* v_a_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lake_Job_wait_x3f___redArg(v_self_1692_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f(lean_object* v_00_u03b1_1695_, lean_object* v_self_1696_){
_start:
{
lean_object* v_task_1698_; lean_object* v___x_1699_; 
v_task_1698_ = lean_ctor_get(v_self_1696_, 0);
lean_inc_ref(v_task_1698_);
lean_dec_ref(v_self_1696_);
v___x_1699_ = lean_io_wait(v_task_1698_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___x_1701_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref_known(v___x_1699_, 2);
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v_a_1700_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; 
lean_dec_ref_known(v___x_1699_, 2);
v___x_1702_ = lean_box(0);
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_self_1704_, lean_object* v_a_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lake_Job_wait_x3f(v_00_u03b1_1703_, v_self_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(lean_object* v_as_1707_, size_t v_i_1708_, size_t v_stop_1709_, lean_object* v_b_1710_, lean_object* v___y_1711_){
_start:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_usize_dec_eq(v_i_1708_, v_stop_1709_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; size_t v___x_1717_; size_t v___x_1718_; 
v___x_1714_ = lean_array_uget_borrowed(v_as_1707_, v_i_1708_);
v___x_1715_ = lean_box(0);
lean_inc(v___x_1714_);
v___x_1716_ = lean_array_push(v___y_1711_, v___x_1714_);
v___x_1717_ = ((size_t)1ULL);
v___x_1718_ = lean_usize_add(v_i_1708_, v___x_1717_);
v_i_1708_ = v___x_1718_;
v_b_1710_ = v___x_1715_;
v___y_1711_ = v___x_1716_;
goto _start;
}
else
{
lean_object* v___x_1720_; 
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_b_1710_);
lean_ctor_set(v___x_1720_, 1, v___y_1711_);
return v___x_1720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0___boxed(lean_object* v_as_1721_, lean_object* v_i_1722_, lean_object* v_stop_1723_, lean_object* v_b_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
size_t v_i_boxed_1727_; size_t v_stop_boxed_1728_; lean_object* v_res_1729_; 
v_i_boxed_1727_ = lean_unbox_usize(v_i_1722_);
lean_dec(v_i_1722_);
v_stop_boxed_1728_ = lean_unbox_usize(v_stop_1723_);
lean_dec(v_stop_1723_);
v_res_1729_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_as_1721_, v_i_boxed_1727_, v_stop_boxed_1728_, v_b_1724_, v___y_1725_);
lean_dec_ref(v_as_1721_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg(lean_object* v_self_1730_, lean_object* v_a_1731_){
_start:
{
lean_object* v_task_1733_; lean_object* v___x_1734_; 
v_task_1733_ = lean_ctor_get(v_self_1730_, 0);
lean_inc_ref(v_task_1733_);
lean_dec_ref(v_self_1730_);
v___x_1734_ = lean_io_wait(v_task_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_a_1735_; lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1763_; 
v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
v_a_1736_ = lean_ctor_get(v___x_1734_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1738_ = v___x_1734_;
v_isShared_1739_ = v_isSharedCheck_1763_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_inc(v_a_1735_);
lean_dec(v___x_1734_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1763_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v_a_1741_; lean_object* v_log_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_log_1745_ = lean_ctor_get(v_a_1736_, 0);
lean_inc_ref(v_log_1745_);
lean_dec(v_a_1736_);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_array_get_size(v_log_1745_);
v___x_1748_ = lean_nat_dec_lt(v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v_log_1745_);
v_a_1741_ = v_a_1731_;
goto v___jp_1740_;
}
else
{
lean_object* v___x_1749_; size_t v___x_1750_; size_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1749_ = lean_box(0);
v___x_1750_ = ((size_t)0ULL);
v___x_1751_ = lean_usize_of_nat(v___x_1747_);
v___x_1752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1745_, v___x_1750_, v___x_1751_, v___x_1749_, v_a_1731_);
lean_dec_ref(v_log_1745_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 1);
lean_inc(v_a_1753_);
lean_dec_ref_known(v___x_1752_, 2);
v_a_1741_ = v_a_1753_;
goto v___jp_1740_;
}
else
{
lean_object* v_a_1754_; lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_del_object(v___x_1738_);
lean_dec(v_a_1735_);
v_a_1754_ = lean_ctor_get(v___x_1752_, 0);
v_a_1755_ = lean_ctor_get(v___x_1752_, 1);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1752_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_inc(v_a_1754_);
lean_dec(v___x_1752_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1754_);
lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
v___jp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 1, v_a_1741_);
v___x_1743_ = v___x_1738_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1735_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_a_1741_);
v___x_1743_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
return v___x_1743_;
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1794_; 
v_a_1764_ = lean_ctor_get(v___x_1734_, 1);
v_a_1765_ = lean_ctor_get(v___x_1734_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1767_ = v___x_1734_;
v_isShared_1768_ = v_isSharedCheck_1794_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1764_);
lean_inc(v_a_1765_);
lean_dec(v___x_1734_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1794_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_log_1769_; lean_object* v___x_1770_; lean_object* v_a_1772_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v_log_1769_ = lean_ctor_get(v_a_1764_, 0);
lean_inc_ref(v_log_1769_);
lean_dec(v_a_1764_);
v___x_1770_ = lean_array_get_size(v_a_1731_);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = lean_array_get_size(v_log_1769_);
v___x_1779_ = lean_nat_dec_lt(v___x_1777_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_dec_ref(v_log_1769_);
v_a_1772_ = v_a_1731_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1780_ = lean_box(0);
v___x_1781_ = ((size_t)0ULL);
v___x_1782_ = lean_usize_of_nat(v___x_1778_);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1769_, v___x_1781_, v___x_1782_, v___x_1780_, v_a_1731_);
lean_dec_ref(v_log_1769_);
if (lean_obj_tag(v___x_1783_) == 0)
{
lean_object* v_a_1784_; 
v_a_1784_ = lean_ctor_get(v___x_1783_, 1);
lean_inc(v_a_1784_);
lean_dec_ref_known(v___x_1783_, 2);
v_a_1772_ = v_a_1784_;
goto v___jp_1771_;
}
else
{
lean_object* v_a_1785_; lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_del_object(v___x_1767_);
lean_dec(v_a_1765_);
v_a_1785_ = lean_ctor_get(v___x_1783_, 0);
v_a_1786_ = lean_ctor_get(v___x_1783_, 1);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1783_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1783_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_inc(v_a_1785_);
lean_dec(v___x_1783_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1785_);
lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
v___jp_1771_:
{
lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1773_ = lean_nat_add(v___x_1770_, v_a_1765_);
lean_dec(v_a_1765_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v_a_1772_);
lean_ctor_set(v___x_1767_, 0, v___x_1773_);
v___x_1775_ = v___x_1767_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_a_1772_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___boxed(lean_object* v_self_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_){
_start:
{
lean_object* v_res_1798_; 
v_res_1798_ = l_Lake_Job_await___redArg(v_self_1795_, v_a_1796_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await(lean_object* v_00_u03b1_1799_, lean_object* v_self_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lake_Job_await___redArg(v_self_1800_, v_a_1801_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___boxed(lean_object* v_00_u03b1_1804_, lean_object* v_self_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lake_Job_await(v_00_u03b1_1804_, v_self_1805_, v_a_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___redArg(lean_object* v_a_1809_){
_start:
{
lean_object* v_log_1811_; uint8_t v_action_1812_; uint8_t v_wantsRebuild_1813_; lean_object* v_trace_1814_; lean_object* v_buildTime_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1825_; 
v_log_1811_ = lean_ctor_get(v_a_1809_, 0);
v_action_1812_ = lean_ctor_get_uint8(v_a_1809_, sizeof(void*)*3);
v_wantsRebuild_1813_ = lean_ctor_get_uint8(v_a_1809_, sizeof(void*)*3 + 1);
v_trace_1814_ = lean_ctor_get(v_a_1809_, 1);
v_buildTime_1815_ = lean_ctor_get(v_a_1809_, 2);
v_isSharedCheck_1825_ = !lean_is_exclusive(v_a_1809_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1817_ = v_a_1809_;
v_isShared_1818_ = v_isSharedCheck_1825_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_buildTime_1815_);
lean_inc(v_trace_1814_);
lean_inc(v_log_1811_);
lean_dec(v_a_1809_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1825_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
uint8_t v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = 1;
lean_inc_ref(v_log_1811_);
if (v_isShared_1818_ == 0)
{
v___x_1821_ = v___x_1817_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_log_1811_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_trace_1814_);
lean_ctor_set(v_reuseFailAlloc_1824_, 2, v_buildTime_1815_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*3, v_action_1812_);
lean_ctor_set_uint8(v_reuseFailAlloc_1824_, sizeof(void*)*3 + 1, v_wantsRebuild_1813_);
v___x_1821_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; 
lean_ctor_set_uint8(v___x_1821_, sizeof(void*)*3 + 2, v___x_1819_);
v___x_1822_ = lean_array_get_size(v_log_1811_);
lean_dec_ref(v_log_1811_);
v___x_1823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1821_);
return v___x_1823_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___redArg___boxed(lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l_Lake_Job_cancelJob___redArg(v_a_1826_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob(lean_object* v_00_u03b1_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = l_Lake_Job_cancelJob___redArg(v_a_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___boxed(lean_object* v_00_u03b1_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lake_Job_cancelJob(v_00_u03b1_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_, v_a_1843_, v_a_1844_);
lean_dec_ref(v_a_1843_);
lean_dec_ref(v_a_1842_);
lean_dec(v_a_1841_);
lean_dec(v_a_1840_);
lean_dec_ref(v_a_1839_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___redArg(lean_object* v_self_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_task_1850_; lean_object* v___x_1851_; 
v_task_1850_ = lean_ctor_get(v_self_1847_, 0);
lean_inc_ref(v_task_1850_);
lean_dec_ref(v_self_1847_);
v___x_1851_ = lean_io_wait(v_task_1850_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1860_; 
v_a_1852_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1860_ == 0)
{
lean_object* v_unused_1861_; 
v_unused_1861_ = lean_ctor_get(v___x_1851_, 1);
lean_dec(v_unused_1861_);
v___x_1854_ = v___x_1851_;
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1860_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_a_1852_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 1, v_a_1848_);
lean_ctor_set(v___x_1854_, 0, v___x_1856_);
v___x_1858_ = v___x_1854_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1856_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_a_1848_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
else
{
lean_object* v_a_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1872_; 
v_a_1862_ = lean_ctor_get(v___x_1851_, 1);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1872_ == 0)
{
lean_object* v_unused_1873_; 
v_unused_1873_ = lean_ctor_get(v___x_1851_, 0);
lean_dec(v_unused_1873_);
v___x_1864_ = v___x_1851_;
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_a_1862_);
lean_dec(v___x_1851_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
uint8_t v_canceled_1866_; 
v_canceled_1866_ = lean_ctor_get_uint8(v_a_1862_, sizeof(void*)*3 + 2);
lean_dec(v_a_1862_);
if (v_canceled_1866_ == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1869_; 
v___x_1867_ = lean_box(0);
if (v_isShared_1865_ == 0)
{
lean_ctor_set_tag(v___x_1864_, 0);
lean_ctor_set(v___x_1864_, 1, v_a_1848_);
lean_ctor_set(v___x_1864_, 0, v___x_1867_);
v___x_1869_ = v___x_1864_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_a_1848_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
else
{
lean_object* v___x_1871_; 
lean_del_object(v___x_1864_);
v___x_1871_ = l_Lake_Job_cancelJob___redArg(v_a_1848_);
return v___x_1871_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___redArg___boxed(lean_object* v_self_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lake_Job_waitUnlessCanceled_x3f___redArg(v_self_1874_, v_a_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f(lean_object* v_00_u03b1_1878_, lean_object* v_self_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lake_Job_waitUnlessCanceled_x3f___redArg(v_self_1879_, v_a_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___boxed(lean_object* v_00_u03b1_1888_, lean_object* v_self_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lake_Job_waitUnlessCanceled_x3f(v_00_u03b1_1888_, v_self_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_a_1895_);
lean_dec_ref(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1890_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg(lean_object* v_s_1902_){
_start:
{
lean_object* v_log_1903_; uint8_t v_action_1904_; uint8_t v_wantsRebuild_1905_; lean_object* v_trace_1906_; lean_object* v_buildTime_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1919_; 
v_log_1903_ = lean_ctor_get(v_s_1902_, 0);
v_action_1904_ = lean_ctor_get_uint8(v_s_1902_, sizeof(void*)*3);
v_wantsRebuild_1905_ = lean_ctor_get_uint8(v_s_1902_, sizeof(void*)*3 + 1);
v_trace_1906_ = lean_ctor_get(v_s_1902_, 1);
v_buildTime_1907_ = lean_ctor_get(v_s_1902_, 2);
v_isSharedCheck_1919_ = !lean_is_exclusive(v_s_1902_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1909_ = v_s_1902_;
v_isShared_1910_ = v_isSharedCheck_1919_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_buildTime_1907_);
lean_inc(v_trace_1906_);
lean_inc(v_log_1903_);
lean_dec(v_s_1902_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1919_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; uint8_t v___x_1914_; lean_object* v___x_1916_; 
v___x_1911_ = lean_array_get_size(v_log_1903_);
v___x_1912_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_1913_ = lean_array_push(v_log_1903_, v___x_1912_);
v___x_1914_ = 1;
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 0, v___x_1913_);
v___x_1916_ = v___x_1909_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1913_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_trace_1906_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_buildTime_1907_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*3, v_action_1904_);
lean_ctor_set_uint8(v_reuseFailAlloc_1918_, sizeof(void*)*3 + 1, v_wantsRebuild_1905_);
v___x_1916_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
lean_object* v___x_1917_; 
lean_ctor_set_uint8(v___x_1916_, sizeof(void*)*3 + 2, v___x_1914_);
v___x_1917_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1917_, 0, v___x_1911_);
lean_ctor_set(v___x_1917_, 1, v___x_1916_);
return v___x_1917_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult(lean_object* v_00_u03b1_1920_, lean_object* v_s_1921_){
_start:
{
lean_object* v_log_1922_; uint8_t v_action_1923_; uint8_t v_wantsRebuild_1924_; lean_object* v_trace_1925_; lean_object* v_buildTime_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1938_; 
v_log_1922_ = lean_ctor_get(v_s_1921_, 0);
v_action_1923_ = lean_ctor_get_uint8(v_s_1921_, sizeof(void*)*3);
v_wantsRebuild_1924_ = lean_ctor_get_uint8(v_s_1921_, sizeof(void*)*3 + 1);
v_trace_1925_ = lean_ctor_get(v_s_1921_, 1);
v_buildTime_1926_ = lean_ctor_get(v_s_1921_, 2);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_s_1921_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1928_ = v_s_1921_;
v_isShared_1929_ = v_isSharedCheck_1938_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_buildTime_1926_);
lean_inc(v_trace_1925_);
lean_inc(v_log_1922_);
lean_dec(v_s_1921_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1938_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1935_; 
v___x_1930_ = lean_array_get_size(v_log_1922_);
v___x_1931_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_1932_ = lean_array_push(v_log_1922_, v___x_1931_);
v___x_1933_ = 1;
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1932_);
v___x_1935_ = v___x_1928_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_trace_1925_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_buildTime_1926_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*3, v_action_1923_);
lean_ctor_set_uint8(v_reuseFailAlloc_1937_, sizeof(void*)*3 + 1, v_wantsRebuild_1924_);
v___x_1935_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; 
lean_ctor_set_uint8(v___x_1935_, sizeof(void*)*3 + 2, v___x_1933_);
v___x_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1936_, 0, v___x_1930_);
lean_ctor_set(v___x_1936_, 1, v___x_1935_);
return v___x_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1(lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_f_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_x_1946_){
_start:
{
lean_object* v_a_1949_; lean_object* v_a_1950_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; uint8_t v___y_1961_; uint8_t v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; uint8_t v___y_1965_; lean_object* v___y_1966_; 
if (lean_obj_tag(v_x_1946_) == 0)
{
lean_object* v_a_1978_; lean_object* v_a_1979_; lean_object* v___x_1981_; uint8_t v_isShared_1982_; uint8_t v_isSharedCheck_2048_; 
v_a_1978_ = lean_ctor_get(v_x_1946_, 0);
v_a_1979_ = lean_ctor_get(v_x_1946_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_x_1946_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_1981_ = v_x_1946_;
v_isShared_1982_ = v_isSharedCheck_2048_;
goto v_resetjp_1980_;
}
else
{
lean_inc(v_a_1979_);
lean_inc(v_a_1978_);
lean_dec(v_x_1946_);
v___x_1981_ = lean_box(0);
v_isShared_1982_ = v_isSharedCheck_2048_;
goto v_resetjp_1980_;
}
v_resetjp_1980_:
{
lean_object* v_cancelTk_x3f_2027_; 
v_cancelTk_x3f_2027_ = lean_ctor_get(v_a_1939_, 6);
if (lean_obj_tag(v_cancelTk_x3f_2027_) == 1)
{
lean_object* v_val_2028_; uint8_t v___x_2029_; 
v_val_2028_ = lean_ctor_get(v_cancelTk_x3f_2027_, 0);
v___x_2029_ = l_IO_CancelToken_isSet(v_val_2028_);
if (v___x_2029_ == 0)
{
lean_del_object(v___x_1981_);
goto v___jp_1983_;
}
else
{
lean_object* v_log_2030_; uint8_t v_action_2031_; uint8_t v_wantsRebuild_2032_; lean_object* v_trace_2033_; lean_object* v_buildTime_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2047_; 
lean_dec(v_a_1978_);
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_f_1941_);
v_log_2030_ = lean_ctor_get(v_a_1979_, 0);
v_action_2031_ = lean_ctor_get_uint8(v_a_1979_, sizeof(void*)*3);
v_wantsRebuild_2032_ = lean_ctor_get_uint8(v_a_1979_, sizeof(void*)*3 + 1);
v_trace_2033_ = lean_ctor_get(v_a_1979_, 1);
v_buildTime_2034_ = lean_ctor_get(v_a_1979_, 2);
v_isSharedCheck_2047_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_2047_ == 0)
{
v___x_2036_ = v_a_1979_;
v_isShared_2037_ = v_isSharedCheck_2047_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_buildTime_2034_);
lean_inc(v_trace_2033_);
lean_inc(v_log_2030_);
lean_dec(v_a_1979_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2047_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2038_ = lean_array_get_size(v_log_2030_);
v___x_2039_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_2040_ = lean_array_push(v_log_2030_, v___x_2039_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2040_);
v___x_2042_ = v___x_2036_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2046_, 1, v_trace_2033_);
lean_ctor_set(v_reuseFailAlloc_2046_, 2, v_buildTime_2034_);
lean_ctor_set_uint8(v_reuseFailAlloc_2046_, sizeof(void*)*3, v_action_2031_);
lean_ctor_set_uint8(v_reuseFailAlloc_2046_, sizeof(void*)*3 + 1, v_wantsRebuild_2032_);
v___x_2042_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2044_; 
lean_ctor_set_uint8(v___x_2042_, sizeof(void*)*3 + 2, v___x_2029_);
if (v_isShared_1982_ == 0)
{
lean_ctor_set_tag(v___x_1981_, 1);
lean_ctor_set(v___x_1981_, 1, v___x_2042_);
lean_ctor_set(v___x_1981_, 0, v___x_2038_);
v___x_2044_ = v___x_1981_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
}
else
{
lean_del_object(v___x_1981_);
goto v___jp_1983_;
}
v___jp_1983_:
{
lean_object* v_log_1984_; uint8_t v_action_1985_; uint8_t v_wantsRebuild_1986_; uint8_t v_canceled_1987_; lean_object* v_trace_1988_; lean_object* v_buildTime_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2026_; 
v_log_1984_ = lean_ctor_get(v_a_1979_, 0);
v_action_1985_ = lean_ctor_get_uint8(v_a_1979_, sizeof(void*)*3);
v_wantsRebuild_1986_ = lean_ctor_get_uint8(v_a_1979_, sizeof(void*)*3 + 1);
v_canceled_1987_ = lean_ctor_get_uint8(v_a_1979_, sizeof(void*)*3 + 2);
v_trace_1988_ = lean_ctor_get(v_a_1979_, 1);
v_buildTime_1989_ = lean_ctor_get(v_a_1979_, 2);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_1991_ = v_a_1979_;
v_isShared_1992_ = v_isSharedCheck_2026_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_buildTime_1989_);
lean_inc(v_trace_1988_);
lean_inc(v_log_1984_);
lean_dec(v_a_1979_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2026_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v_trace_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_inc_ref(v_a_1940_);
v_trace_1993_ = l_Lake_BuildTrace_mix(v_a_1940_, v_trace_1988_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1996_ = lean_st_mk_ref(v___x_1995_);
lean_inc(v___x_1996_);
v___x_1997_ = l_IO_FS_Stream_ofBuffer(v___x_1996_);
lean_inc_ref(v___x_1997_);
v___x_1998_ = lean_get_set_stdout(v___x_1997_);
v___x_1999_ = lean_get_set_stderr(v___x_1997_);
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 1, v_trace_1993_);
v___x_2001_ = v___x_1991_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_log_1984_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_trace_1993_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_buildTime_1989_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*3, v_action_1985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*3 + 1, v_wantsRebuild_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_2025_, sizeof(void*)*3 + 2, v_canceled_1987_);
v___x_2001_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
lean_object* v___x_2002_; 
lean_inc_ref(v_a_1939_);
lean_inc_ref(v_a_1945_);
lean_inc(v_a_1944_);
lean_inc(v_a_1943_);
v___x_2002_ = lean_apply_8(v_f_1941_, v_a_1978_, v_a_1942_, v_a_1943_, v_a_1944_, v_a_1945_, v_a_1939_, v___x_2001_, lean_box(0));
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v_a_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v_a_2007_; lean_object* v_log_2008_; uint8_t v_action_2009_; uint8_t v_wantsRebuild_2010_; uint8_t v_canceled_2011_; lean_object* v_trace_2012_; lean_object* v_buildTime_2013_; lean_object* v___x_2014_; lean_object* v_data_2015_; uint8_t v___x_2016_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc_n(v_a_2003_, 2);
v_a_2004_ = lean_ctor_get(v___x_2002_, 1);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2002_, 2);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_a_2003_);
v___x_2006_ = l_Lake_Job_sync___redArg___lam__0(v___x_1998_, v___x_1999_, v___x_2005_, v_a_2004_);
lean_dec_ref_known(v___x_2005_, 1);
v_a_2007_ = lean_ctor_get(v___x_2006_, 1);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2006_);
v_log_2008_ = lean_ctor_get(v_a_2007_, 0);
lean_inc_ref(v_log_2008_);
v_action_2009_ = lean_ctor_get_uint8(v_a_2007_, sizeof(void*)*3);
v_wantsRebuild_2010_ = lean_ctor_get_uint8(v_a_2007_, sizeof(void*)*3 + 1);
v_canceled_2011_ = lean_ctor_get_uint8(v_a_2007_, sizeof(void*)*3 + 2);
v_trace_2012_ = lean_ctor_get(v_a_2007_, 1);
lean_inc_ref(v_trace_2012_);
v_buildTime_2013_ = lean_ctor_get(v_a_2007_, 2);
lean_inc(v_buildTime_2013_);
v___x_2014_ = lean_st_ref_get(v___x_1996_);
lean_dec(v___x_1996_);
v_data_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc_ref(v_data_2015_);
lean_dec(v___x_2014_);
v___x_2016_ = lean_string_validate_utf8(v_data_2015_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec_ref(v_data_2015_);
v___x_2017_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2018_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2017_);
v___y_1957_ = v_a_2003_;
v___y_1958_ = v___x_1994_;
v___y_1959_ = v_a_2007_;
v___y_1960_ = v_trace_2012_;
v___y_1961_ = v_canceled_2011_;
v___y_1962_ = v_wantsRebuild_2010_;
v___y_1963_ = v_buildTime_2013_;
v___y_1964_ = v_log_2008_;
v___y_1965_ = v_action_2009_;
v___y_1966_ = v___x_2018_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_string_from_utf8_unchecked(v_data_2015_);
v___y_1957_ = v_a_2003_;
v___y_1958_ = v___x_1994_;
v___y_1959_ = v_a_2007_;
v___y_1960_ = v_trace_2012_;
v___y_1961_ = v_canceled_2011_;
v___y_1962_ = v_wantsRebuild_2010_;
v___y_1963_ = v_buildTime_2013_;
v___y_1964_ = v_log_2008_;
v___y_1965_ = v_action_2009_;
v___y_1966_ = v___x_2019_;
goto v___jp_1956_;
}
}
else
{
lean_object* v_a_2020_; lean_object* v_a_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v_a_2024_; 
lean_dec(v___x_1996_);
v_a_2020_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2020_);
v_a_2021_ = lean_ctor_get(v___x_2002_, 1);
lean_inc(v_a_2021_);
lean_dec_ref_known(v___x_2002_, 2);
v___x_2022_ = lean_box(0);
v___x_2023_ = l_Lake_Job_sync___redArg___lam__0(v___x_1998_, v___x_1999_, v___x_2022_, v_a_2021_);
v_a_2024_ = lean_ctor_get(v___x_2023_, 1);
lean_inc(v_a_2024_);
lean_dec_ref(v___x_2023_);
v_a_1949_ = v_a_2020_;
v_a_1950_ = v_a_2024_;
goto v___jp_1948_;
}
}
}
}
}
}
else
{
lean_object* v_a_2049_; lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref(v_a_1942_);
lean_dec_ref(v_f_1941_);
v_a_2049_ = lean_ctor_get(v_x_1946_, 0);
v_a_2050_ = lean_ctor_get(v_x_1946_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_x_1946_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v_x_1946_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_inc(v_a_2049_);
lean_dec(v_x_1946_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2049_);
lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
v___jp_1948_:
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_a_1949_);
lean_ctor_set(v___x_1951_, 1, v_a_1950_);
return v___x_1951_;
}
v___jp_1952_:
{
lean_object* v___x_1955_; 
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___y_1953_);
lean_ctor_set(v___x_1955_, 1, v___y_1954_);
return v___x_1955_;
}
v___jp_1956_:
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = lean_string_utf8_byte_size(v___y_1966_);
v___x_1968_ = lean_nat_dec_eq(v___x_1967_, v___y_1958_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec_ref(v___y_1959_);
v___x_1969_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1970_, 0, v___y_1966_);
lean_ctor_set(v___x_1970_, 1, v___y_1958_);
lean_ctor_set(v___x_1970_, 2, v___x_1967_);
v___x_1971_ = l_String_Slice_trimAscii(v___x_1970_);
v___x_1972_ = l_String_Slice_toString(v___x_1971_);
lean_dec_ref(v___x_1971_);
v___x_1973_ = lean_string_append(v___x_1969_, v___x_1972_);
lean_dec_ref(v___x_1972_);
v___x_1974_ = 1;
v___x_1975_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*1, v___x_1974_);
v___x_1976_ = lean_array_push(v___y_1964_, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v___y_1960_);
lean_ctor_set(v___x_1977_, 2, v___y_1963_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*3, v___y_1965_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*3 + 1, v___y_1962_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*3 + 2, v___y_1961_);
v___y_1953_ = v___y_1957_;
v___y_1954_ = v___x_1977_;
goto v___jp_1952_;
}
else
{
lean_dec_ref(v___y_1966_);
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1963_);
lean_dec_ref(v___y_1960_);
lean_dec(v___y_1958_);
v___y_1953_ = v___y_1957_;
v___y_1954_ = v___y_1959_;
goto v___jp_1952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1___boxed(lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_f_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_x_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lake_Job_mapM___redArg___lam__1(v_a_2058_, v_a_2059_, v_f_2060_, v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_x_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object* v_kind_2068_, lean_object* v_self_2069_, lean_object* v_f_2070_, lean_object* v_prio_2071_, uint8_t v_sync_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_task_2080_; lean_object* v_caption_2081_; uint8_t v_optional_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2091_; 
v_task_2080_ = lean_ctor_get(v_self_2069_, 0);
v_caption_2081_ = lean_ctor_get(v_self_2069_, 2);
v_optional_2082_ = lean_ctor_get_uint8(v_self_2069_, sizeof(void*)*3);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_self_2069_);
if (v_isSharedCheck_2091_ == 0)
{
lean_object* v_unused_2092_; 
v_unused_2092_ = lean_ctor_get(v_self_2069_, 1);
lean_dec(v_unused_2092_);
v___x_2084_ = v_self_2069_;
v_isShared_2085_ = v_isSharedCheck_2091_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_caption_2081_);
lean_inc(v_task_2080_);
lean_dec(v_self_2069_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2091_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
lean_inc_ref(v_a_2076_);
lean_inc(v_a_2075_);
lean_inc(v_a_2074_);
lean_inc_ref(v_a_2078_);
lean_inc_ref(v_a_2077_);
v___f_2086_ = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__1___boxed), 9, 7);
lean_closure_set(v___f_2086_, 0, v_a_2077_);
lean_closure_set(v___f_2086_, 1, v_a_2078_);
lean_closure_set(v___f_2086_, 2, v_f_2070_);
lean_closure_set(v___f_2086_, 3, v_a_2073_);
lean_closure_set(v___f_2086_, 4, v_a_2074_);
lean_closure_set(v___f_2086_, 5, v_a_2075_);
lean_closure_set(v___f_2086_, 6, v_a_2076_);
v___x_2087_ = lean_io_map_task(v___f_2086_, v_task_2080_, v_prio_2071_, v_sync_2072_);
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 1, v_kind_2068_);
lean_ctor_set(v___x_2084_, 0, v___x_2087_);
v___x_2089_ = v___x_2084_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_kind_2068_);
lean_ctor_set(v_reuseFailAlloc_2090_, 2, v_caption_2081_);
lean_ctor_set_uint8(v_reuseFailAlloc_2090_, sizeof(void*)*3, v_optional_2082_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object* v_kind_2093_, lean_object* v_self_2094_, lean_object* v_f_2095_, lean_object* v_prio_2096_, lean_object* v_sync_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
uint8_t v_sync_boxed_2105_; lean_object* v_res_2106_; 
v_sync_boxed_2105_ = lean_unbox(v_sync_2097_);
v_res_2106_ = l_Lake_Job_mapM___redArg(v_kind_2093_, v_self_2094_, v_f_2095_, v_prio_2096_, v_sync_boxed_2105_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_);
lean_dec_ref(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec_ref(v_a_2101_);
lean_dec(v_a_2100_);
lean_dec(v_a_2099_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object* v_00_u03b2_2107_, lean_object* v_00_u03b1_2108_, lean_object* v_kind_2109_, lean_object* v_self_2110_, lean_object* v_f_2111_, lean_object* v_prio_2112_, uint8_t v_sync_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lake_Job_mapM___redArg(v_kind_2109_, v_self_2110_, v_f_2111_, v_prio_2112_, v_sync_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object* v_00_u03b2_2122_, lean_object* v_00_u03b1_2123_, lean_object* v_kind_2124_, lean_object* v_self_2125_, lean_object* v_f_2126_, lean_object* v_prio_2127_, lean_object* v_sync_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
uint8_t v_sync_boxed_2136_; lean_object* v_res_2137_; 
v_sync_boxed_2136_ = lean_unbox(v_sync_2128_);
v_res_2137_ = l_Lake_Job_mapM(v_00_u03b2_2122_, v_00_u03b1_2123_, v_kind_2124_, v_self_2125_, v_f_2126_, v_prio_2127_, v_sync_boxed_2136_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec_ref(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec_ref(v_a_2132_);
lean_dec(v_a_2131_);
lean_dec(v_a_2130_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object* v_a_2138_, lean_object* v_x_2139_){
_start:
{
if (lean_obj_tag(v_x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v_a_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2164_; 
v_a_2140_ = lean_ctor_get(v_x_2139_, 0);
v_a_2141_ = lean_ctor_get(v_x_2139_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_x_2139_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2143_ = v_x_2139_;
v_isShared_2144_ = v_isSharedCheck_2164_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_a_2141_);
lean_inc(v_a_2140_);
lean_dec(v_x_2139_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2164_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v_log_2146_; uint8_t v_action_2147_; uint8_t v_wantsRebuild_2148_; uint8_t v_canceled_2149_; lean_object* v_buildTime_2150_; lean_object* v_trace_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2161_; 
lean_inc(v_a_2141_);
v___x_2145_ = l_Lake_JobState_merge(v_a_2138_, v_a_2141_);
v_log_2146_ = lean_ctor_get(v___x_2145_, 0);
lean_inc_ref(v_log_2146_);
v_action_2147_ = lean_ctor_get_uint8(v___x_2145_, sizeof(void*)*3);
v_wantsRebuild_2148_ = lean_ctor_get_uint8(v___x_2145_, sizeof(void*)*3 + 1);
v_canceled_2149_ = lean_ctor_get_uint8(v___x_2145_, sizeof(void*)*3 + 2);
v_buildTime_2150_ = lean_ctor_get(v___x_2145_, 2);
lean_inc(v_buildTime_2150_);
lean_dec_ref(v___x_2145_);
v_trace_2151_ = lean_ctor_get(v_a_2141_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_a_2141_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; lean_object* v_unused_2163_; 
v_unused_2162_ = lean_ctor_get(v_a_2141_, 2);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_a_2141_, 0);
lean_dec(v_unused_2163_);
v___x_2153_ = v_a_2141_;
v_isShared_2154_ = v_isSharedCheck_2161_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_trace_2151_);
lean_dec(v_a_2141_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2161_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
lean_ctor_set(v___x_2153_, 2, v_buildTime_2150_);
lean_ctor_set(v___x_2153_, 0, v_log_2146_);
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_log_2146_);
lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_trace_2151_);
lean_ctor_set(v_reuseFailAlloc_2160_, 2, v_buildTime_2150_);
v___x_2156_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2158_; 
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*3, v_action_2147_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*3 + 1, v_wantsRebuild_2148_);
lean_ctor_set_uint8(v___x_2156_, sizeof(void*)*3 + 2, v_canceled_2149_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set(v___x_2143_, 1, v___x_2156_);
v___x_2158_ = v___x_2143_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2140_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v___x_2156_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2192_; 
v_a_2165_ = lean_ctor_get(v_x_2139_, 0);
v_a_2166_ = lean_ctor_get(v_x_2139_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_x_2139_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2168_ = v_x_2139_;
v_isShared_2169_ = v_isSharedCheck_2192_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_inc(v_a_2165_);
lean_dec(v_x_2139_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2192_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v_log_2170_; lean_object* v___x_2171_; lean_object* v_log_2172_; uint8_t v_action_2173_; uint8_t v_wantsRebuild_2174_; uint8_t v_canceled_2175_; lean_object* v_buildTime_2176_; lean_object* v_trace_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2189_; 
v_log_2170_ = lean_ctor_get(v_a_2138_, 0);
lean_inc_ref(v_log_2170_);
lean_inc(v_a_2166_);
v___x_2171_ = l_Lake_JobState_merge(v_a_2138_, v_a_2166_);
v_log_2172_ = lean_ctor_get(v___x_2171_, 0);
lean_inc_ref(v_log_2172_);
v_action_2173_ = lean_ctor_get_uint8(v___x_2171_, sizeof(void*)*3);
v_wantsRebuild_2174_ = lean_ctor_get_uint8(v___x_2171_, sizeof(void*)*3 + 1);
v_canceled_2175_ = lean_ctor_get_uint8(v___x_2171_, sizeof(void*)*3 + 2);
v_buildTime_2176_ = lean_ctor_get(v___x_2171_, 2);
lean_inc(v_buildTime_2176_);
lean_dec_ref(v___x_2171_);
v_trace_2177_ = lean_ctor_get(v_a_2166_, 1);
v_isSharedCheck_2189_ = !lean_is_exclusive(v_a_2166_);
if (v_isSharedCheck_2189_ == 0)
{
lean_object* v_unused_2190_; lean_object* v_unused_2191_; 
v_unused_2190_ = lean_ctor_get(v_a_2166_, 2);
lean_dec(v_unused_2190_);
v_unused_2191_ = lean_ctor_get(v_a_2166_, 0);
lean_dec(v_unused_2191_);
v___x_2179_ = v_a_2166_;
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_trace_2177_);
lean_dec(v_a_2166_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2181_ = lean_array_get_size(v_log_2170_);
lean_dec_ref(v_log_2170_);
v___x_2182_ = lean_nat_add(v___x_2181_, v_a_2165_);
lean_dec(v_a_2165_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 2, v_buildTime_2176_);
lean_ctor_set(v___x_2179_, 0, v_log_2172_);
v___x_2184_ = v___x_2179_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_log_2172_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_trace_2177_);
lean_ctor_set(v_reuseFailAlloc_2188_, 2, v_buildTime_2176_);
v___x_2184_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*3, v_action_2173_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*3 + 1, v_wantsRebuild_2174_);
lean_ctor_set_uint8(v___x_2184_, sizeof(void*)*3 + 2, v_canceled_2175_);
if (v_isShared_2169_ == 0)
{
lean_ctor_set(v___x_2168_, 1, v___x_2184_);
lean_ctor_set(v___x_2168_, 0, v___x_2182_);
v___x_2186_ = v___x_2168_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v___x_2184_);
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
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object* v_val_2193_, lean_object* v_val_2194_, lean_object* v_a_x3f_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2198_ = lean_get_set_stdout(v_val_2193_);
lean_dec_ref(v___x_2198_);
v___x_2199_ = lean_box(0);
v___x_2200_ = lean_get_set_stderr(v_val_2194_);
lean_dec_ref(v___x_2200_);
v___x_2201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set(v___x_2201_, 1, v___y_2196_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1___boxed(lean_object* v_val_2202_, lean_object* v_val_2203_, lean_object* v_a_x3f_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lake_Job_bindM___redArg___lam__1(v_val_2202_, v_val_2203_, v_a_x3f_2204_, v___y_2205_);
lean_dec(v_a_x3f_2204_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object* v_a_2208_, lean_object* v_____r_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2217_, 0, v_a_2208_);
lean_ctor_set(v___x_2217_, 1, v___y_2215_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2___boxed(lean_object* v_a_2218_, lean_object* v_____r_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2218_, v_____r_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3(lean_object* v_a_2228_, lean_object* v_prio_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_f_2235_, lean_object* v_x_2236_){
_start:
{
lean_object* v_a_2239_; lean_object* v_a_2240_; lean_object* v___y_2244_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; uint8_t v___y_2257_; uint8_t v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; uint8_t v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; 
if (lean_obj_tag(v_x_2236_) == 0)
{
lean_object* v_a_2279_; lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2351_; 
v_a_2279_ = lean_ctor_get(v_x_2236_, 0);
v_a_2280_ = lean_ctor_get(v_x_2236_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v_x_2236_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2282_ = v_x_2236_;
v_isShared_2283_ = v_isSharedCheck_2351_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_inc(v_a_2279_);
lean_dec(v_x_2236_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2351_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v_cancelTk_x3f_2329_; 
v_cancelTk_x3f_2329_ = lean_ctor_get(v_a_2228_, 6);
if (lean_obj_tag(v_cancelTk_x3f_2329_) == 1)
{
lean_object* v_val_2330_; uint8_t v___x_2331_; 
v_val_2330_ = lean_ctor_get(v_cancelTk_x3f_2329_, 0);
v___x_2331_ = l_IO_CancelToken_isSet(v_val_2330_);
if (v___x_2331_ == 0)
{
lean_del_object(v___x_2282_);
goto v___jp_2284_;
}
else
{
lean_object* v_log_2332_; uint8_t v_action_2333_; uint8_t v_wantsRebuild_2334_; lean_object* v_trace_2335_; lean_object* v_buildTime_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_a_2279_);
lean_dec_ref(v_f_2235_);
lean_dec_ref(v_a_2230_);
lean_dec(v_prio_2229_);
v_log_2332_ = lean_ctor_get(v_a_2280_, 0);
v_action_2333_ = lean_ctor_get_uint8(v_a_2280_, sizeof(void*)*3);
v_wantsRebuild_2334_ = lean_ctor_get_uint8(v_a_2280_, sizeof(void*)*3 + 1);
v_trace_2335_ = lean_ctor_get(v_a_2280_, 1);
v_buildTime_2336_ = lean_ctor_get(v_a_2280_, 2);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_a_2280_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2338_ = v_a_2280_;
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_buildTime_2336_);
lean_inc(v_trace_2335_);
lean_inc(v_log_2332_);
lean_dec(v_a_2280_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2350_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2344_; 
v___x_2340_ = lean_array_get_size(v_log_2332_);
v___x_2341_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_2342_ = lean_array_push(v_log_2332_, v___x_2341_);
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 0, v___x_2342_);
v___x_2344_ = v___x_2338_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2342_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_trace_2335_);
lean_ctor_set(v_reuseFailAlloc_2349_, 2, v_buildTime_2336_);
lean_ctor_set_uint8(v_reuseFailAlloc_2349_, sizeof(void*)*3, v_action_2333_);
lean_ctor_set_uint8(v_reuseFailAlloc_2349_, sizeof(void*)*3 + 1, v_wantsRebuild_2334_);
v___x_2344_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2346_; 
lean_ctor_set_uint8(v___x_2344_, sizeof(void*)*3 + 2, v___x_2331_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set_tag(v___x_2282_, 1);
lean_ctor_set(v___x_2282_, 1, v___x_2344_);
lean_ctor_set(v___x_2282_, 0, v___x_2340_);
v___x_2346_ = v___x_2282_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v___x_2344_);
v___x_2346_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; 
v___x_2347_ = lean_task_pure(v___x_2346_);
return v___x_2347_;
}
}
}
}
}
else
{
lean_del_object(v___x_2282_);
goto v___jp_2284_;
}
v___jp_2284_:
{
lean_object* v_log_2285_; uint8_t v_action_2286_; uint8_t v_wantsRebuild_2287_; uint8_t v_canceled_2288_; lean_object* v_trace_2289_; lean_object* v_buildTime_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2328_; 
v_log_2285_ = lean_ctor_get(v_a_2280_, 0);
v_action_2286_ = lean_ctor_get_uint8(v_a_2280_, sizeof(void*)*3);
v_wantsRebuild_2287_ = lean_ctor_get_uint8(v_a_2280_, sizeof(void*)*3 + 1);
v_canceled_2288_ = lean_ctor_get_uint8(v_a_2280_, sizeof(void*)*3 + 2);
v_trace_2289_ = lean_ctor_get(v_a_2280_, 1);
v_buildTime_2290_ = lean_ctor_get(v_a_2280_, 2);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_a_2280_);
if (v_isSharedCheck_2328_ == 0)
{
v___x_2292_ = v_a_2280_;
v_isShared_2293_ = v_isSharedCheck_2328_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_buildTime_2290_);
lean_inc(v_trace_2289_);
lean_inc(v_log_2285_);
lean_dec(v_a_2280_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2328_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_trace_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2302_; 
lean_inc_ref(v_a_2234_);
v_trace_2294_ = l_Lake_BuildTrace_mix(v_a_2234_, v_trace_2289_);
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_2297_ = lean_st_mk_ref(v___x_2296_);
lean_inc(v___x_2297_);
v___x_2298_ = l_IO_FS_Stream_ofBuffer(v___x_2297_);
lean_inc_ref(v___x_2298_);
v___x_2299_ = lean_get_set_stdout(v___x_2298_);
v___x_2300_ = lean_get_set_stderr(v___x_2298_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 1, v_trace_2294_);
v___x_2302_ = v___x_2292_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2327_; 
v_reuseFailAlloc_2327_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_log_2285_);
lean_ctor_set(v_reuseFailAlloc_2327_, 1, v_trace_2294_);
lean_ctor_set(v_reuseFailAlloc_2327_, 2, v_buildTime_2290_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*3, v_action_2286_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*3 + 1, v_wantsRebuild_2287_);
lean_ctor_set_uint8(v_reuseFailAlloc_2327_, sizeof(void*)*3 + 2, v_canceled_2288_);
v___x_2302_ = v_reuseFailAlloc_2327_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; 
lean_inc_ref(v_a_2228_);
lean_inc_ref(v_a_2233_);
lean_inc(v_a_2232_);
lean_inc(v_a_2231_);
lean_inc_ref(v_a_2230_);
v___x_2303_ = lean_apply_8(v_f_2235_, v_a_2279_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2228_, v___x_2302_, lean_box(0));
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; lean_object* v_a_2305_; lean_object* v___f_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v_a_2309_; lean_object* v_log_2310_; uint8_t v_action_2311_; uint8_t v_wantsRebuild_2312_; uint8_t v_canceled_2313_; lean_object* v_trace_2314_; lean_object* v_buildTime_2315_; lean_object* v___x_2316_; lean_object* v_data_2317_; uint8_t v___x_2318_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc_n(v_a_2304_, 2);
v_a_2305_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_a_2305_);
lean_dec_ref_known(v___x_2303_, 2);
v___f_2306_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_2306_, 0, v_a_2304_);
v___x_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2307_, 0, v_a_2304_);
v___x_2308_ = l_Lake_Job_bindM___redArg___lam__1(v___x_2299_, v___x_2300_, v___x_2307_, v_a_2305_);
lean_dec_ref_known(v___x_2307_, 1);
v_a_2309_ = lean_ctor_get(v___x_2308_, 1);
lean_inc(v_a_2309_);
lean_dec_ref(v___x_2308_);
v_log_2310_ = lean_ctor_get(v_a_2309_, 0);
lean_inc_ref(v_log_2310_);
v_action_2311_ = lean_ctor_get_uint8(v_a_2309_, sizeof(void*)*3);
v_wantsRebuild_2312_ = lean_ctor_get_uint8(v_a_2309_, sizeof(void*)*3 + 1);
v_canceled_2313_ = lean_ctor_get_uint8(v_a_2309_, sizeof(void*)*3 + 2);
v_trace_2314_ = lean_ctor_get(v_a_2309_, 1);
lean_inc_ref(v_trace_2314_);
v_buildTime_2315_ = lean_ctor_get(v_a_2309_, 2);
lean_inc(v_buildTime_2315_);
v___x_2316_ = lean_st_ref_get(v___x_2297_);
lean_dec(v___x_2297_);
v_data_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc_ref(v_data_2317_);
lean_dec(v___x_2316_);
v___x_2318_ = lean_string_validate_utf8(v_data_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_dec_ref(v_data_2317_);
v___x_2319_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2320_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2319_);
v___y_2254_ = v_trace_2314_;
v___y_2255_ = v_log_2310_;
v___y_2256_ = v_a_2309_;
v___y_2257_ = v_canceled_2313_;
v___y_2258_ = v_action_2311_;
v___y_2259_ = v___x_2295_;
v___y_2260_ = v_buildTime_2315_;
v___y_2261_ = v_wantsRebuild_2312_;
v___y_2262_ = v___f_2306_;
v___y_2263_ = v___x_2320_;
goto v___jp_2253_;
}
else
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_string_from_utf8_unchecked(v_data_2317_);
v___y_2254_ = v_trace_2314_;
v___y_2255_ = v_log_2310_;
v___y_2256_ = v_a_2309_;
v___y_2257_ = v_canceled_2313_;
v___y_2258_ = v_action_2311_;
v___y_2259_ = v___x_2295_;
v___y_2260_ = v_buildTime_2315_;
v___y_2261_ = v_wantsRebuild_2312_;
v___y_2262_ = v___f_2306_;
v___y_2263_ = v___x_2321_;
goto v___jp_2253_;
}
}
else
{
lean_object* v_a_2322_; lean_object* v_a_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v_a_2326_; 
lean_dec(v___x_2297_);
lean_dec_ref(v_a_2230_);
lean_dec(v_prio_2229_);
v_a_2322_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2322_);
v_a_2323_ = lean_ctor_get(v___x_2303_, 1);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2303_, 2);
v___x_2324_ = lean_box(0);
v___x_2325_ = l_Lake_Job_bindM___redArg___lam__1(v___x_2299_, v___x_2300_, v___x_2324_, v_a_2323_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 1);
lean_inc(v_a_2326_);
lean_dec_ref(v___x_2325_);
v_a_2239_ = v_a_2322_;
v_a_2240_ = v_a_2326_;
goto v___jp_2238_;
}
}
}
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2361_; 
lean_dec_ref(v_f_2235_);
lean_dec_ref(v_a_2230_);
lean_dec(v_prio_2229_);
v_a_2352_ = lean_ctor_get(v_x_2236_, 0);
v_a_2353_ = lean_ctor_get(v_x_2236_, 1);
v_isSharedCheck_2361_ = !lean_is_exclusive(v_x_2236_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2355_ = v_x_2236_;
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_inc(v_a_2352_);
lean_dec(v_x_2236_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2361_;
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
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2352_);
lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_task_pure(v___x_2358_);
return v___x_2359_;
}
}
}
v___jp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2241_, 0, v_a_2239_);
lean_ctor_set(v___x_2241_, 1, v_a_2240_);
v___x_2242_ = lean_task_pure(v___x_2241_);
return v___x_2242_;
}
v___jp_2243_:
{
if (lean_obj_tag(v___y_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v_a_2246_; lean_object* v_task_2247_; lean_object* v___f_2248_; uint8_t v___x_2249_; lean_object* v___x_2250_; 
v_a_2245_ = lean_ctor_get(v___y_2244_, 0);
lean_inc(v_a_2245_);
v_a_2246_ = lean_ctor_get(v___y_2244_, 1);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___y_2244_, 2);
v_task_2247_ = lean_ctor_get(v_a_2245_, 0);
lean_inc_ref(v_task_2247_);
lean_dec(v_a_2245_);
v___f_2248_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2248_, 0, v_a_2246_);
v___x_2249_ = 1;
v___x_2250_ = lean_task_map(v___f_2248_, v_task_2247_, v_prio_2229_, v___x_2249_);
return v___x_2250_;
}
else
{
lean_object* v_a_2251_; lean_object* v_a_2252_; 
lean_dec(v_prio_2229_);
v_a_2251_ = lean_ctor_get(v___y_2244_, 0);
lean_inc(v_a_2251_);
v_a_2252_ = lean_ctor_get(v___y_2244_, 1);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___y_2244_, 2);
v_a_2239_ = v_a_2251_;
v_a_2240_ = v_a_2252_;
goto v___jp_2238_;
}
}
v___jp_2253_:
{
lean_object* v___x_2264_; uint8_t v___x_2265_; 
v___x_2264_ = lean_string_utf8_byte_size(v___y_2263_);
v___x_2265_ = lean_nat_dec_eq(v___x_2264_, v___y_2259_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_dec_ref(v___y_2256_);
v___x_2266_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_2267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2267_, 0, v___y_2263_);
lean_ctor_set(v___x_2267_, 1, v___y_2259_);
lean_ctor_set(v___x_2267_, 2, v___x_2264_);
v___x_2268_ = l_String_Slice_trimAscii(v___x_2267_);
v___x_2269_ = l_String_Slice_toString(v___x_2268_);
lean_dec_ref(v___x_2268_);
v___x_2270_ = lean_string_append(v___x_2266_, v___x_2269_);
lean_dec_ref(v___x_2269_);
v___x_2271_ = 1;
v___x_2272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2272_, 0, v___x_2270_);
lean_ctor_set_uint8(v___x_2272_, sizeof(void*)*1, v___x_2271_);
v___x_2273_ = lean_box(0);
v___x_2274_ = lean_array_push(v___y_2255_, v___x_2272_);
v___x_2275_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___y_2254_);
lean_ctor_set(v___x_2275_, 2, v___y_2260_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*3, v___y_2258_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*3 + 1, v___y_2261_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*3 + 2, v___y_2257_);
lean_inc_ref(v_a_2228_);
lean_inc_ref(v_a_2233_);
lean_inc(v_a_2232_);
lean_inc(v_a_2231_);
v___x_2276_ = lean_apply_8(v___y_2262_, v___x_2273_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2228_, v___x_2275_, lean_box(0));
v___y_2244_ = v___x_2276_;
goto v___jp_2243_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v___y_2254_);
v___x_2277_ = lean_box(0);
lean_inc_ref(v_a_2228_);
lean_inc_ref(v_a_2233_);
lean_inc(v_a_2232_);
lean_inc(v_a_2231_);
v___x_2278_ = lean_apply_8(v___y_2262_, v___x_2277_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2228_, v___y_2256_, lean_box(0));
v___y_2244_ = v___x_2278_;
goto v___jp_2243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3___boxed(lean_object* v_a_2362_, lean_object* v_prio_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_f_2369_, lean_object* v_x_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lake_Job_bindM___redArg___lam__3(v_a_2362_, v_prio_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_f_2369_, v_x_2370_);
lean_dec_ref(v_a_2368_);
lean_dec_ref(v_a_2367_);
lean_dec(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2362_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg(lean_object* v_kind_2373_, lean_object* v_self_2374_, lean_object* v_f_2375_, lean_object* v_prio_2376_, uint8_t v_sync_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_task_2385_; lean_object* v_caption_2386_; uint8_t v_optional_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2396_; 
v_task_2385_ = lean_ctor_get(v_self_2374_, 0);
v_caption_2386_ = lean_ctor_get(v_self_2374_, 2);
v_optional_2387_ = lean_ctor_get_uint8(v_self_2374_, sizeof(void*)*3);
v_isSharedCheck_2396_ = !lean_is_exclusive(v_self_2374_);
if (v_isSharedCheck_2396_ == 0)
{
lean_object* v_unused_2397_; 
v_unused_2397_ = lean_ctor_get(v_self_2374_, 1);
lean_dec(v_unused_2397_);
v___x_2389_ = v_self_2374_;
v_isShared_2390_ = v_isSharedCheck_2396_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_caption_2386_);
lean_inc(v_task_2385_);
lean_dec(v_self_2374_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2396_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___f_2391_; lean_object* v___x_2392_; lean_object* v___x_2394_; 
lean_inc_ref(v_a_2383_);
lean_inc_ref(v_a_2381_);
lean_inc(v_a_2380_);
lean_inc(v_a_2379_);
lean_inc(v_prio_2376_);
lean_inc_ref(v_a_2382_);
v___f_2391_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__3___boxed), 10, 8);
lean_closure_set(v___f_2391_, 0, v_a_2382_);
lean_closure_set(v___f_2391_, 1, v_prio_2376_);
lean_closure_set(v___f_2391_, 2, v_a_2378_);
lean_closure_set(v___f_2391_, 3, v_a_2379_);
lean_closure_set(v___f_2391_, 4, v_a_2380_);
lean_closure_set(v___f_2391_, 5, v_a_2381_);
lean_closure_set(v___f_2391_, 6, v_a_2383_);
lean_closure_set(v___f_2391_, 7, v_f_2375_);
v___x_2392_ = lean_io_bind_task(v_task_2385_, v___f_2391_, v_prio_2376_, v_sync_2377_);
if (v_isShared_2390_ == 0)
{
lean_ctor_set(v___x_2389_, 1, v_kind_2373_);
lean_ctor_set(v___x_2389_, 0, v___x_2392_);
v___x_2394_ = v___x_2389_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v___x_2392_);
lean_ctor_set(v_reuseFailAlloc_2395_, 1, v_kind_2373_);
lean_ctor_set(v_reuseFailAlloc_2395_, 2, v_caption_2386_);
lean_ctor_set_uint8(v_reuseFailAlloc_2395_, sizeof(void*)*3, v_optional_2387_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object* v_kind_2398_, lean_object* v_self_2399_, lean_object* v_f_2400_, lean_object* v_prio_2401_, lean_object* v_sync_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
uint8_t v_sync_boxed_2410_; lean_object* v_res_2411_; 
v_sync_boxed_2410_ = lean_unbox(v_sync_2402_);
v_res_2411_ = l_Lake_Job_bindM___redArg(v_kind_2398_, v_self_2399_, v_f_2400_, v_prio_2401_, v_sync_boxed_2410_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec_ref(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec(v_a_2404_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM(lean_object* v_00_u03b2_2412_, lean_object* v_00_u03b1_2413_, lean_object* v_kind_2414_, lean_object* v_self_2415_, lean_object* v_f_2416_, lean_object* v_prio_2417_, uint8_t v_sync_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; 
v___x_2426_ = l_Lake_Job_bindM___redArg(v_kind_2414_, v_self_2415_, v_f_2416_, v_prio_2417_, v_sync_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object* v_00_u03b2_2427_, lean_object* v_00_u03b1_2428_, lean_object* v_kind_2429_, lean_object* v_self_2430_, lean_object* v_f_2431_, lean_object* v_prio_2432_, lean_object* v_sync_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
uint8_t v_sync_boxed_2441_; lean_object* v_res_2442_; 
v_sync_boxed_2441_ = lean_unbox(v_sync_2433_);
v_res_2442_ = l_Lake_Job_bindM(v_00_u03b2_2427_, v_00_u03b1_2428_, v_kind_2429_, v_self_2430_, v_f_2431_, v_prio_2432_, v_sync_boxed_2441_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
lean_dec_ref(v_a_2439_);
lean_dec_ref(v_a_2438_);
lean_dec_ref(v_a_2437_);
lean_dec(v_a_2436_);
lean_dec(v_a_2435_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object* v_f_2443_, lean_object* v_rx_2444_, lean_object* v_ry_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_apply_2(v_f_2443_, v_rx_2444_, v_ry_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object* v_other_2447_, lean_object* v_f_2448_, lean_object* v_prio_2449_, uint8_t v_sync_2450_, lean_object* v_rx_2451_){
_start:
{
lean_object* v_task_2452_; lean_object* v___f_2453_; lean_object* v___x_2454_; 
v_task_2452_ = lean_ctor_get(v_other_2447_, 0);
lean_inc_ref(v_task_2452_);
lean_dec_ref(v_other_2447_);
v___f_2453_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2453_, 0, v_f_2448_);
lean_closure_set(v___f_2453_, 1, v_rx_2451_);
v___x_2454_ = lean_task_map(v___f_2453_, v_task_2452_, v_prio_2449_, v_sync_2450_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object* v_other_2455_, lean_object* v_f_2456_, lean_object* v_prio_2457_, lean_object* v_sync_2458_, lean_object* v_rx_2459_){
_start:
{
uint8_t v_sync_boxed_2460_; lean_object* v_res_2461_; 
v_sync_boxed_2460_ = lean_unbox(v_sync_2458_);
v_res_2461_ = l_Lake_Job_zipResultWith___redArg___lam__1(v_other_2455_, v_f_2456_, v_prio_2457_, v_sync_boxed_2460_, v_rx_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg(lean_object* v_inst_2462_, lean_object* v_f_2463_, lean_object* v_self_2464_, lean_object* v_other_2465_, lean_object* v_prio_2466_, uint8_t v_sync_2467_){
_start:
{
lean_object* v_task_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2481_; 
v_task_2468_ = lean_ctor_get(v_self_2464_, 0);
v_isSharedCheck_2481_ = !lean_is_exclusive(v_self_2464_);
if (v_isSharedCheck_2481_ == 0)
{
lean_object* v_unused_2482_; lean_object* v_unused_2483_; 
v_unused_2482_ = lean_ctor_get(v_self_2464_, 2);
lean_dec(v_unused_2482_);
v_unused_2483_ = lean_ctor_get(v_self_2464_, 1);
lean_dec(v_unused_2483_);
v___x_2470_ = v_self_2464_;
v_isShared_2471_ = v_isSharedCheck_2481_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_task_2468_);
lean_dec(v_self_2464_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2481_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___f_2473_; uint8_t v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2479_; 
v___x_2472_ = lean_box(v_sync_2467_);
lean_inc(v_prio_2466_);
v___f_2473_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2473_, 0, v_other_2465_);
lean_closure_set(v___f_2473_, 1, v_f_2463_);
lean_closure_set(v___f_2473_, 2, v_prio_2466_);
lean_closure_set(v___f_2473_, 3, v___x_2472_);
v___x_2474_ = 1;
v___x_2475_ = lean_task_bind(v_task_2468_, v___f_2473_, v_prio_2466_, v___x_2474_);
v___x_2476_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2477_ = 0;
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 2, v___x_2476_);
lean_ctor_set(v___x_2470_, 1, v_inst_2462_);
lean_ctor_set(v___x_2470_, 0, v___x_2475_);
v___x_2479_ = v___x_2470_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2480_; 
v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2475_);
lean_ctor_set(v_reuseFailAlloc_2480_, 1, v_inst_2462_);
lean_ctor_set(v_reuseFailAlloc_2480_, 2, v___x_2476_);
v___x_2479_ = v_reuseFailAlloc_2480_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_ctor_set_uint8(v___x_2479_, sizeof(void*)*3, v___x_2477_);
return v___x_2479_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object* v_inst_2484_, lean_object* v_f_2485_, lean_object* v_self_2486_, lean_object* v_other_2487_, lean_object* v_prio_2488_, lean_object* v_sync_2489_){
_start:
{
uint8_t v_sync_boxed_2490_; lean_object* v_res_2491_; 
v_sync_boxed_2490_ = lean_unbox(v_sync_2489_);
v_res_2491_ = l_Lake_Job_zipResultWith___redArg(v_inst_2484_, v_f_2485_, v_self_2486_, v_other_2487_, v_prio_2488_, v_sync_boxed_2490_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith(lean_object* v_00_u03b3_2492_, lean_object* v_00_u03b1_2493_, lean_object* v_00_u03b2_2494_, lean_object* v_inst_2495_, lean_object* v_f_2496_, lean_object* v_self_2497_, lean_object* v_other_2498_, lean_object* v_prio_2499_, uint8_t v_sync_2500_){
_start:
{
lean_object* v_task_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_2514_; 
v_task_2501_ = lean_ctor_get(v_self_2497_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v_self_2497_);
if (v_isSharedCheck_2514_ == 0)
{
lean_object* v_unused_2515_; lean_object* v_unused_2516_; 
v_unused_2515_ = lean_ctor_get(v_self_2497_, 2);
lean_dec(v_unused_2515_);
v_unused_2516_ = lean_ctor_get(v_self_2497_, 1);
lean_dec(v_unused_2516_);
v___x_2503_ = v_self_2497_;
v_isShared_2504_ = v_isSharedCheck_2514_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_task_2501_);
lean_dec(v_self_2497_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_2514_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2505_; lean_object* v___f_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2512_; 
v___x_2505_ = lean_box(v_sync_2500_);
lean_inc(v_prio_2499_);
v___f_2506_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2506_, 0, v_other_2498_);
lean_closure_set(v___f_2506_, 1, v_f_2496_);
lean_closure_set(v___f_2506_, 2, v_prio_2499_);
lean_closure_set(v___f_2506_, 3, v___x_2505_);
v___x_2507_ = 1;
v___x_2508_ = lean_task_bind(v_task_2501_, v___f_2506_, v_prio_2499_, v___x_2507_);
v___x_2509_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2510_ = 0;
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 2, v___x_2509_);
lean_ctor_set(v___x_2503_, 1, v_inst_2495_);
lean_ctor_set(v___x_2503_, 0, v___x_2508_);
v___x_2512_ = v___x_2503_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2508_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_inst_2495_);
lean_ctor_set(v_reuseFailAlloc_2513_, 2, v___x_2509_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_ctor_set_uint8(v___x_2512_, sizeof(void*)*3, v___x_2510_);
return v___x_2512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object* v_00_u03b3_2517_, lean_object* v_00_u03b1_2518_, lean_object* v_00_u03b2_2519_, lean_object* v_inst_2520_, lean_object* v_f_2521_, lean_object* v_self_2522_, lean_object* v_other_2523_, lean_object* v_prio_2524_, lean_object* v_sync_2525_){
_start:
{
uint8_t v_sync_boxed_2526_; lean_object* v_res_2527_; 
v_sync_boxed_2526_ = lean_unbox(v_sync_2525_);
v_res_2527_ = l_Lake_Job_zipResultWith(v_00_u03b3_2517_, v_00_u03b1_2518_, v_00_u03b2_2519_, v_inst_2520_, v_f_2521_, v_self_2522_, v_other_2523_, v_prio_2524_, v_sync_boxed_2526_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object* v_rx_2528_, lean_object* v_f_2529_, lean_object* v_ry_2530_){
_start:
{
lean_object* v___y_2532_; lean_object* v___y_2533_; lean_object* v___y_2534_; lean_object* v___y_2538_; lean_object* v___y_2539_; lean_object* v___y_2540_; lean_object* v_a_2543_; 
if (lean_obj_tag(v_rx_2528_) == 0)
{
if (lean_obj_tag(v_ry_2530_) == 0)
{
lean_object* v_a_2545_; lean_object* v_a_2546_; lean_object* v_a_2547_; lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2557_; 
v_a_2545_ = lean_ctor_get(v_rx_2528_, 0);
lean_inc(v_a_2545_);
v_a_2546_ = lean_ctor_get(v_rx_2528_, 1);
lean_inc(v_a_2546_);
lean_dec_ref_known(v_rx_2528_, 2);
v_a_2547_ = lean_ctor_get(v_ry_2530_, 0);
v_a_2548_ = lean_ctor_get(v_ry_2530_, 1);
v_isSharedCheck_2557_ = !lean_is_exclusive(v_ry_2530_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2550_ = v_ry_2530_;
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_inc(v_a_2547_);
lean_dec(v_ry_2530_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2557_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2555_; 
v___x_2552_ = lean_apply_2(v_f_2529_, v_a_2545_, v_a_2547_);
v___x_2553_ = l_Lake_JobState_merge(v_a_2546_, v_a_2548_);
if (v_isShared_2551_ == 0)
{
lean_ctor_set(v___x_2550_, 1, v___x_2553_);
lean_ctor_set(v___x_2550_, 0, v___x_2552_);
v___x_2555_ = v___x_2550_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2552_);
lean_ctor_set(v_reuseFailAlloc_2556_, 1, v___x_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
else
{
lean_object* v_a_2558_; 
lean_dec(v_f_2529_);
v_a_2558_ = lean_ctor_get(v_rx_2528_, 1);
lean_inc(v_a_2558_);
lean_dec_ref_known(v_rx_2528_, 2);
v_a_2543_ = v_a_2558_;
goto v___jp_2542_;
}
}
else
{
lean_dec(v_f_2529_);
if (lean_obj_tag(v_rx_2528_) == 0)
{
lean_object* v_a_2559_; 
v_a_2559_ = lean_ctor_get(v_rx_2528_, 1);
lean_inc(v_a_2559_);
lean_dec_ref_known(v_rx_2528_, 2);
v_a_2543_ = v_a_2559_;
goto v___jp_2542_;
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2561_; 
v_a_2560_ = lean_ctor_get(v_rx_2528_, 1);
lean_inc(v_a_2560_);
lean_dec_ref_known(v_rx_2528_, 2);
v___x_2561_ = lean_unsigned_to_nat(0u);
v___y_2538_ = v_ry_2530_;
v___y_2539_ = v___x_2561_;
v___y_2540_ = v_a_2560_;
goto v___jp_2537_;
}
}
v___jp_2531_:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = l_Lake_JobState_merge(v___y_2533_, v___y_2534_);
v___x_2536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___y_2532_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
return v___x_2536_;
}
v___jp_2537_:
{
lean_object* v_a_2541_; 
v_a_2541_ = lean_ctor_get(v___y_2538_, 1);
lean_inc(v_a_2541_);
lean_dec_ref(v___y_2538_);
v___y_2532_ = v___y_2539_;
v___y_2533_ = v___y_2540_;
v___y_2534_ = v_a_2541_;
goto v___jp_2531_;
}
v___jp_2542_:
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_unsigned_to_nat(0u);
v___y_2538_ = v_ry_2530_;
v___y_2539_ = v___x_2544_;
v___y_2540_ = v_a_2543_;
goto v___jp_2537_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object* v_other_2562_, lean_object* v_f_2563_, lean_object* v_prio_2564_, uint8_t v_sync_2565_, lean_object* v_rx_2566_){
_start:
{
lean_object* v_task_2567_; lean_object* v___f_2568_; lean_object* v___x_2569_; 
v_task_2567_ = lean_ctor_get(v_other_2562_, 0);
lean_inc_ref(v_task_2567_);
lean_dec_ref(v_other_2562_);
v___f_2568_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2568_, 0, v_rx_2566_);
lean_closure_set(v___f_2568_, 1, v_f_2563_);
v___x_2569_ = lean_task_map(v___f_2568_, v_task_2567_, v_prio_2564_, v_sync_2565_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object* v_other_2570_, lean_object* v_f_2571_, lean_object* v_prio_2572_, lean_object* v_sync_2573_, lean_object* v_rx_2574_){
_start:
{
uint8_t v_sync_boxed_2575_; lean_object* v_res_2576_; 
v_sync_boxed_2575_ = lean_unbox(v_sync_2573_);
v_res_2576_ = l_Lake_Job_zipWith___redArg___lam__1(v_other_2570_, v_f_2571_, v_prio_2572_, v_sync_boxed_2575_, v_rx_2574_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg(lean_object* v_inst_2577_, lean_object* v_f_2578_, lean_object* v_self_2579_, lean_object* v_other_2580_, lean_object* v_prio_2581_, uint8_t v_sync_2582_){
_start:
{
lean_object* v_task_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2596_; 
v_task_2583_ = lean_ctor_get(v_self_2579_, 0);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_self_2579_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; lean_object* v_unused_2598_; 
v_unused_2597_ = lean_ctor_get(v_self_2579_, 2);
lean_dec(v_unused_2597_);
v_unused_2598_ = lean_ctor_get(v_self_2579_, 1);
lean_dec(v_unused_2598_);
v___x_2585_ = v_self_2579_;
v_isShared_2586_ = v_isSharedCheck_2596_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_task_2583_);
lean_dec(v_self_2579_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2596_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2587_; lean_object* v___f_2588_; uint8_t v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; uint8_t v___x_2592_; lean_object* v___x_2594_; 
v___x_2587_ = lean_box(v_sync_2582_);
lean_inc(v_prio_2581_);
v___f_2588_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2588_, 0, v_other_2580_);
lean_closure_set(v___f_2588_, 1, v_f_2578_);
lean_closure_set(v___f_2588_, 2, v_prio_2581_);
lean_closure_set(v___f_2588_, 3, v___x_2587_);
v___x_2589_ = 1;
v___x_2590_ = lean_task_bind(v_task_2583_, v___f_2588_, v_prio_2581_, v___x_2589_);
v___x_2591_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2592_ = 0;
if (v_isShared_2586_ == 0)
{
lean_ctor_set(v___x_2585_, 2, v___x_2591_);
lean_ctor_set(v___x_2585_, 1, v_inst_2577_);
lean_ctor_set(v___x_2585_, 0, v___x_2590_);
v___x_2594_ = v___x_2585_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2590_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_inst_2577_);
lean_ctor_set(v_reuseFailAlloc_2595_, 2, v___x_2591_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*3, v___x_2592_);
return v___x_2594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object* v_inst_2599_, lean_object* v_f_2600_, lean_object* v_self_2601_, lean_object* v_other_2602_, lean_object* v_prio_2603_, lean_object* v_sync_2604_){
_start:
{
uint8_t v_sync_boxed_2605_; lean_object* v_res_2606_; 
v_sync_boxed_2605_ = lean_unbox(v_sync_2604_);
v_res_2606_ = l_Lake_Job_zipWith___redArg(v_inst_2599_, v_f_2600_, v_self_2601_, v_other_2602_, v_prio_2603_, v_sync_boxed_2605_);
return v_res_2606_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__0(lean_object* v_rx_2607_, lean_object* v_f_2608_, lean_object* v_ry_2609_){
_start:
{
lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v_a_2622_; lean_object* v_rb_2623_; 
if (lean_obj_tag(v_rx_2607_) == 0)
{
if (lean_obj_tag(v_ry_2609_) == 0)
{
lean_object* v_a_2625_; lean_object* v_a_2626_; lean_object* v_a_2627_; lean_object* v_a_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2637_; 
v_a_2625_ = lean_ctor_get(v_rx_2607_, 0);
lean_inc(v_a_2625_);
v_a_2626_ = lean_ctor_get(v_rx_2607_, 1);
lean_inc(v_a_2626_);
lean_dec_ref_known(v_rx_2607_, 2);
v_a_2627_ = lean_ctor_get(v_ry_2609_, 0);
v_a_2628_ = lean_ctor_get(v_ry_2609_, 1);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_ry_2609_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2630_ = v_ry_2609_;
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_a_2628_);
lean_inc(v_a_2627_);
lean_dec(v_ry_2609_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2632_ = lean_apply_2(v_f_2608_, v_a_2625_, v_a_2627_);
v___x_2633_ = l_Lake_JobState_merge(v_a_2626_, v_a_2628_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 1, v___x_2633_);
lean_ctor_set(v___x_2630_, 0, v___x_2632_);
v___x_2635_ = v___x_2630_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
else
{
lean_object* v_a_2638_; 
lean_dec(v_f_2608_);
v_a_2638_ = lean_ctor_get(v_rx_2607_, 1);
lean_inc(v_a_2638_);
lean_dec_ref_known(v_rx_2607_, 2);
v_a_2622_ = v_a_2638_;
v_rb_2623_ = v_ry_2609_;
goto v___jp_2621_;
}
}
else
{
lean_dec(v_f_2608_);
if (lean_obj_tag(v_rx_2607_) == 0)
{
lean_object* v_a_2639_; 
v_a_2639_ = lean_ctor_get(v_rx_2607_, 1);
lean_inc(v_a_2639_);
lean_dec_ref_known(v_rx_2607_, 2);
v_a_2622_ = v_a_2639_;
v_rb_2623_ = v_ry_2609_;
goto v___jp_2621_;
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2641_; 
v_a_2640_ = lean_ctor_get(v_rx_2607_, 1);
lean_inc(v_a_2640_);
lean_dec_ref_known(v_rx_2607_, 2);
v___x_2641_ = lean_unsigned_to_nat(0u);
v___y_2617_ = v_ry_2609_;
v___y_2618_ = v___x_2641_;
v___y_2619_ = v_a_2640_;
goto v___jp_2616_;
}
}
v___jp_2610_:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = l_Lake_JobState_merge(v___y_2612_, v___y_2613_);
v___x_2615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___y_2611_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
return v___x_2615_;
}
v___jp_2616_:
{
lean_object* v_a_2620_; 
v_a_2620_ = lean_ctor_get(v___y_2617_, 1);
lean_inc(v_a_2620_);
lean_dec_ref(v___y_2617_);
v___y_2611_ = v___y_2618_;
v___y_2612_ = v___y_2619_;
v___y_2613_ = v_a_2620_;
goto v___jp_2610_;
}
v___jp_2621_:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_unsigned_to_nat(0u);
v___y_2617_ = v_rb_2623_;
v___y_2618_ = v___x_2624_;
v___y_2619_ = v_a_2622_;
goto v___jp_2616_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1(lean_object* v_other_2642_, lean_object* v_f_2643_, lean_object* v_prio_2644_, uint8_t v_sync_2645_, lean_object* v_rx_2646_){
_start:
{
lean_object* v_task_2647_; lean_object* v___f_2648_; lean_object* v___x_2649_; 
v_task_2647_ = lean_ctor_get(v_other_2642_, 0);
lean_inc_ref(v_task_2647_);
lean_dec_ref(v_other_2642_);
v___f_2648_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__0), 3, 2);
lean_closure_set(v___f_2648_, 0, v_rx_2646_);
lean_closure_set(v___f_2648_, 1, v_f_2643_);
v___x_2649_ = lean_task_map(v___f_2648_, v_task_2647_, v_prio_2644_, v_sync_2645_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1___boxed(lean_object* v_other_2650_, lean_object* v_f_2651_, lean_object* v_prio_2652_, lean_object* v_sync_2653_, lean_object* v_rx_2654_){
_start:
{
uint8_t v_sync_boxed_2655_; lean_object* v_res_2656_; 
v_sync_boxed_2655_ = lean_unbox(v_sync_2653_);
v_res_2656_ = l_Lake_Job_zipWith___lam__1(v_other_2650_, v_f_2651_, v_prio_2652_, v_sync_boxed_2655_, v_rx_2654_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith(lean_object* v_00_u03b3_2657_, lean_object* v_00_u03b1_2658_, lean_object* v_00_u03b2_2659_, lean_object* v_inst_2660_, lean_object* v_f_2661_, lean_object* v_self_2662_, lean_object* v_other_2663_, lean_object* v_prio_2664_, uint8_t v_sync_2665_){
_start:
{
lean_object* v_task_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2679_; 
v_task_2666_ = lean_ctor_get(v_self_2662_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_self_2662_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; lean_object* v_unused_2681_; 
v_unused_2680_ = lean_ctor_get(v_self_2662_, 2);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_self_2662_, 1);
lean_dec(v_unused_2681_);
v___x_2668_ = v_self_2662_;
v_isShared_2669_ = v_isSharedCheck_2679_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_task_2666_);
lean_dec(v_self_2662_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2679_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___f_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; lean_object* v___x_2677_; 
v___x_2670_ = lean_box(v_sync_2665_);
lean_inc(v_prio_2664_);
v___f_2671_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2671_, 0, v_other_2663_);
lean_closure_set(v___f_2671_, 1, v_f_2661_);
lean_closure_set(v___f_2671_, 2, v_prio_2664_);
lean_closure_set(v___f_2671_, 3, v___x_2670_);
v___x_2672_ = 1;
v___x_2673_ = lean_task_bind(v_task_2666_, v___f_2671_, v_prio_2664_, v___x_2672_);
v___x_2674_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2675_ = 0;
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 2, v___x_2674_);
lean_ctor_set(v___x_2668_, 1, v_inst_2660_);
lean_ctor_set(v___x_2668_, 0, v___x_2673_);
v___x_2677_ = v___x_2668_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v___x_2673_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_inst_2660_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v___x_2674_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
lean_ctor_set_uint8(v___x_2677_, sizeof(void*)*3, v___x_2675_);
return v___x_2677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object* v_00_u03b3_2682_, lean_object* v_00_u03b1_2683_, lean_object* v_00_u03b2_2684_, lean_object* v_inst_2685_, lean_object* v_f_2686_, lean_object* v_self_2687_, lean_object* v_other_2688_, lean_object* v_prio_2689_, lean_object* v_sync_2690_){
_start:
{
uint8_t v_sync_boxed_2691_; lean_object* v_res_2692_; 
v_sync_boxed_2691_ = lean_unbox(v_sync_2690_);
v_res_2692_ = l_Lake_Job_zipWith(v_00_u03b3_2682_, v_00_u03b1_2683_, v_00_u03b2_2684_, v_inst_2685_, v_f_2686_, v_self_2687_, v_other_2688_, v_prio_2689_, v_sync_boxed_2691_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object* v___x_2693_, lean_object* v_rx_2694_, lean_object* v_ry_2695_){
_start:
{
lean_object* v___y_2697_; lean_object* v___y_2698_; lean_object* v___y_2717_; lean_object* v___y_2718_; 
if (lean_obj_tag(v_rx_2694_) == 0)
{
if (lean_obj_tag(v_ry_2695_) == 0)
{
lean_object* v_a_2720_; lean_object* v_a_2721_; lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2745_; 
lean_dec(v___x_2693_);
v_a_2720_ = lean_ctor_get(v_rx_2694_, 0);
lean_inc(v_a_2720_);
v_a_2721_ = lean_ctor_get(v_rx_2694_, 1);
lean_inc(v_a_2721_);
lean_dec_ref_known(v_rx_2694_, 2);
v_a_2722_ = lean_ctor_get(v_ry_2695_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_ry_2695_);
if (v_isSharedCheck_2745_ == 0)
{
lean_object* v_unused_2746_; 
v_unused_2746_ = lean_ctor_get(v_ry_2695_, 0);
lean_dec(v_unused_2746_);
v___x_2724_ = v_ry_2695_;
v_isShared_2725_ = v_isSharedCheck_2745_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v_ry_2695_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2745_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2726_; lean_object* v_log_2727_; uint8_t v_action_2728_; uint8_t v_wantsRebuild_2729_; uint8_t v_canceled_2730_; lean_object* v_buildTime_2731_; lean_object* v_trace_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2742_; 
lean_inc(v_a_2721_);
v___x_2726_ = l_Lake_JobState_merge(v_a_2721_, v_a_2722_);
v_log_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc_ref(v_log_2727_);
v_action_2728_ = lean_ctor_get_uint8(v___x_2726_, sizeof(void*)*3);
v_wantsRebuild_2729_ = lean_ctor_get_uint8(v___x_2726_, sizeof(void*)*3 + 1);
v_canceled_2730_ = lean_ctor_get_uint8(v___x_2726_, sizeof(void*)*3 + 2);
v_buildTime_2731_ = lean_ctor_get(v___x_2726_, 2);
lean_inc(v_buildTime_2731_);
lean_dec_ref(v___x_2726_);
v_trace_2732_ = lean_ctor_get(v_a_2721_, 1);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_a_2721_);
if (v_isSharedCheck_2742_ == 0)
{
lean_object* v_unused_2743_; lean_object* v_unused_2744_; 
v_unused_2743_ = lean_ctor_get(v_a_2721_, 2);
lean_dec(v_unused_2743_);
v_unused_2744_ = lean_ctor_get(v_a_2721_, 0);
lean_dec(v_unused_2744_);
v___x_2734_ = v_a_2721_;
v_isShared_2735_ = v_isSharedCheck_2742_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_trace_2732_);
lean_dec(v_a_2721_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2742_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 2, v_buildTime_2731_);
lean_ctor_set(v___x_2734_, 0, v_log_2727_);
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v_log_2727_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_trace_2732_);
lean_ctor_set(v_reuseFailAlloc_2741_, 2, v_buildTime_2731_);
v___x_2737_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
lean_object* v___x_2739_; 
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*3, v_action_2728_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*3 + 1, v_wantsRebuild_2729_);
lean_ctor_set_uint8(v___x_2737_, sizeof(void*)*3 + 2, v_canceled_2730_);
if (v_isShared_2725_ == 0)
{
lean_ctor_set(v___x_2724_, 1, v___x_2737_);
lean_ctor_set(v___x_2724_, 0, v_a_2720_);
v___x_2739_ = v___x_2724_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2720_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2737_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
}
else
{
lean_object* v_a_2747_; 
v_a_2747_ = lean_ctor_get(v_rx_2694_, 1);
lean_inc(v_a_2747_);
lean_dec_ref_known(v_rx_2694_, 2);
v___y_2717_ = v_ry_2695_;
v___y_2718_ = v_a_2747_;
goto v___jp_2716_;
}
}
else
{
lean_object* v_a_2748_; 
v_a_2748_ = lean_ctor_get(v_rx_2694_, 1);
lean_inc(v_a_2748_);
lean_dec_ref(v_rx_2694_);
v___y_2717_ = v_ry_2695_;
v___y_2718_ = v_a_2748_;
goto v___jp_2716_;
}
v___jp_2696_:
{
lean_object* v___x_2699_; lean_object* v_log_2700_; uint8_t v_action_2701_; uint8_t v_wantsRebuild_2702_; uint8_t v_canceled_2703_; lean_object* v_buildTime_2704_; lean_object* v_trace_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2713_; 
lean_inc_ref(v___y_2697_);
v___x_2699_ = l_Lake_JobState_merge(v___y_2697_, v___y_2698_);
v_log_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc_ref(v_log_2700_);
v_action_2701_ = lean_ctor_get_uint8(v___x_2699_, sizeof(void*)*3);
v_wantsRebuild_2702_ = lean_ctor_get_uint8(v___x_2699_, sizeof(void*)*3 + 1);
v_canceled_2703_ = lean_ctor_get_uint8(v___x_2699_, sizeof(void*)*3 + 2);
v_buildTime_2704_ = lean_ctor_get(v___x_2699_, 2);
lean_inc(v_buildTime_2704_);
lean_dec_ref(v___x_2699_);
v_trace_2705_ = lean_ctor_get(v___y_2697_, 1);
v_isSharedCheck_2713_ = !lean_is_exclusive(v___y_2697_);
if (v_isSharedCheck_2713_ == 0)
{
lean_object* v_unused_2714_; lean_object* v_unused_2715_; 
v_unused_2714_ = lean_ctor_get(v___y_2697_, 2);
lean_dec(v_unused_2714_);
v_unused_2715_ = lean_ctor_get(v___y_2697_, 0);
lean_dec(v_unused_2715_);
v___x_2707_ = v___y_2697_;
v_isShared_2708_ = v_isSharedCheck_2713_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_trace_2705_);
lean_dec(v___y_2697_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2713_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v___x_2710_; 
if (v_isShared_2708_ == 0)
{
lean_ctor_set(v___x_2707_, 2, v_buildTime_2704_);
lean_ctor_set(v___x_2707_, 0, v_log_2700_);
v___x_2710_ = v___x_2707_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2712_; 
v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_log_2700_);
lean_ctor_set(v_reuseFailAlloc_2712_, 1, v_trace_2705_);
lean_ctor_set(v_reuseFailAlloc_2712_, 2, v_buildTime_2704_);
v___x_2710_ = v_reuseFailAlloc_2712_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
lean_object* v___x_2711_; 
lean_ctor_set_uint8(v___x_2710_, sizeof(void*)*3, v_action_2701_);
lean_ctor_set_uint8(v___x_2710_, sizeof(void*)*3 + 1, v_wantsRebuild_2702_);
lean_ctor_set_uint8(v___x_2710_, sizeof(void*)*3 + 2, v_canceled_2703_);
v___x_2711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2693_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
return v___x_2711_;
}
}
}
v___jp_2716_:
{
lean_object* v_a_2719_; 
v_a_2719_ = lean_ctor_get(v___y_2717_, 1);
lean_inc(v_a_2719_);
lean_dec_ref(v___y_2717_);
v___y_2697_ = v___y_2718_;
v___y_2698_ = v_a_2719_;
goto v___jp_2696_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1(lean_object* v_other_2749_, lean_object* v___x_2750_, uint8_t v___x_2751_, lean_object* v_rx_2752_){
_start:
{
lean_object* v_task_2753_; lean_object* v___f_2754_; lean_object* v___x_2755_; 
v_task_2753_ = lean_ctor_get(v_other_2749_, 0);
lean_inc_ref(v_task_2753_);
lean_dec_ref(v_other_2749_);
lean_inc(v___x_2750_);
v___f_2754_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2754_, 0, v___x_2750_);
lean_closure_set(v___f_2754_, 1, v_rx_2752_);
v___x_2755_ = lean_task_map(v___f_2754_, v_task_2753_, v___x_2750_, v___x_2751_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object* v_other_2756_, lean_object* v___x_2757_, lean_object* v___x_2758_, lean_object* v_rx_2759_){
_start:
{
uint8_t v___x_258__boxed_2760_; lean_object* v_res_2761_; 
v___x_258__boxed_2760_ = lean_unbox(v___x_2758_);
v_res_2761_ = l_Lake_Job_add___redArg___lam__1(v_other_2756_, v___x_2757_, v___x_258__boxed_2760_, v_rx_2759_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object* v_self_2762_, lean_object* v_other_2763_){
_start:
{
lean_object* v_task_2764_; lean_object* v_kind_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2779_; 
v_task_2764_ = lean_ctor_get(v_self_2762_, 0);
v_kind_2765_ = lean_ctor_get(v_self_2762_, 1);
v_isSharedCheck_2779_ = !lean_is_exclusive(v_self_2762_);
if (v_isSharedCheck_2779_ == 0)
{
lean_object* v_unused_2780_; 
v_unused_2780_ = lean_ctor_get(v_self_2762_, 2);
lean_dec(v_unused_2780_);
v___x_2767_ = v_self_2762_;
v_isShared_2768_ = v_isSharedCheck_2779_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_kind_2765_);
lean_inc(v_task_2764_);
lean_dec(v_self_2762_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2779_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2769_; uint8_t v___x_2770_; lean_object* v___x_2771_; lean_object* v___f_2772_; uint8_t v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = 0;
v___x_2771_ = lean_box(v___x_2770_);
v___f_2772_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2772_, 0, v_other_2763_);
lean_closure_set(v___f_2772_, 1, v___x_2769_);
lean_closure_set(v___f_2772_, 2, v___x_2771_);
v___x_2773_ = 1;
v___x_2774_ = lean_task_bind(v_task_2764_, v___f_2772_, v___x_2769_, v___x_2773_);
v___x_2775_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2768_ == 0)
{
lean_ctor_set(v___x_2767_, 2, v___x_2775_);
lean_ctor_set(v___x_2767_, 0, v___x_2774_);
v___x_2777_ = v___x_2767_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2778_, 1, v_kind_2765_);
lean_ctor_set(v_reuseFailAlloc_2778_, 2, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_ctor_set_uint8(v___x_2777_, sizeof(void*)*3, v___x_2770_);
return v___x_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object* v_00_u03b1_2781_, lean_object* v_00_u03b2_2782_, lean_object* v_self_2783_, lean_object* v_other_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Lake_Job_add___redArg(v_self_2783_, v_other_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object* v___x_2786_, lean_object* v_rx_2787_, lean_object* v_ry_2788_){
_start:
{
lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2795_; lean_object* v___y_2796_; 
if (lean_obj_tag(v_rx_2787_) == 0)
{
if (lean_obj_tag(v_ry_2788_) == 0)
{
lean_object* v_a_2798_; lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v___x_2786_);
v_a_2798_ = lean_ctor_get(v_rx_2787_, 1);
lean_inc(v_a_2798_);
lean_dec_ref_known(v_rx_2787_, 2);
v_a_2799_ = lean_ctor_get(v_ry_2788_, 1);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_ry_2788_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; 
v_unused_2809_ = lean_ctor_get(v_ry_2788_, 0);
lean_dec(v_unused_2809_);
v___x_2801_ = v_ry_2788_;
v_isShared_2802_ = v_isSharedCheck_2808_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v_ry_2788_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2808_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2803_ = lean_box(0);
v___x_2804_ = l_Lake_JobState_merge(v_a_2798_, v_a_2799_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 1, v___x_2804_);
lean_ctor_set(v___x_2801_, 0, v___x_2803_);
v___x_2806_ = v___x_2801_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2803_);
lean_ctor_set(v_reuseFailAlloc_2807_, 1, v___x_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
else
{
lean_object* v_a_2810_; 
v_a_2810_ = lean_ctor_get(v_rx_2787_, 1);
lean_inc(v_a_2810_);
lean_dec_ref_known(v_rx_2787_, 2);
v___y_2795_ = v_ry_2788_;
v___y_2796_ = v_a_2810_;
goto v___jp_2794_;
}
}
else
{
lean_object* v_a_2811_; 
v_a_2811_ = lean_ctor_get(v_rx_2787_, 1);
lean_inc(v_a_2811_);
lean_dec_ref(v_rx_2787_);
v___y_2795_ = v_ry_2788_;
v___y_2796_ = v_a_2811_;
goto v___jp_2794_;
}
v___jp_2789_:
{
lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2792_ = l_Lake_JobState_merge(v___y_2790_, v___y_2791_);
v___x_2793_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2786_);
lean_ctor_set(v___x_2793_, 1, v___x_2792_);
return v___x_2793_;
}
v___jp_2794_:
{
lean_object* v_a_2797_; 
v_a_2797_ = lean_ctor_get(v___y_2795_, 1);
lean_inc(v_a_2797_);
lean_dec_ref(v___y_2795_);
v___y_2790_ = v___y_2796_;
v___y_2791_ = v_a_2797_;
goto v___jp_2789_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object* v_other_2812_, lean_object* v___x_2813_, uint8_t v___x_2814_, lean_object* v_rx_2815_){
_start:
{
lean_object* v_task_2816_; lean_object* v___f_2817_; lean_object* v___x_2818_; 
v_task_2816_ = lean_ctor_get(v_other_2812_, 0);
lean_inc_ref(v_task_2816_);
lean_dec_ref(v_other_2812_);
lean_inc(v___x_2813_);
v___f_2817_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2817_, 0, v___x_2813_);
lean_closure_set(v___f_2817_, 1, v_rx_2815_);
v___x_2818_ = lean_task_map(v___f_2817_, v_task_2816_, v___x_2813_, v___x_2814_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object* v_other_2819_, lean_object* v___x_2820_, lean_object* v___x_2821_, lean_object* v_rx_2822_){
_start:
{
uint8_t v___x_142__boxed_2823_; lean_object* v_res_2824_; 
v___x_142__boxed_2823_ = lean_unbox(v___x_2821_);
v_res_2824_ = l_Lake_Job_mix___redArg___lam__1(v_other_2819_, v___x_2820_, v___x_142__boxed_2823_, v_rx_2822_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object* v_self_2825_, lean_object* v_other_2826_){
_start:
{
lean_object* v_task_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2842_; 
v_task_2827_ = lean_ctor_get(v_self_2825_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_self_2825_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; lean_object* v_unused_2844_; 
v_unused_2843_ = lean_ctor_get(v_self_2825_, 2);
lean_dec(v_unused_2843_);
v_unused_2844_ = lean_ctor_get(v_self_2825_, 1);
lean_dec(v_unused_2844_);
v___x_2829_ = v_self_2825_;
v_isShared_2830_ = v_isSharedCheck_2842_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_task_2827_);
lean_dec(v_self_2825_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2842_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; uint8_t v___x_2833_; lean_object* v___x_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; lean_object* v___x_2840_; 
v___x_2831_ = l_Lake_instDataKindUnit;
v___x_2832_ = lean_unsigned_to_nat(0u);
v___x_2833_ = 1;
v___x_2834_ = lean_box(v___x_2833_);
v___f_2835_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2835_, 0, v_other_2826_);
lean_closure_set(v___f_2835_, 1, v___x_2832_);
lean_closure_set(v___f_2835_, 2, v___x_2834_);
v___x_2836_ = lean_task_bind(v_task_2827_, v___f_2835_, v___x_2832_, v___x_2833_);
v___x_2837_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2838_ = 0;
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 2, v___x_2837_);
lean_ctor_set(v___x_2829_, 1, v___x_2831_);
lean_ctor_set(v___x_2829_, 0, v___x_2836_);
v___x_2840_ = v___x_2829_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2836_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v___x_2831_);
lean_ctor_set(v_reuseFailAlloc_2841_, 2, v___x_2837_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*3, v___x_2838_);
return v___x_2840_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object* v_00_u03b1_2845_, lean_object* v_00_u03b2_2846_, lean_object* v_self_2847_, lean_object* v_other_2848_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l_Lake_Job_mix___redArg(v_self_2847_, v_other_2848_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(lean_object* v_as_2850_, size_t v_i_2851_, size_t v_stop_2852_, lean_object* v_b_2853_){
_start:
{
uint8_t v___x_2854_; 
v___x_2854_ = lean_usize_dec_eq(v_i_2851_, v_stop_2852_);
if (v___x_2854_ == 0)
{
size_t v___x_2855_; size_t v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2855_ = ((size_t)1ULL);
v___x_2856_ = lean_usize_sub(v_i_2851_, v___x_2855_);
v___x_2857_ = lean_array_uget_borrowed(v_as_2850_, v___x_2856_);
lean_inc(v___x_2857_);
v___x_2858_ = l_Lake_Job_mix___redArg(v___x_2857_, v_b_2853_);
v_i_2851_ = v___x_2856_;
v_b_2853_ = v___x_2858_;
goto _start;
}
else
{
return v_b_2853_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2860_, lean_object* v_i_2861_, lean_object* v_stop_2862_, lean_object* v_b_2863_){
_start:
{
size_t v_i_boxed_2864_; size_t v_stop_boxed_2865_; lean_object* v_res_2866_; 
v_i_boxed_2864_ = lean_unbox_usize(v_i_2861_);
lean_dec(v_i_2861_);
v_stop_boxed_2865_ = lean_unbox_usize(v_stop_2862_);
lean_dec(v_stop_2862_);
v_res_2866_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2860_, v_i_boxed_2864_, v_stop_boxed_2865_, v_b_2863_);
lean_dec_ref(v_as_2860_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(lean_object* v_init_2867_, lean_object* v_l_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; uint8_t v___x_2872_; 
v___x_2869_ = lean_array_mk(v_l_2868_);
v___x_2870_ = lean_array_get_size(v___x_2869_);
v___x_2871_ = lean_unsigned_to_nat(0u);
v___x_2872_ = lean_nat_dec_lt(v___x_2871_, v___x_2870_);
if (v___x_2872_ == 0)
{
lean_dec_ref(v___x_2869_);
return v_init_2867_;
}
else
{
size_t v___x_2873_; size_t v___x_2874_; lean_object* v___x_2875_; 
v___x_2873_ = lean_usize_of_nat(v___x_2870_);
v___x_2874_ = ((size_t)0ULL);
v___x_2875_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v___x_2869_, v___x_2873_, v___x_2874_, v_init_2867_);
lean_dec_ref(v___x_2869_);
return v___x_2875_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object* v_jobs_2876_, lean_object* v_traceCaption_2877_){
_start:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; uint8_t v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2878_ = lean_box(0);
v___x_2879_ = lean_box(0);
v___x_2880_ = lean_unsigned_to_nat(0u);
v___x_2881_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2882_ = 0;
v___x_2883_ = 0;
v___x_2884_ = l_Lake_BuildTrace_nil(v_traceCaption_2877_);
v___x_2885_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2885_, 0, v___x_2881_);
lean_ctor_set(v___x_2885_, 1, v___x_2884_);
lean_ctor_set(v___x_2885_, 2, v___x_2880_);
lean_ctor_set_uint8(v___x_2885_, sizeof(void*)*3, v___x_2882_);
lean_ctor_set_uint8(v___x_2885_, sizeof(void*)*3 + 1, v___x_2883_);
lean_ctor_set_uint8(v___x_2885_, sizeof(void*)*3 + 2, v___x_2883_);
v___x_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2878_);
lean_ctor_set(v___x_2886_, 1, v___x_2885_);
v___x_2887_ = lean_task_pure(v___x_2886_);
v___x_2888_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2889_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2889_, 0, v___x_2887_);
lean_ctor_set(v___x_2889_, 1, v___x_2879_);
lean_ctor_set(v___x_2889_, 2, v___x_2888_);
lean_ctor_set_uint8(v___x_2889_, sizeof(void*)*3, v___x_2883_);
v___x_2890_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v___x_2889_, v_jobs_2876_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object* v_00_u03b1_2891_, lean_object* v_jobs_2892_, lean_object* v_traceCaption_2893_){
_start:
{
lean_object* v___x_2894_; 
v___x_2894_ = l_Lake_Job_mixList___redArg(v_jobs_2892_, v_traceCaption_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0(lean_object* v_00_u03b1_2895_, lean_object* v_init_2896_, lean_object* v_l_2897_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v_init_2896_, v_l_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(lean_object* v_00_u03b1_2899_, lean_object* v_as_2900_, size_t v_i_2901_, size_t v_stop_2902_, lean_object* v_b_2903_){
_start:
{
lean_object* v___x_2904_; 
v___x_2904_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2900_, v_i_2901_, v_stop_2902_, v_b_2903_);
return v___x_2904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2905_, lean_object* v_as_2906_, lean_object* v_i_2907_, lean_object* v_stop_2908_, lean_object* v_b_2909_){
_start:
{
size_t v_i_boxed_2910_; size_t v_stop_boxed_2911_; lean_object* v_res_2912_; 
v_i_boxed_2910_ = lean_unbox_usize(v_i_2907_);
lean_dec(v_i_2907_);
v_stop_boxed_2911_ = lean_unbox_usize(v_stop_2908_);
lean_dec(v_stop_2908_);
v_res_2912_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(v_00_u03b1_2905_, v_as_2906_, v_i_boxed_2910_, v_stop_boxed_2911_, v_b_2909_);
lean_dec_ref(v_as_2906_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(lean_object* v_as_2913_, size_t v_i_2914_, size_t v_stop_2915_, lean_object* v_b_2916_){
_start:
{
uint8_t v___x_2917_; 
v___x_2917_ = lean_usize_dec_eq(v_i_2914_, v_stop_2915_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; size_t v___x_2920_; size_t v___x_2921_; 
v___x_2918_ = lean_array_uget_borrowed(v_as_2913_, v_i_2914_);
lean_inc(v___x_2918_);
v___x_2919_ = l_Lake_Job_mix___redArg(v_b_2916_, v___x_2918_);
v___x_2920_ = ((size_t)1ULL);
v___x_2921_ = lean_usize_add(v_i_2914_, v___x_2920_);
v_i_2914_ = v___x_2921_;
v_b_2916_ = v___x_2919_;
goto _start;
}
else
{
return v_b_2916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg___boxed(lean_object* v_as_2923_, lean_object* v_i_2924_, lean_object* v_stop_2925_, lean_object* v_b_2926_){
_start:
{
size_t v_i_boxed_2927_; size_t v_stop_boxed_2928_; lean_object* v_res_2929_; 
v_i_boxed_2927_ = lean_unbox_usize(v_i_2924_);
lean_dec(v_i_2924_);
v_stop_boxed_2928_ = lean_unbox_usize(v_stop_2925_);
lean_dec(v_stop_2925_);
v_res_2929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2923_, v_i_boxed_2927_, v_stop_boxed_2928_, v_b_2926_);
lean_dec_ref(v_as_2923_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object* v_jobs_2930_, lean_object* v_traceCaption_2931_){
_start:
{
lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; uint8_t v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2932_ = lean_box(0);
v___x_2933_ = lean_box(0);
v___x_2934_ = lean_unsigned_to_nat(0u);
v___x_2935_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2936_ = 0;
v___x_2937_ = 0;
v___x_2938_ = l_Lake_BuildTrace_nil(v_traceCaption_2931_);
v___x_2939_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2939_, 0, v___x_2935_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
lean_ctor_set(v___x_2939_, 2, v___x_2934_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*3, v___x_2936_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*3 + 1, v___x_2937_);
lean_ctor_set_uint8(v___x_2939_, sizeof(void*)*3 + 2, v___x_2937_);
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2932_);
lean_ctor_set(v___x_2940_, 1, v___x_2939_);
v___x_2941_ = lean_task_pure(v___x_2940_);
v___x_2942_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2943_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2943_, 0, v___x_2941_);
lean_ctor_set(v___x_2943_, 1, v___x_2933_);
lean_ctor_set(v___x_2943_, 2, v___x_2942_);
lean_ctor_set_uint8(v___x_2943_, sizeof(void*)*3, v___x_2937_);
v___x_2944_ = lean_array_get_size(v_jobs_2930_);
v___x_2945_ = lean_nat_dec_lt(v___x_2934_, v___x_2944_);
if (v___x_2945_ == 0)
{
return v___x_2943_;
}
else
{
size_t v___x_2946_; size_t v___x_2947_; lean_object* v___x_2948_; 
v___x_2946_ = ((size_t)0ULL);
v___x_2947_ = lean_usize_of_nat(v___x_2944_);
v___x_2948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2930_, v___x_2946_, v___x_2947_, v___x_2943_);
return v___x_2948_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object* v_jobs_2949_, lean_object* v_traceCaption_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lake_Job_mixArray___redArg(v_jobs_2949_, v_traceCaption_2950_);
lean_dec_ref(v_jobs_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object* v_00_u03b1_2952_, lean_object* v_jobs_2953_, lean_object* v_traceCaption_2954_){
_start:
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lake_Job_mixArray___redArg(v_jobs_2953_, v_traceCaption_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object* v_00_u03b1_2956_, lean_object* v_jobs_2957_, lean_object* v_traceCaption_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lake_Job_mixArray(v_00_u03b1_2956_, v_jobs_2957_, v_traceCaption_2958_);
lean_dec_ref(v_jobs_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_object* v_00_u03b1_2960_, lean_object* v_as_2961_, size_t v_i_2962_, size_t v_stop_2963_, lean_object* v_b_2964_){
_start:
{
lean_object* v___x_2965_; 
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2961_, v_i_2962_, v_stop_2963_, v_b_2964_);
return v___x_2965_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(lean_object* v_00_u03b1_2966_, lean_object* v_as_2967_, lean_object* v_i_2968_, lean_object* v_stop_2969_, lean_object* v_b_2970_){
_start:
{
size_t v_i_boxed_2971_; size_t v_stop_boxed_2972_; lean_object* v_res_2973_; 
v_i_boxed_2971_ = lean_unbox_usize(v_i_2968_);
lean_dec(v_i_2968_);
v_stop_boxed_2972_ = lean_unbox_usize(v_stop_2969_);
lean_dec(v_stop_2969_);
v_res_2973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(v_00_u03b1_2966_, v_as_2967_, v_i_boxed_2971_, v_stop_boxed_2972_, v_b_2970_);
lean_dec_ref(v_as_2967_);
return v_res_2973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object* v___x_2974_, lean_object* v_rx_2975_, lean_object* v_ry_2976_){
_start:
{
lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2983_; lean_object* v___y_2984_; 
if (lean_obj_tag(v_rx_2975_) == 0)
{
if (lean_obj_tag(v_ry_2976_) == 0)
{
lean_object* v_a_2986_; lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3004_; 
lean_dec(v___x_2974_);
v_a_2986_ = lean_ctor_get(v_rx_2975_, 0);
v_a_2987_ = lean_ctor_get(v_rx_2975_, 1);
v_isSharedCheck_3004_ = !lean_is_exclusive(v_rx_2975_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2989_ = v_rx_2975_;
v_isShared_2990_ = v_isSharedCheck_3004_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_inc(v_a_2986_);
lean_dec(v_rx_2975_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3004_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v_a_2991_; lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3003_; 
v_a_2991_ = lean_ctor_get(v_ry_2976_, 0);
v_a_2992_ = lean_ctor_get(v_ry_2976_, 1);
v_isSharedCheck_3003_ = !lean_is_exclusive(v_ry_2976_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2994_ = v_ry_2976_;
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_inc(v_a_2991_);
lean_dec(v_ry_2976_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3003_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2990_ == 0)
{
lean_ctor_set_tag(v___x_2989_, 1);
lean_ctor_set(v___x_2989_, 1, v_a_2991_);
v___x_2997_ = v___x_2989_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2986_);
lean_ctor_set(v_reuseFailAlloc_3002_, 1, v_a_2991_);
v___x_2997_ = v_reuseFailAlloc_3002_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_3000_; 
v___x_2998_ = l_Lake_JobState_merge(v_a_2987_, v_a_2992_);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 1, v___x_2998_);
lean_ctor_set(v___x_2994_, 0, v___x_2997_);
v___x_3000_ = v___x_2994_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3001_, 1, v___x_2998_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
}
else
{
lean_object* v_a_3005_; 
v_a_3005_ = lean_ctor_get(v_rx_2975_, 1);
lean_inc(v_a_3005_);
lean_dec_ref_known(v_rx_2975_, 2);
v___y_2983_ = v_ry_2976_;
v___y_2984_ = v_a_3005_;
goto v___jp_2982_;
}
}
else
{
lean_object* v_a_3006_; 
v_a_3006_ = lean_ctor_get(v_rx_2975_, 1);
lean_inc(v_a_3006_);
lean_dec_ref(v_rx_2975_);
v___y_2983_ = v_ry_2976_;
v___y_2984_ = v_a_3006_;
goto v___jp_2982_;
}
v___jp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2980_ = l_Lake_JobState_merge(v___y_2978_, v___y_2979_);
v___x_2981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2981_, 0, v___x_2974_);
lean_ctor_set(v___x_2981_, 1, v___x_2980_);
return v___x_2981_;
}
v___jp_2982_:
{
lean_object* v_a_2985_; 
v_a_2985_ = lean_ctor_get(v___y_2983_, 1);
lean_inc(v_a_2985_);
lean_dec_ref(v___y_2983_);
v___y_2978_ = v___y_2984_;
v___y_2979_ = v_a_2985_;
goto v___jp_2977_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object* v_b_3007_, lean_object* v___x_3008_, uint8_t v___x_3009_, lean_object* v_rx_3010_){
_start:
{
lean_object* v_task_3011_; lean_object* v___f_3012_; lean_object* v___x_3013_; 
v_task_3011_ = lean_ctor_get(v_b_3007_, 0);
lean_inc_ref(v_task_3011_);
lean_dec_ref(v_b_3007_);
lean_inc(v___x_3008_);
v___f_3012_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3012_, 0, v___x_3008_);
lean_closure_set(v___f_3012_, 1, v_rx_3010_);
v___x_3013_ = lean_task_map(v___f_3012_, v_task_3011_, v___x_3008_, v___x_3009_);
return v___x_3013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_b_3014_, lean_object* v___x_3015_, lean_object* v___x_3016_, lean_object* v_rx_3017_){
_start:
{
uint8_t v___x_480__boxed_3018_; lean_object* v_res_3019_; 
v___x_480__boxed_3018_ = lean_unbox(v___x_3016_);
v_res_3019_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_3014_, v___x_3015_, v___x_480__boxed_3018_, v_rx_3017_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(lean_object* v_as_3020_, size_t v_i_3021_, size_t v_stop_3022_, lean_object* v_b_3023_){
_start:
{
uint8_t v___x_3024_; 
v___x_3024_ = lean_usize_dec_eq(v_i_3021_, v_stop_3022_);
if (v___x_3024_ == 0)
{
size_t v___x_3025_; size_t v___x_3026_; lean_object* v___x_3027_; lean_object* v_task_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3043_; 
v___x_3025_ = ((size_t)1ULL);
v___x_3026_ = lean_usize_sub(v_i_3021_, v___x_3025_);
v___x_3027_ = lean_array_uget(v_as_3020_, v___x_3026_);
v_task_3028_ = lean_ctor_get(v___x_3027_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3027_);
if (v_isSharedCheck_3043_ == 0)
{
lean_object* v_unused_3044_; lean_object* v_unused_3045_; 
v_unused_3044_ = lean_ctor_get(v___x_3027_, 2);
lean_dec(v_unused_3044_);
v_unused_3045_ = lean_ctor_get(v___x_3027_, 1);
lean_dec(v_unused_3045_);
v___x_3030_ = v___x_3027_;
v_isShared_3031_ = v_isSharedCheck_3043_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_task_3028_);
lean_dec(v___x_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3043_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; uint8_t v___x_3034_; lean_object* v___x_3035_; lean_object* v___f_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3040_; 
v___x_3032_ = lean_box(0);
v___x_3033_ = lean_unsigned_to_nat(0u);
v___x_3034_ = 1;
v___x_3035_ = lean_box(v___x_3034_);
v___f_3036_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3036_, 0, v_b_3023_);
lean_closure_set(v___f_3036_, 1, v___x_3033_);
lean_closure_set(v___f_3036_, 2, v___x_3035_);
v___x_3037_ = lean_task_bind(v_task_3028_, v___f_3036_, v___x_3033_, v___x_3034_);
v___x_3038_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_3031_ == 0)
{
lean_ctor_set(v___x_3030_, 2, v___x_3038_);
lean_ctor_set(v___x_3030_, 1, v___x_3032_);
lean_ctor_set(v___x_3030_, 0, v___x_3037_);
v___x_3040_ = v___x_3030_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3037_);
lean_ctor_set(v_reuseFailAlloc_3042_, 1, v___x_3032_);
lean_ctor_set(v_reuseFailAlloc_3042_, 2, v___x_3038_);
v___x_3040_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
lean_ctor_set_uint8(v___x_3040_, sizeof(void*)*3, v___x_3024_);
v_i_3021_ = v___x_3026_;
v_b_3023_ = v___x_3040_;
goto _start;
}
}
}
else
{
return v_b_3023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object* v_as_3046_, lean_object* v_i_3047_, lean_object* v_stop_3048_, lean_object* v_b_3049_){
_start:
{
size_t v_i_boxed_3050_; size_t v_stop_boxed_3051_; lean_object* v_res_3052_; 
v_i_boxed_3050_ = lean_unbox_usize(v_i_3047_);
lean_dec(v_i_3047_);
v_stop_boxed_3051_ = lean_unbox_usize(v_stop_3048_);
lean_dec(v_stop_3048_);
v_res_3052_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_3046_, v_i_boxed_3050_, v_stop_boxed_3051_, v_b_3049_);
lean_dec_ref(v_as_3046_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(lean_object* v_init_3053_, lean_object* v_l_3054_){
_start:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; uint8_t v___x_3058_; 
v___x_3055_ = lean_array_mk(v_l_3054_);
v___x_3056_ = lean_array_get_size(v___x_3055_);
v___x_3057_ = lean_unsigned_to_nat(0u);
v___x_3058_ = lean_nat_dec_lt(v___x_3057_, v___x_3056_);
if (v___x_3058_ == 0)
{
lean_dec_ref(v___x_3055_);
return v_init_3053_;
}
else
{
size_t v___x_3059_; size_t v___x_3060_; lean_object* v___x_3061_; 
v___x_3059_ = lean_usize_of_nat(v___x_3056_);
v___x_3060_ = ((size_t)0ULL);
v___x_3061_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v___x_3055_, v___x_3059_, v___x_3060_, v_init_3053_);
lean_dec_ref(v___x_3055_);
return v___x_3061_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object* v_jobs_3062_, lean_object* v_traceCaption_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; uint8_t v___x_3068_; uint8_t v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3064_ = lean_box(0);
v___x_3065_ = lean_box(0);
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3068_ = 0;
v___x_3069_ = 0;
v___x_3070_ = l_Lake_BuildTrace_nil(v_traceCaption_3063_);
v___x_3071_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3071_, 0, v___x_3067_);
lean_ctor_set(v___x_3071_, 1, v___x_3070_);
lean_ctor_set(v___x_3071_, 2, v___x_3066_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*3, v___x_3068_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*3 + 1, v___x_3069_);
lean_ctor_set_uint8(v___x_3071_, sizeof(void*)*3 + 2, v___x_3069_);
v___x_3072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3064_);
lean_ctor_set(v___x_3072_, 1, v___x_3071_);
v___x_3073_ = lean_task_pure(v___x_3072_);
v___x_3074_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3075_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3075_, 0, v___x_3073_);
lean_ctor_set(v___x_3075_, 1, v___x_3065_);
lean_ctor_set(v___x_3075_, 2, v___x_3074_);
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*3, v___x_3069_);
v___x_3076_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v___x_3075_, v_jobs_3062_);
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object* v_00_u03b1_3077_, lean_object* v_jobs_3078_, lean_object* v_traceCaption_3079_){
_start:
{
lean_object* v___x_3080_; 
v___x_3080_ = l_Lake_Job_collectList___redArg(v_jobs_3078_, v_traceCaption_3079_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0(lean_object* v_00_u03b1_3081_, lean_object* v_init_3082_, lean_object* v_l_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v_init_3082_, v_l_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_object* v_00_u03b1_3085_, lean_object* v_as_3086_, size_t v_i_3087_, size_t v_stop_3088_, lean_object* v_b_3089_){
_start:
{
lean_object* v___x_3090_; 
v___x_3090_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_3086_, v_i_3087_, v_stop_3088_, v_b_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3091_, lean_object* v_as_3092_, lean_object* v_i_3093_, lean_object* v_stop_3094_, lean_object* v_b_3095_){
_start:
{
size_t v_i_boxed_3096_; size_t v_stop_boxed_3097_; lean_object* v_res_3098_; 
v_i_boxed_3096_ = lean_unbox_usize(v_i_3093_);
lean_dec(v_i_3093_);
v_stop_boxed_3097_ = lean_unbox_usize(v_stop_3094_);
lean_dec(v_stop_3094_);
v_res_3098_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(v_00_u03b1_3091_, v_as_3092_, v_i_boxed_3096_, v_stop_boxed_3097_, v_b_3095_);
lean_dec_ref(v_as_3092_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object* v___x_3099_, lean_object* v_rx_3100_, lean_object* v_ry_3101_){
_start:
{
lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3108_; lean_object* v___y_3109_; 
if (lean_obj_tag(v_rx_3100_) == 0)
{
if (lean_obj_tag(v_ry_3101_) == 0)
{
lean_object* v_a_3111_; lean_object* v_a_3112_; lean_object* v_a_3113_; lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v___x_3099_);
v_a_3111_ = lean_ctor_get(v_rx_3100_, 0);
lean_inc(v_a_3111_);
v_a_3112_ = lean_ctor_get(v_rx_3100_, 1);
lean_inc(v_a_3112_);
lean_dec_ref_known(v_rx_3100_, 2);
v_a_3113_ = lean_ctor_get(v_ry_3101_, 0);
v_a_3114_ = lean_ctor_get(v_ry_3101_, 1);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_ry_3101_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3116_ = v_ry_3101_;
v_isShared_3117_ = v_isSharedCheck_3123_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_inc(v_a_3113_);
lean_dec(v_ry_3101_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3123_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3118_ = lean_array_push(v_a_3111_, v_a_3113_);
v___x_3119_ = l_Lake_JobState_merge(v_a_3112_, v_a_3114_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 1, v___x_3119_);
lean_ctor_set(v___x_3116_, 0, v___x_3118_);
v___x_3121_ = v___x_3116_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v___x_3119_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
else
{
lean_object* v_a_3124_; 
v_a_3124_ = lean_ctor_get(v_rx_3100_, 1);
lean_inc(v_a_3124_);
lean_dec_ref_known(v_rx_3100_, 2);
v___y_3108_ = v_ry_3101_;
v___y_3109_ = v_a_3124_;
goto v___jp_3107_;
}
}
else
{
lean_object* v_a_3125_; 
v_a_3125_ = lean_ctor_get(v_rx_3100_, 1);
lean_inc(v_a_3125_);
lean_dec_ref(v_rx_3100_);
v___y_3108_ = v_ry_3101_;
v___y_3109_ = v_a_3125_;
goto v___jp_3107_;
}
v___jp_3102_:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = l_Lake_JobState_merge(v___y_3103_, v___y_3104_);
v___x_3106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3106_, 0, v___x_3099_);
lean_ctor_set(v___x_3106_, 1, v___x_3105_);
return v___x_3106_;
}
v___jp_3107_:
{
lean_object* v_a_3110_; 
v_a_3110_ = lean_ctor_get(v___y_3108_, 1);
lean_inc(v_a_3110_);
lean_dec_ref(v___y_3108_);
v___y_3103_ = v___y_3109_;
v___y_3104_ = v_a_3110_;
goto v___jp_3102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object* v___x_3126_, lean_object* v___x_3127_, uint8_t v___x_3128_, lean_object* v_rx_3129_){
_start:
{
lean_object* v_task_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; 
v_task_3130_ = lean_ctor_get(v___x_3126_, 0);
lean_inc_ref(v_task_3130_);
lean_dec_ref(v___x_3126_);
lean_inc(v___x_3127_);
v___f_3131_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3131_, 0, v___x_3127_);
lean_closure_set(v___f_3131_, 1, v_rx_3129_);
v___x_3132_ = lean_task_map(v___f_3131_, v_task_3130_, v___x_3127_, v___x_3128_);
return v___x_3132_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object* v___x_3133_, lean_object* v___x_3134_, lean_object* v___x_3135_, lean_object* v_rx_3136_){
_start:
{
uint8_t v___x_413__boxed_3137_; lean_object* v_res_3138_; 
v___x_413__boxed_3137_ = lean_unbox(v___x_3135_);
v_res_3138_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_3133_, v___x_3134_, v___x_413__boxed_3137_, v_rx_3136_);
return v_res_3138_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(lean_object* v_as_3139_, size_t v_i_3140_, size_t v_stop_3141_, lean_object* v_b_3142_){
_start:
{
uint8_t v___x_3143_; 
v___x_3143_ = lean_usize_dec_eq(v_i_3140_, v_stop_3141_);
if (v___x_3143_ == 0)
{
lean_object* v_task_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3162_; 
v_task_3144_ = lean_ctor_get(v_b_3142_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v_b_3142_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; lean_object* v_unused_3164_; 
v_unused_3163_ = lean_ctor_get(v_b_3142_, 2);
lean_dec(v_unused_3163_);
v_unused_3164_ = lean_ctor_get(v_b_3142_, 1);
lean_dec(v_unused_3164_);
v___x_3146_ = v_b_3142_;
v_isShared_3147_ = v_isSharedCheck_3162_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_task_3144_);
lean_dec(v_b_3142_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3162_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; lean_object* v___x_3152_; lean_object* v___f_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3157_; 
v___x_3148_ = lean_box(0);
v___x_3149_ = lean_array_uget_borrowed(v_as_3139_, v_i_3140_);
v___x_3150_ = lean_unsigned_to_nat(0u);
v___x_3151_ = 1;
v___x_3152_ = lean_box(v___x_3151_);
lean_inc(v___x_3149_);
v___f_3153_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3153_, 0, v___x_3149_);
lean_closure_set(v___f_3153_, 1, v___x_3150_);
lean_closure_set(v___f_3153_, 2, v___x_3152_);
v___x_3154_ = lean_task_bind(v_task_3144_, v___f_3153_, v___x_3150_, v___x_3151_);
v___x_3155_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_3147_ == 0)
{
lean_ctor_set(v___x_3146_, 2, v___x_3155_);
lean_ctor_set(v___x_3146_, 1, v___x_3148_);
lean_ctor_set(v___x_3146_, 0, v___x_3154_);
v___x_3157_ = v___x_3146_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3154_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v___x_3148_);
lean_ctor_set(v_reuseFailAlloc_3161_, 2, v___x_3155_);
v___x_3157_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
size_t v___x_3158_; size_t v___x_3159_; 
lean_ctor_set_uint8(v___x_3157_, sizeof(void*)*3, v___x_3143_);
v___x_3158_ = ((size_t)1ULL);
v___x_3159_ = lean_usize_add(v_i_3140_, v___x_3158_);
v_i_3140_ = v___x_3159_;
v_b_3142_ = v___x_3157_;
goto _start;
}
}
}
else
{
return v_b_3142_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(lean_object* v_as_3165_, lean_object* v_i_3166_, lean_object* v_stop_3167_, lean_object* v_b_3168_){
_start:
{
size_t v_i_boxed_3169_; size_t v_stop_boxed_3170_; lean_object* v_res_3171_; 
v_i_boxed_3169_ = lean_unbox_usize(v_i_3166_);
lean_dec(v_i_3166_);
v_stop_boxed_3170_ = lean_unbox_usize(v_stop_3167_);
lean_dec(v_stop_3167_);
v_res_3171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3165_, v_i_boxed_3169_, v_stop_boxed_3170_, v_b_3168_);
lean_dec_ref(v_as_3165_);
return v_res_3171_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object* v_jobs_3172_, lean_object* v_traceCaption_3173_){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; uint8_t v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; uint8_t v___x_3187_; 
v___x_3174_ = lean_array_get_size(v_jobs_3172_);
v___x_3175_ = lean_mk_empty_array_with_capacity(v___x_3174_);
v___x_3176_ = lean_box(0);
v___x_3177_ = lean_unsigned_to_nat(0u);
v___x_3178_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3179_ = 0;
v___x_3180_ = 0;
v___x_3181_ = l_Lake_BuildTrace_nil(v_traceCaption_3173_);
v___x_3182_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3182_, 0, v___x_3178_);
lean_ctor_set(v___x_3182_, 1, v___x_3181_);
lean_ctor_set(v___x_3182_, 2, v___x_3177_);
lean_ctor_set_uint8(v___x_3182_, sizeof(void*)*3, v___x_3179_);
lean_ctor_set_uint8(v___x_3182_, sizeof(void*)*3 + 1, v___x_3180_);
lean_ctor_set_uint8(v___x_3182_, sizeof(void*)*3 + 2, v___x_3180_);
v___x_3183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3183_, 0, v___x_3175_);
lean_ctor_set(v___x_3183_, 1, v___x_3182_);
v___x_3184_ = lean_task_pure(v___x_3183_);
v___x_3185_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3186_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3186_, 0, v___x_3184_);
lean_ctor_set(v___x_3186_, 1, v___x_3176_);
lean_ctor_set(v___x_3186_, 2, v___x_3185_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*3, v___x_3180_);
v___x_3187_ = lean_nat_dec_lt(v___x_3177_, v___x_3174_);
if (v___x_3187_ == 0)
{
return v___x_3186_;
}
else
{
size_t v___x_3188_; size_t v___x_3189_; lean_object* v___x_3190_; 
v___x_3188_ = ((size_t)0ULL);
v___x_3189_ = lean_usize_of_nat(v___x_3174_);
v___x_3190_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_3172_, v___x_3188_, v___x_3189_, v___x_3186_);
return v___x_3190_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object* v_jobs_3191_, lean_object* v_traceCaption_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_Lake_Job_collectArray___redArg(v_jobs_3191_, v_traceCaption_3192_);
lean_dec_ref(v_jobs_3191_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object* v_00_u03b1_3194_, lean_object* v_jobs_3195_, lean_object* v_traceCaption_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Lake_Job_collectArray___redArg(v_jobs_3195_, v_traceCaption_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object* v_00_u03b1_3198_, lean_object* v_jobs_3199_, lean_object* v_traceCaption_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lake_Job_collectArray(v_00_u03b1_3198_, v_jobs_3199_, v_traceCaption_3200_);
lean_dec_ref(v_jobs_3199_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_object* v_00_u03b1_3202_, lean_object* v_as_3203_, size_t v_i_3204_, size_t v_stop_3205_, lean_object* v_b_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3203_, v_i_3204_, v_stop_3205_, v_b_3206_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(lean_object* v_00_u03b1_3208_, lean_object* v_as_3209_, lean_object* v_i_3210_, lean_object* v_stop_3211_, lean_object* v_b_3212_){
_start:
{
size_t v_i_boxed_3213_; size_t v_stop_boxed_3214_; lean_object* v_res_3215_; 
v_i_boxed_3213_ = lean_unbox_usize(v_i_3210_);
lean_dec(v_i_3210_);
v_stop_boxed_3214_ = lean_unbox_usize(v_stop_3211_);
lean_dec(v_stop_3211_);
v_res_3215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(v_00_u03b1_3208_, v_as_3209_, v_i_boxed_3213_, v_stop_boxed_3214_, v_b_3212_);
lean_dec_ref(v_as_3209_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg(){
_start:
{
lean_object* v___x_3217_; 
v___x_3217_ = lean_box(0);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg___boxed(lean_object* v___dummy_3218_){
_start:
{
lean_object* v_res_3219_; 
v_res_3219_ = l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg();
return v_res_3219_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(lean_object* v_00_u03b1_3220_, lean_object* v_inst_3221_){
_start:
{
lean_object* v___x_3222_; 
v___x_3222_ = lean_box(0);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0(lean_object* v___x_3223_, lean_object* v_rx_3224_, lean_object* v_i_3225_, lean_object* v_ry_3226_){
_start:
{
lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3233_; lean_object* v___y_3234_; 
if (lean_obj_tag(v_rx_3224_) == 0)
{
if (lean_obj_tag(v_ry_3226_) == 0)
{
lean_object* v_a_3236_; lean_object* v_a_3237_; lean_object* v_a_3238_; lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3248_; 
lean_dec(v___x_3223_);
v_a_3236_ = lean_ctor_get(v_rx_3224_, 0);
lean_inc(v_a_3236_);
v_a_3237_ = lean_ctor_get(v_rx_3224_, 1);
lean_inc(v_a_3237_);
lean_dec_ref_known(v_rx_3224_, 2);
v_a_3238_ = lean_ctor_get(v_ry_3226_, 0);
v_a_3239_ = lean_ctor_get(v_ry_3226_, 1);
v_isSharedCheck_3248_ = !lean_is_exclusive(v_ry_3226_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3241_ = v_ry_3226_;
v_isShared_3242_ = v_isSharedCheck_3248_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_inc(v_a_3238_);
lean_dec(v_ry_3226_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3248_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3243_ = lean_array_fset(v_a_3236_, v_i_3225_, v_a_3238_);
v___x_3244_ = l_Lake_JobState_merge(v_a_3237_, v_a_3239_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 1, v___x_3244_);
lean_ctor_set(v___x_3241_, 0, v___x_3243_);
v___x_3246_ = v___x_3241_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3247_, 1, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
else
{
lean_object* v_a_3249_; 
v_a_3249_ = lean_ctor_get(v_rx_3224_, 1);
lean_inc(v_a_3249_);
lean_dec_ref_known(v_rx_3224_, 2);
v___y_3233_ = v_ry_3226_;
v___y_3234_ = v_a_3249_;
goto v___jp_3232_;
}
}
else
{
lean_object* v_a_3250_; 
v_a_3250_ = lean_ctor_get(v_rx_3224_, 1);
lean_inc(v_a_3250_);
lean_dec_ref(v_rx_3224_);
v___y_3233_ = v_ry_3226_;
v___y_3234_ = v_a_3250_;
goto v___jp_3232_;
}
v___jp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; 
v___x_3230_ = l_Lake_JobState_merge(v___y_3228_, v___y_3229_);
v___x_3231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3223_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
return v___x_3231_;
}
v___jp_3232_:
{
lean_object* v_a_3235_; 
v_a_3235_ = lean_ctor_get(v___y_3233_, 1);
lean_inc(v_a_3235_);
lean_dec_ref(v___y_3233_);
v___y_3228_ = v___y_3234_;
v___y_3229_ = v_a_3235_;
goto v___jp_3227_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0___boxed(lean_object* v___x_3251_, lean_object* v_rx_3252_, lean_object* v_i_3253_, lean_object* v_ry_3254_){
_start:
{
lean_object* v_res_3255_; 
v_res_3255_ = l_Lake_Job_collectVector___redArg___lam__0(v___x_3251_, v_rx_3252_, v_i_3253_, v_ry_3254_);
lean_dec(v_i_3253_);
return v_res_3255_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1(lean_object* v___x_3256_, lean_object* v___x_3257_, lean_object* v_i_3258_, uint8_t v___x_3259_, lean_object* v_rx_3260_){
_start:
{
lean_object* v_task_3261_; lean_object* v___f_3262_; lean_object* v___x_3263_; 
v_task_3261_ = lean_ctor_get(v___x_3256_, 0);
lean_inc_ref(v_task_3261_);
lean_dec_ref(v___x_3256_);
lean_inc(v___x_3257_);
v___f_3262_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3262_, 0, v___x_3257_);
lean_closure_set(v___f_3262_, 1, v_rx_3260_);
lean_closure_set(v___f_3262_, 2, v_i_3258_);
v___x_3263_ = lean_task_map(v___f_3262_, v_task_3261_, v___x_3257_, v___x_3259_);
return v___x_3263_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1___boxed(lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v_i_3266_, lean_object* v___x_3267_, lean_object* v_rx_3268_){
_start:
{
uint8_t v___x_191__boxed_3269_; lean_object* v_res_3270_; 
v___x_191__boxed_3269_ = lean_unbox(v___x_3267_);
v_res_3270_ = l_Lake_Job_collectVector___redArg___lam__1(v___x_3264_, v___x_3265_, v_i_3266_, v___x_191__boxed_3269_, v_rx_3268_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2(lean_object* v_jobs_3271_, lean_object* v___x_3272_, lean_object* v_i_3273_, lean_object* v_h_3274_, lean_object* v_job_3275_){
_start:
{
lean_object* v_task_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3291_; 
v_task_3276_ = lean_ctor_get(v_job_3275_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v_job_3275_);
if (v_isSharedCheck_3291_ == 0)
{
lean_object* v_unused_3292_; lean_object* v_unused_3293_; 
v_unused_3292_ = lean_ctor_get(v_job_3275_, 2);
lean_dec(v_unused_3292_);
v_unused_3293_ = lean_ctor_get(v_job_3275_, 1);
lean_dec(v_unused_3293_);
v___x_3278_ = v_job_3275_;
v_isShared_3279_ = v_isSharedCheck_3291_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_task_3276_);
lean_dec(v_job_3275_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3291_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; uint8_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___f_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; lean_object* v___x_3289_; 
v___x_3280_ = lean_array_fget_borrowed(v_jobs_3271_, v_i_3273_);
v___x_3281_ = lean_unsigned_to_nat(0u);
v___x_3282_ = 1;
v___x_3283_ = lean_box(v___x_3282_);
lean_inc(v___x_3280_);
v___f_3284_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3284_, 0, v___x_3280_);
lean_closure_set(v___f_3284_, 1, v___x_3281_);
lean_closure_set(v___f_3284_, 2, v_i_3273_);
lean_closure_set(v___f_3284_, 3, v___x_3283_);
v___x_3285_ = lean_task_bind(v_task_3276_, v___f_3284_, v___x_3281_, v___x_3282_);
v___x_3286_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3287_ = 0;
if (v_isShared_3279_ == 0)
{
lean_ctor_set(v___x_3278_, 2, v___x_3286_);
lean_ctor_set(v___x_3278_, 1, v___x_3272_);
lean_ctor_set(v___x_3278_, 0, v___x_3285_);
v___x_3289_ = v___x_3278_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3285_);
lean_ctor_set(v_reuseFailAlloc_3290_, 1, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3290_, 2, v___x_3286_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
lean_ctor_set_uint8(v___x_3289_, sizeof(void*)*3, v___x_3287_);
return v___x_3289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2___boxed(lean_object* v_jobs_3294_, lean_object* v___x_3295_, lean_object* v_i_3296_, lean_object* v_h_3297_, lean_object* v_job_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l_Lake_Job_collectVector___redArg___lam__2(v_jobs_3294_, v___x_3295_, v_i_3296_, v_h_3297_, v_job_3298_);
lean_dec_ref(v_jobs_3294_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg(lean_object* v_n_3300_, lean_object* v_jobs_3301_, lean_object* v_traceCaption_3302_){
_start:
{
lean_object* v_placeholder_3303_; lean_object* v___x_3304_; lean_object* v___f_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; uint8_t v___x_3309_; uint8_t v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_placeholder_3303_ = lean_box(0);
v___x_3304_ = lean_box(0);
v___f_3305_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3305_, 0, v_jobs_3301_);
lean_closure_set(v___f_3305_, 1, v___x_3304_);
lean_inc_n(v_n_3300_, 2);
v___x_3306_ = lean_mk_array(v_n_3300_, v_placeholder_3303_);
v___x_3307_ = lean_unsigned_to_nat(0u);
v___x_3308_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3309_ = 0;
v___x_3310_ = 0;
v___x_3311_ = l_Lake_BuildTrace_nil(v_traceCaption_3302_);
v___x_3312_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3312_, 0, v___x_3308_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
lean_ctor_set(v___x_3312_, 2, v___x_3307_);
lean_ctor_set_uint8(v___x_3312_, sizeof(void*)*3, v___x_3309_);
lean_ctor_set_uint8(v___x_3312_, sizeof(void*)*3 + 1, v___x_3310_);
lean_ctor_set_uint8(v___x_3312_, sizeof(void*)*3 + 2, v___x_3310_);
v___x_3313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3306_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_task_pure(v___x_3313_);
v___x_3315_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3316_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3304_);
lean_ctor_set(v___x_3316_, 2, v___x_3315_);
lean_ctor_set_uint8(v___x_3316_, sizeof(void*)*3, v___x_3310_);
v___x_3317_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3300_, v___f_3305_, v_n_3300_, lean_box(0), v___x_3316_);
lean_dec(v_n_3300_);
return v___x_3317_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector(lean_object* v_n_3318_, lean_object* v_00_u03b1_3319_, lean_object* v_inst_3320_, lean_object* v_jobs_3321_, lean_object* v_traceCaption_3322_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Lake_Job_collectVector___redArg(v_n_3318_, v_jobs_3321_, v_traceCaption_3322_);
return v___x_3323_;
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
