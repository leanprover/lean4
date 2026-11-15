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
lean_object* v_a_1764_; lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1792_; 
v_a_1764_ = lean_ctor_get(v___x_1734_, 0);
v_a_1765_ = lean_ctor_get(v___x_1734_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1734_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1767_ = v___x_1734_;
v_isShared_1768_ = v_isSharedCheck_1792_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_inc(v_a_1764_);
lean_dec(v___x_1734_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1792_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_a_1770_; lean_object* v_log_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_log_1774_ = lean_ctor_get(v_a_1765_, 0);
lean_inc_ref(v_log_1774_);
lean_dec(v_a_1765_);
v___x_1775_ = lean_unsigned_to_nat(0u);
v___x_1776_ = lean_array_get_size(v_log_1774_);
v___x_1777_ = lean_nat_dec_lt(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v_log_1774_);
v_a_1770_ = v_a_1731_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1778_; size_t v___x_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
v___x_1778_ = lean_box(0);
v___x_1779_ = ((size_t)0ULL);
v___x_1780_ = lean_usize_of_nat(v___x_1776_);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1774_, v___x_1779_, v___x_1780_, v___x_1778_, v_a_1731_);
lean_dec_ref(v_log_1774_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 1);
lean_inc(v_a_1782_);
lean_dec_ref_known(v___x_1781_, 2);
v_a_1770_ = v_a_1782_;
goto v___jp_1769_;
}
else
{
lean_object* v_a_1783_; lean_object* v_a_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1791_; 
lean_del_object(v___x_1767_);
lean_dec(v_a_1764_);
v_a_1783_ = lean_ctor_get(v___x_1781_, 0);
v_a_1784_ = lean_ctor_get(v___x_1781_, 1);
v_isSharedCheck_1791_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1786_ = v___x_1781_;
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_a_1784_);
lean_inc(v_a_1783_);
lean_dec(v___x_1781_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1791_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v___x_1789_; 
if (v_isShared_1787_ == 0)
{
v___x_1789_ = v___x_1786_;
goto v_reusejp_1788_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1783_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_a_1784_);
v___x_1789_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1788_;
}
v_reusejp_1788_:
{
return v___x_1789_;
}
}
}
}
v___jp_1769_:
{
lean_object* v___x_1772_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 1, v_a_1770_);
v___x_1772_ = v___x_1767_;
goto v_reusejp_1771_;
}
else
{
lean_object* v_reuseFailAlloc_1773_; 
v_reuseFailAlloc_1773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1773_, 0, v_a_1764_);
lean_ctor_set(v_reuseFailAlloc_1773_, 1, v_a_1770_);
v___x_1772_ = v_reuseFailAlloc_1773_;
goto v_reusejp_1771_;
}
v_reusejp_1771_:
{
return v___x_1772_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___boxed(lean_object* v_self_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lake_Job_await___redArg(v_self_1793_, v_a_1794_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await(lean_object* v_00_u03b1_1797_, lean_object* v_self_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = l_Lake_Job_await___redArg(v_self_1798_, v_a_1799_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___boxed(lean_object* v_00_u03b1_1802_, lean_object* v_self_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v_res_1806_; 
v_res_1806_ = l_Lake_Job_await(v_00_u03b1_1802_, v_self_1803_, v_a_1804_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___redArg(lean_object* v_a_1807_){
_start:
{
lean_object* v_log_1809_; uint8_t v_action_1810_; uint8_t v_wantsRebuild_1811_; lean_object* v_trace_1812_; lean_object* v_buildTime_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1823_; 
v_log_1809_ = lean_ctor_get(v_a_1807_, 0);
v_action_1810_ = lean_ctor_get_uint8(v_a_1807_, sizeof(void*)*3);
v_wantsRebuild_1811_ = lean_ctor_get_uint8(v_a_1807_, sizeof(void*)*3 + 1);
v_trace_1812_ = lean_ctor_get(v_a_1807_, 1);
v_buildTime_1813_ = lean_ctor_get(v_a_1807_, 2);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_a_1807_);
if (v_isSharedCheck_1823_ == 0)
{
v___x_1815_ = v_a_1807_;
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_buildTime_1813_);
lean_inc(v_trace_1812_);
lean_inc(v_log_1809_);
lean_dec(v_a_1807_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1823_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
uint8_t v___x_1817_; lean_object* v___x_1819_; 
v___x_1817_ = 1;
lean_inc_ref(v_log_1809_);
if (v_isShared_1816_ == 0)
{
v___x_1819_ = v___x_1815_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_log_1809_);
lean_ctor_set(v_reuseFailAlloc_1822_, 1, v_trace_1812_);
lean_ctor_set(v_reuseFailAlloc_1822_, 2, v_buildTime_1813_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, sizeof(void*)*3, v_action_1810_);
lean_ctor_set_uint8(v_reuseFailAlloc_1822_, sizeof(void*)*3 + 1, v_wantsRebuild_1811_);
v___x_1819_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
lean_ctor_set_uint8(v___x_1819_, sizeof(void*)*3 + 2, v___x_1817_);
v___x_1820_ = lean_array_get_size(v_log_1809_);
lean_dec_ref(v_log_1809_);
v___x_1821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v___x_1819_);
return v___x_1821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___redArg___boxed(lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lake_Job_cancelJob___redArg(v_a_1824_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob(lean_object* v_00_u03b1_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = l_Lake_Job_cancelJob___redArg(v_a_1833_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___boxed(lean_object* v_00_u03b1_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lake_Job_cancelJob(v_00_u03b1_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_, v_a_1842_);
lean_dec_ref(v_a_1841_);
lean_dec_ref(v_a_1840_);
lean_dec(v_a_1839_);
lean_dec(v_a_1838_);
lean_dec_ref(v_a_1837_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___redArg(lean_object* v_self_1845_, lean_object* v_a_1846_){
_start:
{
lean_object* v_task_1848_; lean_object* v___x_1849_; 
v_task_1848_ = lean_ctor_get(v_self_1845_, 0);
lean_inc_ref(v_task_1848_);
lean_dec_ref(v_self_1845_);
v___x_1849_ = lean_io_wait(v_task_1848_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1858_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v___x_1849_, 1);
lean_dec(v_unused_1859_);
v___x_1852_ = v___x_1849_;
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_a_1850_);
lean_dec(v___x_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1858_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
lean_object* v___x_1854_; lean_object* v___x_1856_; 
v___x_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1854_, 0, v_a_1850_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 1, v_a_1846_);
lean_ctor_set(v___x_1852_, 0, v___x_1854_);
v___x_1856_ = v___x_1852_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_a_1846_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1870_; 
v_a_1860_ = lean_ctor_get(v___x_1849_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1870_ == 0)
{
lean_object* v_unused_1871_; 
v_unused_1871_ = lean_ctor_get(v___x_1849_, 0);
lean_dec(v_unused_1871_);
v___x_1862_ = v___x_1849_;
v_isShared_1863_ = v_isSharedCheck_1870_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1849_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1870_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
uint8_t v_canceled_1864_; 
v_canceled_1864_ = lean_ctor_get_uint8(v_a_1860_, sizeof(void*)*3 + 2);
lean_dec(v_a_1860_);
if (v_canceled_1864_ == 0)
{
lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1865_ = lean_box(0);
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 0);
lean_ctor_set(v___x_1862_, 1, v_a_1846_);
lean_ctor_set(v___x_1862_, 0, v___x_1865_);
v___x_1867_ = v___x_1862_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_a_1846_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
return v___x_1867_;
}
}
else
{
lean_object* v___x_1869_; 
lean_del_object(v___x_1862_);
v___x_1869_ = l_Lake_Job_cancelJob___redArg(v_a_1846_);
return v___x_1869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___redArg___boxed(lean_object* v_self_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lake_Job_waitUnlessCanceled_x3f___redArg(v_self_1872_, v_a_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f(lean_object* v_00_u03b1_1876_, lean_object* v_self_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Lake_Job_waitUnlessCanceled_x3f___redArg(v_self_1877_, v_a_1883_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___boxed(lean_object* v_00_u03b1_1886_, lean_object* v_self_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_Lake_Job_waitUnlessCanceled_x3f(v_00_u03b1_1886_, v_self_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_);
lean_dec_ref(v_a_1892_);
lean_dec_ref(v_a_1891_);
lean_dec(v_a_1890_);
lean_dec(v_a_1889_);
lean_dec_ref(v_a_1888_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg(lean_object* v_s_1900_){
_start:
{
lean_object* v_log_1901_; uint8_t v_action_1902_; uint8_t v_wantsRebuild_1903_; lean_object* v_trace_1904_; lean_object* v_buildTime_1905_; lean_object* v___x_1907_; uint8_t v_isShared_1908_; uint8_t v_isSharedCheck_1917_; 
v_log_1901_ = lean_ctor_get(v_s_1900_, 0);
v_action_1902_ = lean_ctor_get_uint8(v_s_1900_, sizeof(void*)*3);
v_wantsRebuild_1903_ = lean_ctor_get_uint8(v_s_1900_, sizeof(void*)*3 + 1);
v_trace_1904_ = lean_ctor_get(v_s_1900_, 1);
v_buildTime_1905_ = lean_ctor_get(v_s_1900_, 2);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_s_1900_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1907_ = v_s_1900_;
v_isShared_1908_ = v_isSharedCheck_1917_;
goto v_resetjp_1906_;
}
else
{
lean_inc(v_buildTime_1905_);
lean_inc(v_trace_1904_);
lean_inc(v_log_1901_);
lean_dec(v_s_1900_);
v___x_1907_ = lean_box(0);
v_isShared_1908_ = v_isSharedCheck_1917_;
goto v_resetjp_1906_;
}
v_resetjp_1906_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; lean_object* v___x_1914_; 
v___x_1909_ = lean_array_get_size(v_log_1901_);
v___x_1910_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_1911_ = lean_array_push(v_log_1901_, v___x_1910_);
v___x_1912_ = 1;
if (v_isShared_1908_ == 0)
{
lean_ctor_set(v___x_1907_, 0, v___x_1911_);
v___x_1914_ = v___x_1907_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1911_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_trace_1904_);
lean_ctor_set(v_reuseFailAlloc_1916_, 2, v_buildTime_1905_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*3, v_action_1902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1916_, sizeof(void*)*3 + 1, v_wantsRebuild_1903_);
v___x_1914_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
lean_object* v___x_1915_; 
lean_ctor_set_uint8(v___x_1914_, sizeof(void*)*3 + 2, v___x_1912_);
v___x_1915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1909_);
lean_ctor_set(v___x_1915_, 1, v___x_1914_);
return v___x_1915_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult(lean_object* v_00_u03b1_1918_, lean_object* v_s_1919_){
_start:
{
lean_object* v_log_1920_; uint8_t v_action_1921_; uint8_t v_wantsRebuild_1922_; lean_object* v_trace_1923_; lean_object* v_buildTime_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1936_; 
v_log_1920_ = lean_ctor_get(v_s_1919_, 0);
v_action_1921_ = lean_ctor_get_uint8(v_s_1919_, sizeof(void*)*3);
v_wantsRebuild_1922_ = lean_ctor_get_uint8(v_s_1919_, sizeof(void*)*3 + 1);
v_trace_1923_ = lean_ctor_get(v_s_1919_, 1);
v_buildTime_1924_ = lean_ctor_get(v_s_1919_, 2);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_s_1919_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1926_ = v_s_1919_;
v_isShared_1927_ = v_isSharedCheck_1936_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_buildTime_1924_);
lean_inc(v_trace_1923_);
lean_inc(v_log_1920_);
lean_dec(v_s_1919_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1936_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; lean_object* v___x_1933_; 
v___x_1928_ = lean_array_get_size(v_log_1920_);
v___x_1929_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_1930_ = lean_array_push(v_log_1920_, v___x_1929_);
v___x_1931_ = 1;
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1930_);
v___x_1933_ = v___x_1926_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_trace_1923_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_buildTime_1924_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*3, v_action_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1935_, sizeof(void*)*3 + 1, v_wantsRebuild_1922_);
v___x_1933_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; 
lean_ctor_set_uint8(v___x_1933_, sizeof(void*)*3 + 2, v___x_1931_);
v___x_1934_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1928_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
return v___x_1934_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1(lean_object* v_a_1937_, lean_object* v_a_1938_, lean_object* v_f_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_x_1944_){
_start:
{
lean_object* v_a_1947_; lean_object* v_a_1948_; lean_object* v___y_1951_; lean_object* v___y_1952_; uint8_t v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; uint8_t v___y_1962_; uint8_t v___y_1963_; lean_object* v___y_1964_; 
if (lean_obj_tag(v_x_1944_) == 0)
{
lean_object* v_a_1976_; lean_object* v_a_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2046_; 
v_a_1976_ = lean_ctor_get(v_x_1944_, 0);
v_a_1977_ = lean_ctor_get(v_x_1944_, 1);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_x_1944_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_1979_ = v_x_1944_;
v_isShared_1980_ = v_isSharedCheck_2046_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_a_1977_);
lean_inc(v_a_1976_);
lean_dec(v_x_1944_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2046_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_cancelTk_x3f_2025_; 
v_cancelTk_x3f_2025_ = lean_ctor_get(v_a_1937_, 6);
if (lean_obj_tag(v_cancelTk_x3f_2025_) == 1)
{
lean_object* v_val_2026_; uint8_t v___x_2027_; 
v_val_2026_ = lean_ctor_get(v_cancelTk_x3f_2025_, 0);
v___x_2027_ = l_IO_CancelToken_isSet(v_val_2026_);
if (v___x_2027_ == 0)
{
lean_del_object(v___x_1979_);
goto v___jp_1981_;
}
else
{
lean_object* v_log_2028_; uint8_t v_action_2029_; uint8_t v_wantsRebuild_2030_; lean_object* v_trace_2031_; lean_object* v_buildTime_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2045_; 
lean_dec(v_a_1976_);
lean_dec_ref(v_a_1940_);
lean_dec_ref(v_f_1939_);
v_log_2028_ = lean_ctor_get(v_a_1977_, 0);
v_action_2029_ = lean_ctor_get_uint8(v_a_1977_, sizeof(void*)*3);
v_wantsRebuild_2030_ = lean_ctor_get_uint8(v_a_1977_, sizeof(void*)*3 + 1);
v_trace_2031_ = lean_ctor_get(v_a_1977_, 1);
v_buildTime_2032_ = lean_ctor_get(v_a_1977_, 2);
v_isSharedCheck_2045_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_2045_ == 0)
{
v___x_2034_ = v_a_1977_;
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_buildTime_2032_);
lean_inc(v_trace_2031_);
lean_inc(v_log_2028_);
lean_dec(v_a_1977_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2045_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2036_ = lean_array_get_size(v_log_2028_);
v___x_2037_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_2038_ = lean_array_push(v_log_2028_, v___x_2037_);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2038_);
v___x_2040_ = v___x_2034_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_trace_2031_);
lean_ctor_set(v_reuseFailAlloc_2044_, 2, v_buildTime_2032_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*3, v_action_2029_);
lean_ctor_set_uint8(v_reuseFailAlloc_2044_, sizeof(void*)*3 + 1, v_wantsRebuild_2030_);
v___x_2040_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
lean_object* v___x_2042_; 
lean_ctor_set_uint8(v___x_2040_, sizeof(void*)*3 + 2, v___x_2027_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set_tag(v___x_1979_, 1);
lean_ctor_set(v___x_1979_, 1, v___x_2040_);
lean_ctor_set(v___x_1979_, 0, v___x_2036_);
v___x_2042_ = v___x_1979_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
}
else
{
lean_del_object(v___x_1979_);
goto v___jp_1981_;
}
v___jp_1981_:
{
lean_object* v_log_1982_; uint8_t v_action_1983_; uint8_t v_wantsRebuild_1984_; uint8_t v_canceled_1985_; lean_object* v_trace_1986_; lean_object* v_buildTime_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2024_; 
v_log_1982_ = lean_ctor_get(v_a_1977_, 0);
v_action_1983_ = lean_ctor_get_uint8(v_a_1977_, sizeof(void*)*3);
v_wantsRebuild_1984_ = lean_ctor_get_uint8(v_a_1977_, sizeof(void*)*3 + 1);
v_canceled_1985_ = lean_ctor_get_uint8(v_a_1977_, sizeof(void*)*3 + 2);
v_trace_1986_ = lean_ctor_get(v_a_1977_, 1);
v_buildTime_1987_ = lean_ctor_get(v_a_1977_, 2);
v_isSharedCheck_2024_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_2024_ == 0)
{
v___x_1989_ = v_a_1977_;
v_isShared_1990_ = v_isSharedCheck_2024_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_buildTime_1987_);
lean_inc(v_trace_1986_);
lean_inc(v_log_1982_);
lean_dec(v_a_1977_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2024_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v_trace_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1999_; 
lean_inc_ref(v_a_1938_);
v_trace_1991_ = l_Lake_BuildTrace_mix(v_a_1938_, v_trace_1986_);
v___x_1992_ = lean_unsigned_to_nat(0u);
v___x_1993_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1994_ = lean_st_mk_ref(v___x_1993_);
lean_inc(v___x_1994_);
v___x_1995_ = l_IO_FS_Stream_ofBuffer(v___x_1994_);
lean_inc_ref(v___x_1995_);
v___x_1996_ = lean_get_set_stdout(v___x_1995_);
v___x_1997_ = lean_get_set_stderr(v___x_1995_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 1, v_trace_1991_);
v___x_1999_ = v___x_1989_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_log_1982_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_trace_1991_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_buildTime_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3, v_action_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3 + 1, v_wantsRebuild_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_2023_, sizeof(void*)*3 + 2, v_canceled_1985_);
v___x_1999_ = v_reuseFailAlloc_2023_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; 
lean_inc_ref(v_a_1937_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc(v_a_1941_);
v___x_2000_ = lean_apply_8(v_f_1939_, v_a_1976_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1937_, v___x_1999_, lean_box(0));
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v_a_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v_a_2005_; lean_object* v_log_2006_; uint8_t v_action_2007_; uint8_t v_wantsRebuild_2008_; uint8_t v_canceled_2009_; lean_object* v_trace_2010_; lean_object* v_buildTime_2011_; lean_object* v___x_2012_; lean_object* v_data_2013_; uint8_t v___x_2014_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc_n(v_a_2001_, 2);
v_a_2002_ = lean_ctor_get(v___x_2000_, 1);
lean_inc(v_a_2002_);
lean_dec_ref_known(v___x_2000_, 2);
v___x_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_a_2001_);
v___x_2004_ = l_Lake_Job_sync___redArg___lam__0(v___x_1996_, v___x_1997_, v___x_2003_, v_a_2002_);
lean_dec_ref_known(v___x_2003_, 1);
v_a_2005_ = lean_ctor_get(v___x_2004_, 1);
lean_inc(v_a_2005_);
lean_dec_ref(v___x_2004_);
v_log_2006_ = lean_ctor_get(v_a_2005_, 0);
lean_inc_ref(v_log_2006_);
v_action_2007_ = lean_ctor_get_uint8(v_a_2005_, sizeof(void*)*3);
v_wantsRebuild_2008_ = lean_ctor_get_uint8(v_a_2005_, sizeof(void*)*3 + 1);
v_canceled_2009_ = lean_ctor_get_uint8(v_a_2005_, sizeof(void*)*3 + 2);
v_trace_2010_ = lean_ctor_get(v_a_2005_, 1);
lean_inc_ref(v_trace_2010_);
v_buildTime_2011_ = lean_ctor_get(v_a_2005_, 2);
lean_inc(v_buildTime_2011_);
v___x_2012_ = lean_st_ref_get(v___x_1994_);
lean_dec(v___x_1994_);
v_data_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc_ref(v_data_2013_);
lean_dec(v___x_2012_);
v___x_2014_ = lean_string_validate_utf8(v_data_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_dec_ref(v_data_2013_);
v___x_2015_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2016_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2015_);
v___y_1955_ = v_canceled_2009_;
v___y_1956_ = v_a_2005_;
v___y_1957_ = v_trace_2010_;
v___y_1958_ = v_a_2001_;
v___y_1959_ = v_log_2006_;
v___y_1960_ = v___x_1992_;
v___y_1961_ = v_buildTime_2011_;
v___y_1962_ = v_action_2007_;
v___y_1963_ = v_wantsRebuild_2008_;
v___y_1964_ = v___x_2016_;
goto v___jp_1954_;
}
else
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_string_from_utf8_unchecked(v_data_2013_);
v___y_1955_ = v_canceled_2009_;
v___y_1956_ = v_a_2005_;
v___y_1957_ = v_trace_2010_;
v___y_1958_ = v_a_2001_;
v___y_1959_ = v_log_2006_;
v___y_1960_ = v___x_1992_;
v___y_1961_ = v_buildTime_2011_;
v___y_1962_ = v_action_2007_;
v___y_1963_ = v_wantsRebuild_2008_;
v___y_1964_ = v___x_2017_;
goto v___jp_1954_;
}
}
else
{
lean_object* v_a_2018_; lean_object* v_a_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v_a_2022_; 
lean_dec(v___x_1994_);
v_a_2018_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2018_);
v_a_2019_ = lean_ctor_get(v___x_2000_, 1);
lean_inc(v_a_2019_);
lean_dec_ref_known(v___x_2000_, 2);
v___x_2020_ = lean_box(0);
v___x_2021_ = l_Lake_Job_sync___redArg___lam__0(v___x_1996_, v___x_1997_, v___x_2020_, v_a_2019_);
v_a_2022_ = lean_ctor_get(v___x_2021_, 1);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_2021_);
v_a_1947_ = v_a_2018_;
v_a_1948_ = v_a_2022_;
goto v___jp_1946_;
}
}
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v_a_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2055_; 
lean_dec_ref(v_a_1940_);
lean_dec_ref(v_f_1939_);
v_a_2047_ = lean_ctor_get(v_x_1944_, 0);
v_a_2048_ = lean_ctor_get(v_x_1944_, 1);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_x_1944_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2050_ = v_x_1944_;
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_a_2048_);
lean_inc(v_a_2047_);
lean_dec(v_x_1944_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2055_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___x_2053_; 
if (v_isShared_2051_ == 0)
{
v___x_2053_ = v___x_2050_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_a_2047_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_a_2048_);
v___x_2053_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
return v___x_2053_;
}
}
}
v___jp_1946_:
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_a_1947_);
lean_ctor_set(v___x_1949_, 1, v_a_1948_);
return v___x_1949_;
}
v___jp_1950_:
{
lean_object* v___x_1953_; 
v___x_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1953_, 0, v___y_1951_);
lean_ctor_set(v___x_1953_, 1, v___y_1952_);
return v___x_1953_;
}
v___jp_1954_:
{
lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = lean_string_utf8_byte_size(v___y_1964_);
v___x_1966_ = lean_nat_dec_eq(v___x_1965_, v___y_1960_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
lean_dec_ref(v___y_1956_);
v___x_1967_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1968_, 0, v___y_1964_);
lean_ctor_set(v___x_1968_, 1, v___y_1960_);
lean_ctor_set(v___x_1968_, 2, v___x_1965_);
v___x_1969_ = l_String_Slice_trimAscii(v___x_1968_);
v___x_1970_ = l_String_Slice_toString(v___x_1969_);
lean_dec_ref(v___x_1969_);
v___x_1971_ = lean_string_append(v___x_1967_, v___x_1970_);
lean_dec_ref(v___x_1970_);
v___x_1972_ = 1;
v___x_1973_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1973_, 0, v___x_1971_);
lean_ctor_set_uint8(v___x_1973_, sizeof(void*)*1, v___x_1972_);
v___x_1974_ = lean_array_push(v___y_1959_, v___x_1973_);
v___x_1975_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
lean_ctor_set(v___x_1975_, 1, v___y_1957_);
lean_ctor_set(v___x_1975_, 2, v___y_1961_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*3, v___y_1962_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*3 + 1, v___y_1963_);
lean_ctor_set_uint8(v___x_1975_, sizeof(void*)*3 + 2, v___y_1955_);
v___y_1951_ = v___y_1958_;
v___y_1952_ = v___x_1975_;
goto v___jp_1950_;
}
else
{
lean_dec_ref(v___y_1964_);
lean_dec(v___y_1961_);
lean_dec(v___y_1960_);
lean_dec_ref(v___y_1959_);
lean_dec_ref(v___y_1957_);
v___y_1951_ = v___y_1958_;
v___y_1952_ = v___y_1956_;
goto v___jp_1950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1___boxed(lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_f_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_x_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lake_Job_mapM___redArg___lam__1(v_a_2056_, v_a_2057_, v_f_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_x_2063_);
lean_dec_ref(v_a_2062_);
lean_dec(v_a_2061_);
lean_dec(v_a_2060_);
lean_dec_ref(v_a_2057_);
lean_dec_ref(v_a_2056_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object* v_kind_2066_, lean_object* v_self_2067_, lean_object* v_f_2068_, lean_object* v_prio_2069_, uint8_t v_sync_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_){
_start:
{
lean_object* v_task_2078_; lean_object* v_caption_2079_; uint8_t v_optional_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2089_; 
v_task_2078_ = lean_ctor_get(v_self_2067_, 0);
v_caption_2079_ = lean_ctor_get(v_self_2067_, 2);
v_optional_2080_ = lean_ctor_get_uint8(v_self_2067_, sizeof(void*)*3);
v_isSharedCheck_2089_ = !lean_is_exclusive(v_self_2067_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; 
v_unused_2090_ = lean_ctor_get(v_self_2067_, 1);
lean_dec(v_unused_2090_);
v___x_2082_ = v_self_2067_;
v_isShared_2083_ = v_isSharedCheck_2089_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_caption_2079_);
lean_inc(v_task_2078_);
lean_dec(v_self_2067_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2089_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v___f_2084_; lean_object* v___x_2085_; lean_object* v___x_2087_; 
lean_inc_ref(v_a_2074_);
lean_inc(v_a_2073_);
lean_inc(v_a_2072_);
lean_inc_ref(v_a_2076_);
lean_inc_ref(v_a_2075_);
v___f_2084_ = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__1___boxed), 9, 7);
lean_closure_set(v___f_2084_, 0, v_a_2075_);
lean_closure_set(v___f_2084_, 1, v_a_2076_);
lean_closure_set(v___f_2084_, 2, v_f_2068_);
lean_closure_set(v___f_2084_, 3, v_a_2071_);
lean_closure_set(v___f_2084_, 4, v_a_2072_);
lean_closure_set(v___f_2084_, 5, v_a_2073_);
lean_closure_set(v___f_2084_, 6, v_a_2074_);
v___x_2085_ = lean_io_map_task(v___f_2084_, v_task_2078_, v_prio_2069_, v_sync_2070_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 1, v_kind_2066_);
lean_ctor_set(v___x_2082_, 0, v___x_2085_);
v___x_2087_ = v___x_2082_;
goto v_reusejp_2086_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_kind_2066_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_caption_2079_);
lean_ctor_set_uint8(v_reuseFailAlloc_2088_, sizeof(void*)*3, v_optional_2080_);
v___x_2087_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2086_;
}
v_reusejp_2086_:
{
return v___x_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object* v_kind_2091_, lean_object* v_self_2092_, lean_object* v_f_2093_, lean_object* v_prio_2094_, lean_object* v_sync_2095_, lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_){
_start:
{
uint8_t v_sync_boxed_2103_; lean_object* v_res_2104_; 
v_sync_boxed_2103_ = lean_unbox(v_sync_2095_);
v_res_2104_ = l_Lake_Job_mapM___redArg(v_kind_2091_, v_self_2092_, v_f_2093_, v_prio_2094_, v_sync_boxed_2103_, v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_, v_a_2101_);
lean_dec_ref(v_a_2101_);
lean_dec_ref(v_a_2100_);
lean_dec_ref(v_a_2099_);
lean_dec(v_a_2098_);
lean_dec(v_a_2097_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object* v_00_u03b2_2105_, lean_object* v_00_u03b1_2106_, lean_object* v_kind_2107_, lean_object* v_self_2108_, lean_object* v_f_2109_, lean_object* v_prio_2110_, uint8_t v_sync_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Lake_Job_mapM___redArg(v_kind_2107_, v_self_2108_, v_f_2109_, v_prio_2110_, v_sync_2111_, v_a_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object* v_00_u03b2_2120_, lean_object* v_00_u03b1_2121_, lean_object* v_kind_2122_, lean_object* v_self_2123_, lean_object* v_f_2124_, lean_object* v_prio_2125_, lean_object* v_sync_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_, lean_object* v_a_2129_, lean_object* v_a_2130_, lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_){
_start:
{
uint8_t v_sync_boxed_2134_; lean_object* v_res_2135_; 
v_sync_boxed_2134_ = lean_unbox(v_sync_2126_);
v_res_2135_ = l_Lake_Job_mapM(v_00_u03b2_2120_, v_00_u03b1_2121_, v_kind_2122_, v_self_2123_, v_f_2124_, v_prio_2125_, v_sync_boxed_2134_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_, v_a_2132_);
lean_dec_ref(v_a_2132_);
lean_dec_ref(v_a_2131_);
lean_dec_ref(v_a_2130_);
lean_dec(v_a_2129_);
lean_dec(v_a_2128_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object* v_a_2136_, lean_object* v_x_2137_){
_start:
{
if (lean_obj_tag(v_x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2162_; 
v_a_2138_ = lean_ctor_get(v_x_2137_, 0);
v_a_2139_ = lean_ctor_get(v_x_2137_, 1);
v_isSharedCheck_2162_ = !lean_is_exclusive(v_x_2137_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2141_ = v_x_2137_;
v_isShared_2142_ = v_isSharedCheck_2162_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_inc(v_a_2138_);
lean_dec(v_x_2137_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2162_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2143_; lean_object* v_log_2144_; uint8_t v_action_2145_; uint8_t v_wantsRebuild_2146_; uint8_t v_canceled_2147_; lean_object* v_buildTime_2148_; lean_object* v_trace_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2159_; 
lean_inc(v_a_2139_);
v___x_2143_ = l_Lake_JobState_merge(v_a_2136_, v_a_2139_);
v_log_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc_ref(v_log_2144_);
v_action_2145_ = lean_ctor_get_uint8(v___x_2143_, sizeof(void*)*3);
v_wantsRebuild_2146_ = lean_ctor_get_uint8(v___x_2143_, sizeof(void*)*3 + 1);
v_canceled_2147_ = lean_ctor_get_uint8(v___x_2143_, sizeof(void*)*3 + 2);
v_buildTime_2148_ = lean_ctor_get(v___x_2143_, 2);
lean_inc(v_buildTime_2148_);
lean_dec_ref(v___x_2143_);
v_trace_2149_ = lean_ctor_get(v_a_2139_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_a_2139_);
if (v_isSharedCheck_2159_ == 0)
{
lean_object* v_unused_2160_; lean_object* v_unused_2161_; 
v_unused_2160_ = lean_ctor_get(v_a_2139_, 2);
lean_dec(v_unused_2160_);
v_unused_2161_ = lean_ctor_get(v_a_2139_, 0);
lean_dec(v_unused_2161_);
v___x_2151_ = v_a_2139_;
v_isShared_2152_ = v_isSharedCheck_2159_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_trace_2149_);
lean_dec(v_a_2139_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2159_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
lean_ctor_set(v___x_2151_, 2, v_buildTime_2148_);
lean_ctor_set(v___x_2151_, 0, v_log_2144_);
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_log_2144_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_trace_2149_);
lean_ctor_set(v_reuseFailAlloc_2158_, 2, v_buildTime_2148_);
v___x_2154_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2156_; 
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3, v_action_2145_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 1, v_wantsRebuild_2146_);
lean_ctor_set_uint8(v___x_2154_, sizeof(void*)*3 + 2, v_canceled_2147_);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 1, v___x_2154_);
v___x_2156_ = v___x_2141_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2138_);
lean_ctor_set(v_reuseFailAlloc_2157_, 1, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2190_; 
v_a_2163_ = lean_ctor_get(v_x_2137_, 0);
v_a_2164_ = lean_ctor_get(v_x_2137_, 1);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_x_2137_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2166_ = v_x_2137_;
v_isShared_2167_ = v_isSharedCheck_2190_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_inc(v_a_2163_);
lean_dec(v_x_2137_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2190_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v_log_2168_; lean_object* v___x_2169_; lean_object* v_log_2170_; uint8_t v_action_2171_; uint8_t v_wantsRebuild_2172_; uint8_t v_canceled_2173_; lean_object* v_buildTime_2174_; lean_object* v_trace_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2187_; 
v_log_2168_ = lean_ctor_get(v_a_2136_, 0);
lean_inc_ref(v_log_2168_);
lean_inc(v_a_2164_);
v___x_2169_ = l_Lake_JobState_merge(v_a_2136_, v_a_2164_);
v_log_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc_ref(v_log_2170_);
v_action_2171_ = lean_ctor_get_uint8(v___x_2169_, sizeof(void*)*3);
v_wantsRebuild_2172_ = lean_ctor_get_uint8(v___x_2169_, sizeof(void*)*3 + 1);
v_canceled_2173_ = lean_ctor_get_uint8(v___x_2169_, sizeof(void*)*3 + 2);
v_buildTime_2174_ = lean_ctor_get(v___x_2169_, 2);
lean_inc(v_buildTime_2174_);
lean_dec_ref(v___x_2169_);
v_trace_2175_ = lean_ctor_get(v_a_2164_, 1);
v_isSharedCheck_2187_ = !lean_is_exclusive(v_a_2164_);
if (v_isSharedCheck_2187_ == 0)
{
lean_object* v_unused_2188_; lean_object* v_unused_2189_; 
v_unused_2188_ = lean_ctor_get(v_a_2164_, 2);
lean_dec(v_unused_2188_);
v_unused_2189_ = lean_ctor_get(v_a_2164_, 0);
lean_dec(v_unused_2189_);
v___x_2177_ = v_a_2164_;
v_isShared_2178_ = v_isSharedCheck_2187_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_trace_2175_);
lean_dec(v_a_2164_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2187_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2182_; 
v___x_2179_ = lean_array_get_size(v_log_2168_);
lean_dec_ref(v_log_2168_);
v___x_2180_ = lean_nat_add(v___x_2179_, v_a_2163_);
lean_dec(v_a_2163_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 2, v_buildTime_2174_);
lean_ctor_set(v___x_2177_, 0, v_log_2170_);
v___x_2182_ = v___x_2177_;
goto v_reusejp_2181_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v_log_2170_);
lean_ctor_set(v_reuseFailAlloc_2186_, 1, v_trace_2175_);
lean_ctor_set(v_reuseFailAlloc_2186_, 2, v_buildTime_2174_);
v___x_2182_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2181_;
}
v_reusejp_2181_:
{
lean_object* v___x_2184_; 
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*3, v_action_2171_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*3 + 1, v_wantsRebuild_2172_);
lean_ctor_set_uint8(v___x_2182_, sizeof(void*)*3 + 2, v_canceled_2173_);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 1, v___x_2182_);
lean_ctor_set(v___x_2166_, 0, v___x_2180_);
v___x_2184_ = v___x_2166_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2180_);
lean_ctor_set(v_reuseFailAlloc_2185_, 1, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object* v_val_2191_, lean_object* v_val_2192_, lean_object* v_a_x3f_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2196_ = lean_get_set_stdout(v_val_2191_);
lean_dec_ref(v___x_2196_);
v___x_2197_ = lean_box(0);
v___x_2198_ = lean_get_set_stderr(v_val_2192_);
lean_dec_ref(v___x_2198_);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___y_2194_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1___boxed(lean_object* v_val_2200_, lean_object* v_val_2201_, lean_object* v_a_x3f_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lake_Job_bindM___redArg___lam__1(v_val_2200_, v_val_2201_, v_a_x3f_2202_, v___y_2203_);
lean_dec(v_a_x3f_2202_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object* v_a_2206_, lean_object* v_____r_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2215_, 0, v_a_2206_);
lean_ctor_set(v___x_2215_, 1, v___y_2213_);
return v___x_2215_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2___boxed(lean_object* v_a_2216_, lean_object* v_____r_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2216_, v_____r_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3(lean_object* v_a_2226_, lean_object* v_prio_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_f_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v_a_2237_; lean_object* v_a_2238_; lean_object* v___y_2242_; lean_object* v___y_2252_; uint8_t v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; uint8_t v___y_2256_; lean_object* v___y_2257_; uint8_t v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; 
if (lean_obj_tag(v_x_2234_) == 0)
{
lean_object* v_a_2277_; lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2349_; 
v_a_2277_ = lean_ctor_get(v_x_2234_, 0);
v_a_2278_ = lean_ctor_get(v_x_2234_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_x_2234_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2280_ = v_x_2234_;
v_isShared_2281_ = v_isSharedCheck_2349_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_inc(v_a_2277_);
lean_dec(v_x_2234_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2349_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v_cancelTk_x3f_2327_; 
v_cancelTk_x3f_2327_ = lean_ctor_get(v_a_2226_, 6);
if (lean_obj_tag(v_cancelTk_x3f_2327_) == 1)
{
lean_object* v_val_2328_; uint8_t v___x_2329_; 
v_val_2328_ = lean_ctor_get(v_cancelTk_x3f_2327_, 0);
v___x_2329_ = l_IO_CancelToken_isSet(v_val_2328_);
if (v___x_2329_ == 0)
{
lean_del_object(v___x_2280_);
goto v___jp_2282_;
}
else
{
lean_object* v_log_2330_; uint8_t v_action_2331_; uint8_t v_wantsRebuild_2332_; lean_object* v_trace_2333_; lean_object* v_buildTime_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_a_2277_);
lean_dec_ref(v_f_2233_);
lean_dec_ref(v_a_2228_);
lean_dec(v_prio_2227_);
v_log_2330_ = lean_ctor_get(v_a_2278_, 0);
v_action_2331_ = lean_ctor_get_uint8(v_a_2278_, sizeof(void*)*3);
v_wantsRebuild_2332_ = lean_ctor_get_uint8(v_a_2278_, sizeof(void*)*3 + 1);
v_trace_2333_ = lean_ctor_get(v_a_2278_, 1);
v_buildTime_2334_ = lean_ctor_get(v_a_2278_, 2);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_a_2278_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2336_ = v_a_2278_;
v_isShared_2337_ = v_isSharedCheck_2348_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_buildTime_2334_);
lean_inc(v_trace_2333_);
lean_inc(v_log_2330_);
lean_dec(v_a_2278_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2348_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2342_; 
v___x_2338_ = lean_array_get_size(v_log_2330_);
v___x_2339_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_2340_ = lean_array_push(v_log_2330_, v___x_2339_);
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 0, v___x_2340_);
v___x_2342_ = v___x_2336_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2340_);
lean_ctor_set(v_reuseFailAlloc_2347_, 1, v_trace_2333_);
lean_ctor_set(v_reuseFailAlloc_2347_, 2, v_buildTime_2334_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*3, v_action_2331_);
lean_ctor_set_uint8(v_reuseFailAlloc_2347_, sizeof(void*)*3 + 1, v_wantsRebuild_2332_);
v___x_2342_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
lean_object* v___x_2344_; 
lean_ctor_set_uint8(v___x_2342_, sizeof(void*)*3 + 2, v___x_2329_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set_tag(v___x_2280_, 1);
lean_ctor_set(v___x_2280_, 1, v___x_2342_);
lean_ctor_set(v___x_2280_, 0, v___x_2338_);
v___x_2344_ = v___x_2280_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v___x_2342_);
v___x_2344_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2345_; 
v___x_2345_ = lean_task_pure(v___x_2344_);
return v___x_2345_;
}
}
}
}
}
else
{
lean_del_object(v___x_2280_);
goto v___jp_2282_;
}
v___jp_2282_:
{
lean_object* v_log_2283_; uint8_t v_action_2284_; uint8_t v_wantsRebuild_2285_; uint8_t v_canceled_2286_; lean_object* v_trace_2287_; lean_object* v_buildTime_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2326_; 
v_log_2283_ = lean_ctor_get(v_a_2278_, 0);
v_action_2284_ = lean_ctor_get_uint8(v_a_2278_, sizeof(void*)*3);
v_wantsRebuild_2285_ = lean_ctor_get_uint8(v_a_2278_, sizeof(void*)*3 + 1);
v_canceled_2286_ = lean_ctor_get_uint8(v_a_2278_, sizeof(void*)*3 + 2);
v_trace_2287_ = lean_ctor_get(v_a_2278_, 1);
v_buildTime_2288_ = lean_ctor_get(v_a_2278_, 2);
v_isSharedCheck_2326_ = !lean_is_exclusive(v_a_2278_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2290_ = v_a_2278_;
v_isShared_2291_ = v_isSharedCheck_2326_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_buildTime_2288_);
lean_inc(v_trace_2287_);
lean_inc(v_log_2283_);
lean_dec(v_a_2278_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2326_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_trace_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
lean_inc_ref(v_a_2232_);
v_trace_2292_ = l_Lake_BuildTrace_mix(v_a_2232_, v_trace_2287_);
v___x_2293_ = lean_unsigned_to_nat(0u);
v___x_2294_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_2295_ = lean_st_mk_ref(v___x_2294_);
lean_inc(v___x_2295_);
v___x_2296_ = l_IO_FS_Stream_ofBuffer(v___x_2295_);
lean_inc_ref(v___x_2296_);
v___x_2297_ = lean_get_set_stdout(v___x_2296_);
v___x_2298_ = lean_get_set_stderr(v___x_2296_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 1, v_trace_2292_);
v___x_2300_ = v___x_2290_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_log_2283_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_trace_2292_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_buildTime_2288_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*3, v_action_2284_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*3 + 1, v_wantsRebuild_2285_);
lean_ctor_set_uint8(v_reuseFailAlloc_2325_, sizeof(void*)*3 + 2, v_canceled_2286_);
v___x_2300_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; 
lean_inc_ref(v_a_2226_);
lean_inc_ref(v_a_2231_);
lean_inc(v_a_2230_);
lean_inc(v_a_2229_);
lean_inc_ref(v_a_2228_);
v___x_2301_ = lean_apply_8(v_f_2233_, v_a_2277_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2226_, v___x_2300_, lean_box(0));
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; lean_object* v_a_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v_a_2307_; lean_object* v_log_2308_; uint8_t v_action_2309_; uint8_t v_wantsRebuild_2310_; uint8_t v_canceled_2311_; lean_object* v_trace_2312_; lean_object* v_buildTime_2313_; lean_object* v___x_2314_; lean_object* v_data_2315_; uint8_t v___x_2316_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc_n(v_a_2302_, 2);
v_a_2303_ = lean_ctor_get(v___x_2301_, 1);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2301_, 2);
v___f_2304_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_2304_, 0, v_a_2302_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_a_2302_);
v___x_2306_ = l_Lake_Job_bindM___redArg___lam__1(v___x_2297_, v___x_2298_, v___x_2305_, v_a_2303_);
lean_dec_ref_known(v___x_2305_, 1);
v_a_2307_ = lean_ctor_get(v___x_2306_, 1);
lean_inc(v_a_2307_);
lean_dec_ref(v___x_2306_);
v_log_2308_ = lean_ctor_get(v_a_2307_, 0);
lean_inc_ref(v_log_2308_);
v_action_2309_ = lean_ctor_get_uint8(v_a_2307_, sizeof(void*)*3);
v_wantsRebuild_2310_ = lean_ctor_get_uint8(v_a_2307_, sizeof(void*)*3 + 1);
v_canceled_2311_ = lean_ctor_get_uint8(v_a_2307_, sizeof(void*)*3 + 2);
v_trace_2312_ = lean_ctor_get(v_a_2307_, 1);
lean_inc_ref(v_trace_2312_);
v_buildTime_2313_ = lean_ctor_get(v_a_2307_, 2);
lean_inc(v_buildTime_2313_);
v___x_2314_ = lean_st_ref_get(v___x_2295_);
lean_dec(v___x_2295_);
v_data_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc_ref(v_data_2315_);
lean_dec(v___x_2314_);
v___x_2316_ = lean_string_validate_utf8(v_data_2315_);
if (v___x_2316_ == 0)
{
lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v_data_2315_);
v___x_2317_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2318_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2317_);
v___y_2252_ = v_buildTime_2313_;
v___y_2253_ = v_action_2309_;
v___y_2254_ = v_a_2307_;
v___y_2255_ = v___f_2304_;
v___y_2256_ = v_canceled_2311_;
v___y_2257_ = v_trace_2312_;
v___y_2258_ = v_wantsRebuild_2310_;
v___y_2259_ = v___x_2293_;
v___y_2260_ = v_log_2308_;
v___y_2261_ = v___x_2318_;
goto v___jp_2251_;
}
else
{
lean_object* v___x_2319_; 
v___x_2319_ = lean_string_from_utf8_unchecked(v_data_2315_);
v___y_2252_ = v_buildTime_2313_;
v___y_2253_ = v_action_2309_;
v___y_2254_ = v_a_2307_;
v___y_2255_ = v___f_2304_;
v___y_2256_ = v_canceled_2311_;
v___y_2257_ = v_trace_2312_;
v___y_2258_ = v_wantsRebuild_2310_;
v___y_2259_ = v___x_2293_;
v___y_2260_ = v_log_2308_;
v___y_2261_ = v___x_2319_;
goto v___jp_2251_;
}
}
else
{
lean_object* v_a_2320_; lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v_a_2324_; 
lean_dec(v___x_2295_);
lean_dec_ref(v_a_2228_);
lean_dec(v_prio_2227_);
v_a_2320_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2320_);
v_a_2321_ = lean_ctor_get(v___x_2301_, 1);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2301_, 2);
v___x_2322_ = lean_box(0);
v___x_2323_ = l_Lake_Job_bindM___redArg___lam__1(v___x_2297_, v___x_2298_, v___x_2322_, v_a_2321_);
v_a_2324_ = lean_ctor_get(v___x_2323_, 1);
lean_inc(v_a_2324_);
lean_dec_ref(v___x_2323_);
v_a_2237_ = v_a_2320_;
v_a_2238_ = v_a_2324_;
goto v___jp_2236_;
}
}
}
}
}
}
else
{
lean_object* v_a_2350_; lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2359_; 
lean_dec_ref(v_f_2233_);
lean_dec_ref(v_a_2228_);
lean_dec(v_prio_2227_);
v_a_2350_ = lean_ctor_get(v_x_2234_, 0);
v_a_2351_ = lean_ctor_get(v_x_2234_, 1);
v_isSharedCheck_2359_ = !lean_is_exclusive(v_x_2234_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2353_ = v_x_2234_;
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_inc(v_a_2350_);
lean_dec(v_x_2234_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2359_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2350_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
lean_object* v___x_2357_; 
v___x_2357_ = lean_task_pure(v___x_2356_);
return v___x_2357_;
}
}
}
v___jp_2236_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2239_, 0, v_a_2237_);
lean_ctor_set(v___x_2239_, 1, v_a_2238_);
v___x_2240_ = lean_task_pure(v___x_2239_);
return v___x_2240_;
}
v___jp_2241_:
{
if (lean_obj_tag(v___y_2242_) == 0)
{
lean_object* v_a_2243_; lean_object* v_a_2244_; lean_object* v_task_2245_; lean_object* v___f_2246_; uint8_t v___x_2247_; lean_object* v___x_2248_; 
v_a_2243_ = lean_ctor_get(v___y_2242_, 0);
lean_inc(v_a_2243_);
v_a_2244_ = lean_ctor_get(v___y_2242_, 1);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___y_2242_, 2);
v_task_2245_ = lean_ctor_get(v_a_2243_, 0);
lean_inc_ref(v_task_2245_);
lean_dec(v_a_2243_);
v___f_2246_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2246_, 0, v_a_2244_);
v___x_2247_ = 1;
v___x_2248_ = lean_task_map(v___f_2246_, v_task_2245_, v_prio_2227_, v___x_2247_);
return v___x_2248_;
}
else
{
lean_object* v_a_2249_; lean_object* v_a_2250_; 
lean_dec(v_prio_2227_);
v_a_2249_ = lean_ctor_get(v___y_2242_, 0);
lean_inc(v_a_2249_);
v_a_2250_ = lean_ctor_get(v___y_2242_, 1);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___y_2242_, 2);
v_a_2237_ = v_a_2249_;
v_a_2238_ = v_a_2250_;
goto v___jp_2236_;
}
}
v___jp_2251_:
{
lean_object* v___x_2262_; uint8_t v___x_2263_; 
v___x_2262_ = lean_string_utf8_byte_size(v___y_2261_);
v___x_2263_ = lean_nat_dec_eq(v___x_2262_, v___y_2259_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_dec_ref(v___y_2254_);
v___x_2264_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_2265_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2265_, 0, v___y_2261_);
lean_ctor_set(v___x_2265_, 1, v___y_2259_);
lean_ctor_set(v___x_2265_, 2, v___x_2262_);
v___x_2266_ = l_String_Slice_trimAscii(v___x_2265_);
v___x_2267_ = l_String_Slice_toString(v___x_2266_);
lean_dec_ref(v___x_2266_);
v___x_2268_ = lean_string_append(v___x_2264_, v___x_2267_);
lean_dec_ref(v___x_2267_);
v___x_2269_ = 1;
v___x_2270_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2270_, 0, v___x_2268_);
lean_ctor_set_uint8(v___x_2270_, sizeof(void*)*1, v___x_2269_);
v___x_2271_ = lean_box(0);
v___x_2272_ = lean_array_push(v___y_2260_, v___x_2270_);
v___x_2273_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2273_, 0, v___x_2272_);
lean_ctor_set(v___x_2273_, 1, v___y_2257_);
lean_ctor_set(v___x_2273_, 2, v___y_2252_);
lean_ctor_set_uint8(v___x_2273_, sizeof(void*)*3, v___y_2253_);
lean_ctor_set_uint8(v___x_2273_, sizeof(void*)*3 + 1, v___y_2258_);
lean_ctor_set_uint8(v___x_2273_, sizeof(void*)*3 + 2, v___y_2256_);
lean_inc_ref(v_a_2226_);
lean_inc_ref(v_a_2231_);
lean_inc(v_a_2230_);
lean_inc(v_a_2229_);
v___x_2274_ = lean_apply_8(v___y_2255_, v___x_2271_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2226_, v___x_2273_, lean_box(0));
v___y_2242_ = v___x_2274_;
goto v___jp_2241_;
}
else
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_dec_ref(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2252_);
v___x_2275_ = lean_box(0);
lean_inc_ref(v_a_2226_);
lean_inc_ref(v_a_2231_);
lean_inc(v_a_2230_);
lean_inc(v_a_2229_);
v___x_2276_ = lean_apply_8(v___y_2255_, v___x_2275_, v_a_2228_, v_a_2229_, v_a_2230_, v_a_2231_, v_a_2226_, v___y_2254_, lean_box(0));
v___y_2242_ = v___x_2276_;
goto v___jp_2241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3___boxed(lean_object* v_a_2360_, lean_object* v_prio_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_f_2367_, lean_object* v_x_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_res_2370_; 
v_res_2370_ = l_Lake_Job_bindM___redArg___lam__3(v_a_2360_, v_prio_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_, v_f_2367_, v_x_2368_);
lean_dec_ref(v_a_2366_);
lean_dec_ref(v_a_2365_);
lean_dec(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2360_);
return v_res_2370_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg(lean_object* v_kind_2371_, lean_object* v_self_2372_, lean_object* v_f_2373_, lean_object* v_prio_2374_, uint8_t v_sync_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_){
_start:
{
lean_object* v_task_2383_; lean_object* v_caption_2384_; uint8_t v_optional_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2394_; 
v_task_2383_ = lean_ctor_get(v_self_2372_, 0);
v_caption_2384_ = lean_ctor_get(v_self_2372_, 2);
v_optional_2385_ = lean_ctor_get_uint8(v_self_2372_, sizeof(void*)*3);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_self_2372_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; 
v_unused_2395_ = lean_ctor_get(v_self_2372_, 1);
lean_dec(v_unused_2395_);
v___x_2387_ = v_self_2372_;
v_isShared_2388_ = v_isSharedCheck_2394_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_caption_2384_);
lean_inc(v_task_2383_);
lean_dec(v_self_2372_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2394_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___f_2389_; lean_object* v___x_2390_; lean_object* v___x_2392_; 
lean_inc_ref(v_a_2381_);
lean_inc_ref(v_a_2379_);
lean_inc(v_a_2378_);
lean_inc(v_a_2377_);
lean_inc(v_prio_2374_);
lean_inc_ref(v_a_2380_);
v___f_2389_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__3___boxed), 10, 8);
lean_closure_set(v___f_2389_, 0, v_a_2380_);
lean_closure_set(v___f_2389_, 1, v_prio_2374_);
lean_closure_set(v___f_2389_, 2, v_a_2376_);
lean_closure_set(v___f_2389_, 3, v_a_2377_);
lean_closure_set(v___f_2389_, 4, v_a_2378_);
lean_closure_set(v___f_2389_, 5, v_a_2379_);
lean_closure_set(v___f_2389_, 6, v_a_2381_);
lean_closure_set(v___f_2389_, 7, v_f_2373_);
v___x_2390_ = lean_io_bind_task(v_task_2383_, v___f_2389_, v_prio_2374_, v_sync_2375_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 1, v_kind_2371_);
lean_ctor_set(v___x_2387_, 0, v___x_2390_);
v___x_2392_ = v___x_2387_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2390_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_kind_2371_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v_caption_2384_);
lean_ctor_set_uint8(v_reuseFailAlloc_2393_, sizeof(void*)*3, v_optional_2385_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object* v_kind_2396_, lean_object* v_self_2397_, lean_object* v_f_2398_, lean_object* v_prio_2399_, lean_object* v_sync_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_){
_start:
{
uint8_t v_sync_boxed_2408_; lean_object* v_res_2409_; 
v_sync_boxed_2408_ = lean_unbox(v_sync_2400_);
v_res_2409_ = l_Lake_Job_bindM___redArg(v_kind_2396_, v_self_2397_, v_f_2398_, v_prio_2399_, v_sync_boxed_2408_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_, v_a_2406_);
lean_dec_ref(v_a_2406_);
lean_dec_ref(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec(v_a_2402_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM(lean_object* v_00_u03b2_2410_, lean_object* v_00_u03b1_2411_, lean_object* v_kind_2412_, lean_object* v_self_2413_, lean_object* v_f_2414_, lean_object* v_prio_2415_, uint8_t v_sync_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_, lean_object* v_a_2422_){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lake_Job_bindM___redArg(v_kind_2412_, v_self_2413_, v_f_2414_, v_prio_2415_, v_sync_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_, v_a_2421_, v_a_2422_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object* v_00_u03b2_2425_, lean_object* v_00_u03b1_2426_, lean_object* v_kind_2427_, lean_object* v_self_2428_, lean_object* v_f_2429_, lean_object* v_prio_2430_, lean_object* v_sync_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_){
_start:
{
uint8_t v_sync_boxed_2439_; lean_object* v_res_2440_; 
v_sync_boxed_2439_ = lean_unbox(v_sync_2431_);
v_res_2440_ = l_Lake_Job_bindM(v_00_u03b2_2425_, v_00_u03b1_2426_, v_kind_2427_, v_self_2428_, v_f_2429_, v_prio_2430_, v_sync_boxed_2439_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_, v_a_2437_);
lean_dec_ref(v_a_2437_);
lean_dec_ref(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec(v_a_2433_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object* v_f_2441_, lean_object* v_rx_2442_, lean_object* v_ry_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_apply_2(v_f_2441_, v_rx_2442_, v_ry_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object* v_other_2445_, lean_object* v_f_2446_, lean_object* v_prio_2447_, uint8_t v_sync_2448_, lean_object* v_rx_2449_){
_start:
{
lean_object* v_task_2450_; lean_object* v___f_2451_; lean_object* v___x_2452_; 
v_task_2450_ = lean_ctor_get(v_other_2445_, 0);
lean_inc_ref(v_task_2450_);
lean_dec_ref(v_other_2445_);
v___f_2451_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2451_, 0, v_f_2446_);
lean_closure_set(v___f_2451_, 1, v_rx_2449_);
v___x_2452_ = lean_task_map(v___f_2451_, v_task_2450_, v_prio_2447_, v_sync_2448_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object* v_other_2453_, lean_object* v_f_2454_, lean_object* v_prio_2455_, lean_object* v_sync_2456_, lean_object* v_rx_2457_){
_start:
{
uint8_t v_sync_boxed_2458_; lean_object* v_res_2459_; 
v_sync_boxed_2458_ = lean_unbox(v_sync_2456_);
v_res_2459_ = l_Lake_Job_zipResultWith___redArg___lam__1(v_other_2453_, v_f_2454_, v_prio_2455_, v_sync_boxed_2458_, v_rx_2457_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg(lean_object* v_inst_2460_, lean_object* v_f_2461_, lean_object* v_self_2462_, lean_object* v_other_2463_, lean_object* v_prio_2464_, uint8_t v_sync_2465_){
_start:
{
lean_object* v_task_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2479_; 
v_task_2466_ = lean_ctor_get(v_self_2462_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v_self_2462_);
if (v_isSharedCheck_2479_ == 0)
{
lean_object* v_unused_2480_; lean_object* v_unused_2481_; 
v_unused_2480_ = lean_ctor_get(v_self_2462_, 2);
lean_dec(v_unused_2480_);
v_unused_2481_ = lean_ctor_get(v_self_2462_, 1);
lean_dec(v_unused_2481_);
v___x_2468_ = v_self_2462_;
v_isShared_2469_ = v_isSharedCheck_2479_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_task_2466_);
lean_dec(v_self_2462_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2479_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2470_; lean_object* v___f_2471_; uint8_t v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; uint8_t v___x_2475_; lean_object* v___x_2477_; 
v___x_2470_ = lean_box(v_sync_2465_);
lean_inc(v_prio_2464_);
v___f_2471_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2471_, 0, v_other_2463_);
lean_closure_set(v___f_2471_, 1, v_f_2461_);
lean_closure_set(v___f_2471_, 2, v_prio_2464_);
lean_closure_set(v___f_2471_, 3, v___x_2470_);
v___x_2472_ = 1;
v___x_2473_ = lean_task_bind(v_task_2466_, v___f_2471_, v_prio_2464_, v___x_2472_);
v___x_2474_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2475_ = 0;
if (v_isShared_2469_ == 0)
{
lean_ctor_set(v___x_2468_, 2, v___x_2474_);
lean_ctor_set(v___x_2468_, 1, v_inst_2460_);
lean_ctor_set(v___x_2468_, 0, v___x_2473_);
v___x_2477_ = v___x_2468_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2478_, 1, v_inst_2460_);
lean_ctor_set(v_reuseFailAlloc_2478_, 2, v___x_2474_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_ctor_set_uint8(v___x_2477_, sizeof(void*)*3, v___x_2475_);
return v___x_2477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object* v_inst_2482_, lean_object* v_f_2483_, lean_object* v_self_2484_, lean_object* v_other_2485_, lean_object* v_prio_2486_, lean_object* v_sync_2487_){
_start:
{
uint8_t v_sync_boxed_2488_; lean_object* v_res_2489_; 
v_sync_boxed_2488_ = lean_unbox(v_sync_2487_);
v_res_2489_ = l_Lake_Job_zipResultWith___redArg(v_inst_2482_, v_f_2483_, v_self_2484_, v_other_2485_, v_prio_2486_, v_sync_boxed_2488_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith(lean_object* v_00_u03b3_2490_, lean_object* v_00_u03b1_2491_, lean_object* v_00_u03b2_2492_, lean_object* v_inst_2493_, lean_object* v_f_2494_, lean_object* v_self_2495_, lean_object* v_other_2496_, lean_object* v_prio_2497_, uint8_t v_sync_2498_){
_start:
{
lean_object* v_task_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2512_; 
v_task_2499_ = lean_ctor_get(v_self_2495_, 0);
v_isSharedCheck_2512_ = !lean_is_exclusive(v_self_2495_);
if (v_isSharedCheck_2512_ == 0)
{
lean_object* v_unused_2513_; lean_object* v_unused_2514_; 
v_unused_2513_ = lean_ctor_get(v_self_2495_, 2);
lean_dec(v_unused_2513_);
v_unused_2514_ = lean_ctor_get(v_self_2495_, 1);
lean_dec(v_unused_2514_);
v___x_2501_ = v_self_2495_;
v_isShared_2502_ = v_isSharedCheck_2512_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_task_2499_);
lean_dec(v_self_2495_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2512_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2503_; lean_object* v___f_2504_; uint8_t v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; uint8_t v___x_2508_; lean_object* v___x_2510_; 
v___x_2503_ = lean_box(v_sync_2498_);
lean_inc(v_prio_2497_);
v___f_2504_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2504_, 0, v_other_2496_);
lean_closure_set(v___f_2504_, 1, v_f_2494_);
lean_closure_set(v___f_2504_, 2, v_prio_2497_);
lean_closure_set(v___f_2504_, 3, v___x_2503_);
v___x_2505_ = 1;
v___x_2506_ = lean_task_bind(v_task_2499_, v___f_2504_, v_prio_2497_, v___x_2505_);
v___x_2507_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2508_ = 0;
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 2, v___x_2507_);
lean_ctor_set(v___x_2501_, 1, v_inst_2493_);
lean_ctor_set(v___x_2501_, 0, v___x_2506_);
v___x_2510_ = v___x_2501_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2506_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_inst_2493_);
lean_ctor_set(v_reuseFailAlloc_2511_, 2, v___x_2507_);
v___x_2510_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_ctor_set_uint8(v___x_2510_, sizeof(void*)*3, v___x_2508_);
return v___x_2510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object* v_00_u03b3_2515_, lean_object* v_00_u03b1_2516_, lean_object* v_00_u03b2_2517_, lean_object* v_inst_2518_, lean_object* v_f_2519_, lean_object* v_self_2520_, lean_object* v_other_2521_, lean_object* v_prio_2522_, lean_object* v_sync_2523_){
_start:
{
uint8_t v_sync_boxed_2524_; lean_object* v_res_2525_; 
v_sync_boxed_2524_ = lean_unbox(v_sync_2523_);
v_res_2525_ = l_Lake_Job_zipResultWith(v_00_u03b3_2515_, v_00_u03b1_2516_, v_00_u03b2_2517_, v_inst_2518_, v_f_2519_, v_self_2520_, v_other_2521_, v_prio_2522_, v_sync_boxed_2524_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object* v_rx_2526_, lean_object* v_f_2527_, lean_object* v_ry_2528_){
_start:
{
lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___y_2536_; lean_object* v___y_2537_; lean_object* v___y_2538_; lean_object* v_a_2541_; 
if (lean_obj_tag(v_rx_2526_) == 0)
{
if (lean_obj_tag(v_ry_2528_) == 0)
{
lean_object* v_a_2543_; lean_object* v_a_2544_; lean_object* v_a_2545_; lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2555_; 
v_a_2543_ = lean_ctor_get(v_rx_2526_, 0);
lean_inc(v_a_2543_);
v_a_2544_ = lean_ctor_get(v_rx_2526_, 1);
lean_inc(v_a_2544_);
lean_dec_ref_known(v_rx_2526_, 2);
v_a_2545_ = lean_ctor_get(v_ry_2528_, 0);
v_a_2546_ = lean_ctor_get(v_ry_2528_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_ry_2528_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2548_ = v_ry_2528_;
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_inc(v_a_2545_);
lean_dec(v_ry_2528_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2555_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2553_; 
v___x_2550_ = lean_apply_2(v_f_2527_, v_a_2543_, v_a_2545_);
v___x_2551_ = l_Lake_JobState_merge(v_a_2544_, v_a_2546_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 1, v___x_2551_);
lean_ctor_set(v___x_2548_, 0, v___x_2550_);
v___x_2553_ = v___x_2548_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2550_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v___x_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
else
{
lean_object* v_a_2556_; 
lean_dec(v_f_2527_);
v_a_2556_ = lean_ctor_get(v_rx_2526_, 1);
lean_inc(v_a_2556_);
lean_dec_ref_known(v_rx_2526_, 2);
v_a_2541_ = v_a_2556_;
goto v___jp_2540_;
}
}
else
{
lean_dec(v_f_2527_);
if (lean_obj_tag(v_rx_2526_) == 0)
{
lean_object* v_a_2557_; 
v_a_2557_ = lean_ctor_get(v_rx_2526_, 1);
lean_inc(v_a_2557_);
lean_dec_ref_known(v_rx_2526_, 2);
v_a_2541_ = v_a_2557_;
goto v___jp_2540_;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2559_; 
v_a_2558_ = lean_ctor_get(v_rx_2526_, 1);
lean_inc(v_a_2558_);
lean_dec_ref_known(v_rx_2526_, 2);
v___x_2559_ = lean_unsigned_to_nat(0u);
v___y_2536_ = v___x_2559_;
v___y_2537_ = v_ry_2528_;
v___y_2538_ = v_a_2558_;
goto v___jp_2535_;
}
}
v___jp_2529_:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = l_Lake_JobState_merge(v___y_2530_, v___y_2532_);
v___x_2534_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___y_2531_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
return v___x_2534_;
}
v___jp_2535_:
{
lean_object* v_a_2539_; 
v_a_2539_ = lean_ctor_get(v___y_2537_, 1);
lean_inc(v_a_2539_);
lean_dec_ref(v___y_2537_);
v___y_2530_ = v___y_2538_;
v___y_2531_ = v___y_2536_;
v___y_2532_ = v_a_2539_;
goto v___jp_2529_;
}
v___jp_2540_:
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_unsigned_to_nat(0u);
v___y_2536_ = v___x_2542_;
v___y_2537_ = v_ry_2528_;
v___y_2538_ = v_a_2541_;
goto v___jp_2535_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object* v_other_2560_, lean_object* v_f_2561_, lean_object* v_prio_2562_, uint8_t v_sync_2563_, lean_object* v_rx_2564_){
_start:
{
lean_object* v_task_2565_; lean_object* v___f_2566_; lean_object* v___x_2567_; 
v_task_2565_ = lean_ctor_get(v_other_2560_, 0);
lean_inc_ref(v_task_2565_);
lean_dec_ref(v_other_2560_);
v___f_2566_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2566_, 0, v_rx_2564_);
lean_closure_set(v___f_2566_, 1, v_f_2561_);
v___x_2567_ = lean_task_map(v___f_2566_, v_task_2565_, v_prio_2562_, v_sync_2563_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object* v_other_2568_, lean_object* v_f_2569_, lean_object* v_prio_2570_, lean_object* v_sync_2571_, lean_object* v_rx_2572_){
_start:
{
uint8_t v_sync_boxed_2573_; lean_object* v_res_2574_; 
v_sync_boxed_2573_ = lean_unbox(v_sync_2571_);
v_res_2574_ = l_Lake_Job_zipWith___redArg___lam__1(v_other_2568_, v_f_2569_, v_prio_2570_, v_sync_boxed_2573_, v_rx_2572_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg(lean_object* v_inst_2575_, lean_object* v_f_2576_, lean_object* v_self_2577_, lean_object* v_other_2578_, lean_object* v_prio_2579_, uint8_t v_sync_2580_){
_start:
{
lean_object* v_task_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2594_; 
v_task_2581_ = lean_ctor_get(v_self_2577_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v_self_2577_);
if (v_isSharedCheck_2594_ == 0)
{
lean_object* v_unused_2595_; lean_object* v_unused_2596_; 
v_unused_2595_ = lean_ctor_get(v_self_2577_, 2);
lean_dec(v_unused_2595_);
v_unused_2596_ = lean_ctor_get(v_self_2577_, 1);
lean_dec(v_unused_2596_);
v___x_2583_ = v_self_2577_;
v_isShared_2584_ = v_isSharedCheck_2594_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_task_2581_);
lean_dec(v_self_2577_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2594_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___f_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; uint8_t v___x_2590_; lean_object* v___x_2592_; 
v___x_2585_ = lean_box(v_sync_2580_);
lean_inc(v_prio_2579_);
v___f_2586_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2586_, 0, v_other_2578_);
lean_closure_set(v___f_2586_, 1, v_f_2576_);
lean_closure_set(v___f_2586_, 2, v_prio_2579_);
lean_closure_set(v___f_2586_, 3, v___x_2585_);
v___x_2587_ = 1;
v___x_2588_ = lean_task_bind(v_task_2581_, v___f_2586_, v_prio_2579_, v___x_2587_);
v___x_2589_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2590_ = 0;
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 2, v___x_2589_);
lean_ctor_set(v___x_2583_, 1, v_inst_2575_);
lean_ctor_set(v___x_2583_, 0, v___x_2588_);
v___x_2592_ = v___x_2583_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v___x_2588_);
lean_ctor_set(v_reuseFailAlloc_2593_, 1, v_inst_2575_);
lean_ctor_set(v_reuseFailAlloc_2593_, 2, v___x_2589_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
lean_ctor_set_uint8(v___x_2592_, sizeof(void*)*3, v___x_2590_);
return v___x_2592_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object* v_inst_2597_, lean_object* v_f_2598_, lean_object* v_self_2599_, lean_object* v_other_2600_, lean_object* v_prio_2601_, lean_object* v_sync_2602_){
_start:
{
uint8_t v_sync_boxed_2603_; lean_object* v_res_2604_; 
v_sync_boxed_2603_ = lean_unbox(v_sync_2602_);
v_res_2604_ = l_Lake_Job_zipWith___redArg(v_inst_2597_, v_f_2598_, v_self_2599_, v_other_2600_, v_prio_2601_, v_sync_boxed_2603_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__0(lean_object* v_rx_2605_, lean_object* v_f_2606_, lean_object* v_ry_2607_){
_start:
{
lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v_a_2620_; lean_object* v_rb_2621_; 
if (lean_obj_tag(v_rx_2605_) == 0)
{
if (lean_obj_tag(v_ry_2607_) == 0)
{
lean_object* v_a_2623_; lean_object* v_a_2624_; lean_object* v_a_2625_; lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2635_; 
v_a_2623_ = lean_ctor_get(v_rx_2605_, 0);
lean_inc(v_a_2623_);
v_a_2624_ = lean_ctor_get(v_rx_2605_, 1);
lean_inc(v_a_2624_);
lean_dec_ref_known(v_rx_2605_, 2);
v_a_2625_ = lean_ctor_get(v_ry_2607_, 0);
v_a_2626_ = lean_ctor_get(v_ry_2607_, 1);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_ry_2607_);
if (v_isSharedCheck_2635_ == 0)
{
v___x_2628_ = v_ry_2607_;
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_inc(v_a_2625_);
lean_dec(v_ry_2607_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2635_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2633_; 
v___x_2630_ = lean_apply_2(v_f_2606_, v_a_2623_, v_a_2625_);
v___x_2631_ = l_Lake_JobState_merge(v_a_2624_, v_a_2626_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 1, v___x_2631_);
lean_ctor_set(v___x_2628_, 0, v___x_2630_);
v___x_2633_ = v___x_2628_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2634_; 
v_reuseFailAlloc_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2630_);
lean_ctor_set(v_reuseFailAlloc_2634_, 1, v___x_2631_);
v___x_2633_ = v_reuseFailAlloc_2634_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
return v___x_2633_;
}
}
}
else
{
lean_object* v_a_2636_; 
lean_dec(v_f_2606_);
v_a_2636_ = lean_ctor_get(v_rx_2605_, 1);
lean_inc(v_a_2636_);
lean_dec_ref_known(v_rx_2605_, 2);
v_a_2620_ = v_a_2636_;
v_rb_2621_ = v_ry_2607_;
goto v___jp_2619_;
}
}
else
{
lean_dec(v_f_2606_);
if (lean_obj_tag(v_rx_2605_) == 0)
{
lean_object* v_a_2637_; 
v_a_2637_ = lean_ctor_get(v_rx_2605_, 1);
lean_inc(v_a_2637_);
lean_dec_ref_known(v_rx_2605_, 2);
v_a_2620_ = v_a_2637_;
v_rb_2621_ = v_ry_2607_;
goto v___jp_2619_;
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2639_; 
v_a_2638_ = lean_ctor_get(v_rx_2605_, 1);
lean_inc(v_a_2638_);
lean_dec_ref_known(v_rx_2605_, 2);
v___x_2639_ = lean_unsigned_to_nat(0u);
v___y_2615_ = v___x_2639_;
v___y_2616_ = v_ry_2607_;
v___y_2617_ = v_a_2638_;
goto v___jp_2614_;
}
}
v___jp_2608_:
{
lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2612_ = l_Lake_JobState_merge(v___y_2609_, v___y_2611_);
v___x_2613_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___y_2610_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
return v___x_2613_;
}
v___jp_2614_:
{
lean_object* v_a_2618_; 
v_a_2618_ = lean_ctor_get(v___y_2616_, 1);
lean_inc(v_a_2618_);
lean_dec_ref(v___y_2616_);
v___y_2609_ = v___y_2617_;
v___y_2610_ = v___y_2615_;
v___y_2611_ = v_a_2618_;
goto v___jp_2608_;
}
v___jp_2619_:
{
lean_object* v___x_2622_; 
v___x_2622_ = lean_unsigned_to_nat(0u);
v___y_2615_ = v___x_2622_;
v___y_2616_ = v_rb_2621_;
v___y_2617_ = v_a_2620_;
goto v___jp_2614_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1(lean_object* v_other_2640_, lean_object* v_f_2641_, lean_object* v_prio_2642_, uint8_t v_sync_2643_, lean_object* v_rx_2644_){
_start:
{
lean_object* v_task_2645_; lean_object* v___f_2646_; lean_object* v___x_2647_; 
v_task_2645_ = lean_ctor_get(v_other_2640_, 0);
lean_inc_ref(v_task_2645_);
lean_dec_ref(v_other_2640_);
v___f_2646_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__0), 3, 2);
lean_closure_set(v___f_2646_, 0, v_rx_2644_);
lean_closure_set(v___f_2646_, 1, v_f_2641_);
v___x_2647_ = lean_task_map(v___f_2646_, v_task_2645_, v_prio_2642_, v_sync_2643_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1___boxed(lean_object* v_other_2648_, lean_object* v_f_2649_, lean_object* v_prio_2650_, lean_object* v_sync_2651_, lean_object* v_rx_2652_){
_start:
{
uint8_t v_sync_boxed_2653_; lean_object* v_res_2654_; 
v_sync_boxed_2653_ = lean_unbox(v_sync_2651_);
v_res_2654_ = l_Lake_Job_zipWith___lam__1(v_other_2648_, v_f_2649_, v_prio_2650_, v_sync_boxed_2653_, v_rx_2652_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith(lean_object* v_00_u03b3_2655_, lean_object* v_00_u03b1_2656_, lean_object* v_00_u03b2_2657_, lean_object* v_inst_2658_, lean_object* v_f_2659_, lean_object* v_self_2660_, lean_object* v_other_2661_, lean_object* v_prio_2662_, uint8_t v_sync_2663_){
_start:
{
lean_object* v_task_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2677_; 
v_task_2664_ = lean_ctor_get(v_self_2660_, 0);
v_isSharedCheck_2677_ = !lean_is_exclusive(v_self_2660_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; lean_object* v_unused_2679_; 
v_unused_2678_ = lean_ctor_get(v_self_2660_, 2);
lean_dec(v_unused_2678_);
v_unused_2679_ = lean_ctor_get(v_self_2660_, 1);
lean_dec(v_unused_2679_);
v___x_2666_ = v_self_2660_;
v_isShared_2667_ = v_isSharedCheck_2677_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_task_2664_);
lean_dec(v_self_2660_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2677_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
lean_object* v___x_2668_; lean_object* v___f_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; lean_object* v___x_2675_; 
v___x_2668_ = lean_box(v_sync_2663_);
lean_inc(v_prio_2662_);
v___f_2669_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2669_, 0, v_other_2661_);
lean_closure_set(v___f_2669_, 1, v_f_2659_);
lean_closure_set(v___f_2669_, 2, v_prio_2662_);
lean_closure_set(v___f_2669_, 3, v___x_2668_);
v___x_2670_ = 1;
v___x_2671_ = lean_task_bind(v_task_2664_, v___f_2669_, v_prio_2662_, v___x_2670_);
v___x_2672_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2673_ = 0;
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 2, v___x_2672_);
lean_ctor_set(v___x_2666_, 1, v_inst_2658_);
lean_ctor_set(v___x_2666_, 0, v___x_2671_);
v___x_2675_ = v___x_2666_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v___x_2671_);
lean_ctor_set(v_reuseFailAlloc_2676_, 1, v_inst_2658_);
lean_ctor_set(v_reuseFailAlloc_2676_, 2, v___x_2672_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
lean_ctor_set_uint8(v___x_2675_, sizeof(void*)*3, v___x_2673_);
return v___x_2675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object* v_00_u03b3_2680_, lean_object* v_00_u03b1_2681_, lean_object* v_00_u03b2_2682_, lean_object* v_inst_2683_, lean_object* v_f_2684_, lean_object* v_self_2685_, lean_object* v_other_2686_, lean_object* v_prio_2687_, lean_object* v_sync_2688_){
_start:
{
uint8_t v_sync_boxed_2689_; lean_object* v_res_2690_; 
v_sync_boxed_2689_ = lean_unbox(v_sync_2688_);
v_res_2690_ = l_Lake_Job_zipWith(v_00_u03b3_2680_, v_00_u03b1_2681_, v_00_u03b2_2682_, v_inst_2683_, v_f_2684_, v_self_2685_, v_other_2686_, v_prio_2687_, v_sync_boxed_2689_);
return v_res_2690_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object* v___x_2691_, lean_object* v_rx_2692_, lean_object* v_ry_2693_){
_start:
{
lean_object* v___y_2695_; lean_object* v___y_2696_; lean_object* v___y_2715_; lean_object* v___y_2716_; 
if (lean_obj_tag(v_rx_2692_) == 0)
{
if (lean_obj_tag(v_ry_2693_) == 0)
{
lean_object* v_a_2718_; lean_object* v_a_2719_; lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v___x_2691_);
v_a_2718_ = lean_ctor_get(v_rx_2692_, 0);
lean_inc(v_a_2718_);
v_a_2719_ = lean_ctor_get(v_rx_2692_, 1);
lean_inc(v_a_2719_);
lean_dec_ref_known(v_rx_2692_, 2);
v_a_2720_ = lean_ctor_get(v_ry_2693_, 1);
v_isSharedCheck_2743_ = !lean_is_exclusive(v_ry_2693_);
if (v_isSharedCheck_2743_ == 0)
{
lean_object* v_unused_2744_; 
v_unused_2744_ = lean_ctor_get(v_ry_2693_, 0);
lean_dec(v_unused_2744_);
v___x_2722_ = v_ry_2693_;
v_isShared_2723_ = v_isSharedCheck_2743_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v_ry_2693_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2743_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v_log_2725_; uint8_t v_action_2726_; uint8_t v_wantsRebuild_2727_; uint8_t v_canceled_2728_; lean_object* v_buildTime_2729_; lean_object* v_trace_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2740_; 
lean_inc(v_a_2719_);
v___x_2724_ = l_Lake_JobState_merge(v_a_2719_, v_a_2720_);
v_log_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc_ref(v_log_2725_);
v_action_2726_ = lean_ctor_get_uint8(v___x_2724_, sizeof(void*)*3);
v_wantsRebuild_2727_ = lean_ctor_get_uint8(v___x_2724_, sizeof(void*)*3 + 1);
v_canceled_2728_ = lean_ctor_get_uint8(v___x_2724_, sizeof(void*)*3 + 2);
v_buildTime_2729_ = lean_ctor_get(v___x_2724_, 2);
lean_inc(v_buildTime_2729_);
lean_dec_ref(v___x_2724_);
v_trace_2730_ = lean_ctor_get(v_a_2719_, 1);
v_isSharedCheck_2740_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2740_ == 0)
{
lean_object* v_unused_2741_; lean_object* v_unused_2742_; 
v_unused_2741_ = lean_ctor_get(v_a_2719_, 2);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_a_2719_, 0);
lean_dec(v_unused_2742_);
v___x_2732_ = v_a_2719_;
v_isShared_2733_ = v_isSharedCheck_2740_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_trace_2730_);
lean_dec(v_a_2719_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2740_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 2, v_buildTime_2729_);
lean_ctor_set(v___x_2732_, 0, v_log_2725_);
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_log_2725_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v_trace_2730_);
lean_ctor_set(v_reuseFailAlloc_2739_, 2, v_buildTime_2729_);
v___x_2735_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___x_2737_; 
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*3, v_action_2726_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*3 + 1, v_wantsRebuild_2727_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*3 + 2, v_canceled_2728_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set(v___x_2722_, 1, v___x_2735_);
lean_ctor_set(v___x_2722_, 0, v_a_2718_);
v___x_2737_ = v___x_2722_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2718_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
else
{
lean_object* v_a_2745_; 
v_a_2745_ = lean_ctor_get(v_rx_2692_, 1);
lean_inc(v_a_2745_);
lean_dec_ref_known(v_rx_2692_, 2);
v___y_2715_ = v_ry_2693_;
v___y_2716_ = v_a_2745_;
goto v___jp_2714_;
}
}
else
{
lean_object* v_a_2746_; 
v_a_2746_ = lean_ctor_get(v_rx_2692_, 1);
lean_inc(v_a_2746_);
lean_dec_ref(v_rx_2692_);
v___y_2715_ = v_ry_2693_;
v___y_2716_ = v_a_2746_;
goto v___jp_2714_;
}
v___jp_2694_:
{
lean_object* v___x_2697_; lean_object* v_log_2698_; uint8_t v_action_2699_; uint8_t v_wantsRebuild_2700_; uint8_t v_canceled_2701_; lean_object* v_buildTime_2702_; lean_object* v_trace_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2711_; 
lean_inc_ref(v___y_2695_);
v___x_2697_ = l_Lake_JobState_merge(v___y_2695_, v___y_2696_);
v_log_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc_ref(v_log_2698_);
v_action_2699_ = lean_ctor_get_uint8(v___x_2697_, sizeof(void*)*3);
v_wantsRebuild_2700_ = lean_ctor_get_uint8(v___x_2697_, sizeof(void*)*3 + 1);
v_canceled_2701_ = lean_ctor_get_uint8(v___x_2697_, sizeof(void*)*3 + 2);
v_buildTime_2702_ = lean_ctor_get(v___x_2697_, 2);
lean_inc(v_buildTime_2702_);
lean_dec_ref(v___x_2697_);
v_trace_2703_ = lean_ctor_get(v___y_2695_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___y_2695_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; lean_object* v_unused_2713_; 
v_unused_2712_ = lean_ctor_get(v___y_2695_, 2);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v___y_2695_, 0);
lean_dec(v_unused_2713_);
v___x_2705_ = v___y_2695_;
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_trace_2703_);
lean_dec(v___y_2695_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 2, v_buildTime_2702_);
lean_ctor_set(v___x_2705_, 0, v_log_2698_);
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_log_2698_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_trace_2703_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_buildTime_2702_);
v___x_2708_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
lean_object* v___x_2709_; 
lean_ctor_set_uint8(v___x_2708_, sizeof(void*)*3, v_action_2699_);
lean_ctor_set_uint8(v___x_2708_, sizeof(void*)*3 + 1, v_wantsRebuild_2700_);
lean_ctor_set_uint8(v___x_2708_, sizeof(void*)*3 + 2, v_canceled_2701_);
v___x_2709_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2691_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
return v___x_2709_;
}
}
}
v___jp_2714_:
{
lean_object* v_a_2717_; 
v_a_2717_ = lean_ctor_get(v___y_2715_, 1);
lean_inc(v_a_2717_);
lean_dec_ref(v___y_2715_);
v___y_2695_ = v___y_2716_;
v___y_2696_ = v_a_2717_;
goto v___jp_2694_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1(lean_object* v_other_2747_, lean_object* v___x_2748_, uint8_t v___x_2749_, lean_object* v_rx_2750_){
_start:
{
lean_object* v_task_2751_; lean_object* v___f_2752_; lean_object* v___x_2753_; 
v_task_2751_ = lean_ctor_get(v_other_2747_, 0);
lean_inc_ref(v_task_2751_);
lean_dec_ref(v_other_2747_);
lean_inc(v___x_2748_);
v___f_2752_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2752_, 0, v___x_2748_);
lean_closure_set(v___f_2752_, 1, v_rx_2750_);
v___x_2753_ = lean_task_map(v___f_2752_, v_task_2751_, v___x_2748_, v___x_2749_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object* v_other_2754_, lean_object* v___x_2755_, lean_object* v___x_2756_, lean_object* v_rx_2757_){
_start:
{
uint8_t v___x_258__boxed_2758_; lean_object* v_res_2759_; 
v___x_258__boxed_2758_ = lean_unbox(v___x_2756_);
v_res_2759_ = l_Lake_Job_add___redArg___lam__1(v_other_2754_, v___x_2755_, v___x_258__boxed_2758_, v_rx_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object* v_self_2760_, lean_object* v_other_2761_){
_start:
{
lean_object* v_task_2762_; lean_object* v_kind_2763_; lean_object* v___x_2765_; uint8_t v_isShared_2766_; uint8_t v_isSharedCheck_2777_; 
v_task_2762_ = lean_ctor_get(v_self_2760_, 0);
v_kind_2763_ = lean_ctor_get(v_self_2760_, 1);
v_isSharedCheck_2777_ = !lean_is_exclusive(v_self_2760_);
if (v_isSharedCheck_2777_ == 0)
{
lean_object* v_unused_2778_; 
v_unused_2778_ = lean_ctor_get(v_self_2760_, 2);
lean_dec(v_unused_2778_);
v___x_2765_ = v_self_2760_;
v_isShared_2766_ = v_isSharedCheck_2777_;
goto v_resetjp_2764_;
}
else
{
lean_inc(v_kind_2763_);
lean_inc(v_task_2762_);
lean_dec(v_self_2760_);
v___x_2765_ = lean_box(0);
v_isShared_2766_ = v_isSharedCheck_2777_;
goto v_resetjp_2764_;
}
v_resetjp_2764_:
{
lean_object* v___x_2767_; uint8_t v___x_2768_; lean_object* v___x_2769_; lean_object* v___f_2770_; uint8_t v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
v___x_2767_ = lean_unsigned_to_nat(0u);
v___x_2768_ = 0;
v___x_2769_ = lean_box(v___x_2768_);
v___f_2770_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2770_, 0, v_other_2761_);
lean_closure_set(v___f_2770_, 1, v___x_2767_);
lean_closure_set(v___f_2770_, 2, v___x_2769_);
v___x_2771_ = 1;
v___x_2772_ = lean_task_bind(v_task_2762_, v___f_2770_, v___x_2767_, v___x_2771_);
v___x_2773_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2766_ == 0)
{
lean_ctor_set(v___x_2765_, 2, v___x_2773_);
lean_ctor_set(v___x_2765_, 0, v___x_2772_);
v___x_2775_ = v___x_2765_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v_kind_2763_);
lean_ctor_set(v_reuseFailAlloc_2776_, 2, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_ctor_set_uint8(v___x_2775_, sizeof(void*)*3, v___x_2768_);
return v___x_2775_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object* v_00_u03b1_2779_, lean_object* v_00_u03b2_2780_, lean_object* v_self_2781_, lean_object* v_other_2782_){
_start:
{
lean_object* v___x_2783_; 
v___x_2783_ = l_Lake_Job_add___redArg(v_self_2781_, v_other_2782_);
return v___x_2783_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object* v___x_2784_, lean_object* v_rx_2785_, lean_object* v_ry_2786_){
_start:
{
lean_object* v___y_2788_; lean_object* v___y_2789_; lean_object* v___y_2793_; lean_object* v___y_2794_; 
if (lean_obj_tag(v_rx_2785_) == 0)
{
if (lean_obj_tag(v_ry_2786_) == 0)
{
lean_object* v_a_2796_; lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2806_; 
lean_dec(v___x_2784_);
v_a_2796_ = lean_ctor_get(v_rx_2785_, 1);
lean_inc(v_a_2796_);
lean_dec_ref_known(v_rx_2785_, 2);
v_a_2797_ = lean_ctor_get(v_ry_2786_, 1);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_ry_2786_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v_ry_2786_, 0);
lean_dec(v_unused_2807_);
v___x_2799_ = v_ry_2786_;
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v_ry_2786_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2806_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2801_ = lean_box(0);
v___x_2802_ = l_Lake_JobState_merge(v_a_2796_, v_a_2797_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 1, v___x_2802_);
lean_ctor_set(v___x_2799_, 0, v___x_2801_);
v___x_2804_ = v___x_2799_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2801_);
lean_ctor_set(v_reuseFailAlloc_2805_, 1, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
else
{
lean_object* v_a_2808_; 
v_a_2808_ = lean_ctor_get(v_rx_2785_, 1);
lean_inc(v_a_2808_);
lean_dec_ref_known(v_rx_2785_, 2);
v___y_2793_ = v_ry_2786_;
v___y_2794_ = v_a_2808_;
goto v___jp_2792_;
}
}
else
{
lean_object* v_a_2809_; 
v_a_2809_ = lean_ctor_get(v_rx_2785_, 1);
lean_inc(v_a_2809_);
lean_dec_ref(v_rx_2785_);
v___y_2793_ = v_ry_2786_;
v___y_2794_ = v_a_2809_;
goto v___jp_2792_;
}
v___jp_2787_:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = l_Lake_JobState_merge(v___y_2788_, v___y_2789_);
v___x_2791_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2791_, 0, v___x_2784_);
lean_ctor_set(v___x_2791_, 1, v___x_2790_);
return v___x_2791_;
}
v___jp_2792_:
{
lean_object* v_a_2795_; 
v_a_2795_ = lean_ctor_get(v___y_2793_, 1);
lean_inc(v_a_2795_);
lean_dec_ref(v___y_2793_);
v___y_2788_ = v___y_2794_;
v___y_2789_ = v_a_2795_;
goto v___jp_2787_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object* v_other_2810_, lean_object* v___x_2811_, uint8_t v___x_2812_, lean_object* v_rx_2813_){
_start:
{
lean_object* v_task_2814_; lean_object* v___f_2815_; lean_object* v___x_2816_; 
v_task_2814_ = lean_ctor_get(v_other_2810_, 0);
lean_inc_ref(v_task_2814_);
lean_dec_ref(v_other_2810_);
lean_inc(v___x_2811_);
v___f_2815_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2815_, 0, v___x_2811_);
lean_closure_set(v___f_2815_, 1, v_rx_2813_);
v___x_2816_ = lean_task_map(v___f_2815_, v_task_2814_, v___x_2811_, v___x_2812_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object* v_other_2817_, lean_object* v___x_2818_, lean_object* v___x_2819_, lean_object* v_rx_2820_){
_start:
{
uint8_t v___x_142__boxed_2821_; lean_object* v_res_2822_; 
v___x_142__boxed_2821_ = lean_unbox(v___x_2819_);
v_res_2822_ = l_Lake_Job_mix___redArg___lam__1(v_other_2817_, v___x_2818_, v___x_142__boxed_2821_, v_rx_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object* v_self_2823_, lean_object* v_other_2824_){
_start:
{
lean_object* v_task_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2840_; 
v_task_2825_ = lean_ctor_get(v_self_2823_, 0);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_self_2823_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; lean_object* v_unused_2842_; 
v_unused_2841_ = lean_ctor_get(v_self_2823_, 2);
lean_dec(v_unused_2841_);
v_unused_2842_ = lean_ctor_get(v_self_2823_, 1);
lean_dec(v_unused_2842_);
v___x_2827_ = v_self_2823_;
v_isShared_2828_ = v_isSharedCheck_2840_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_task_2825_);
lean_dec(v_self_2823_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2840_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; lean_object* v___x_2832_; lean_object* v___f_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; uint8_t v___x_2836_; lean_object* v___x_2838_; 
v___x_2829_ = l_Lake_instDataKindUnit;
v___x_2830_ = lean_unsigned_to_nat(0u);
v___x_2831_ = 1;
v___x_2832_ = lean_box(v___x_2831_);
v___f_2833_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2833_, 0, v_other_2824_);
lean_closure_set(v___f_2833_, 1, v___x_2830_);
lean_closure_set(v___f_2833_, 2, v___x_2832_);
v___x_2834_ = lean_task_bind(v_task_2825_, v___f_2833_, v___x_2830_, v___x_2831_);
v___x_2835_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2836_ = 0;
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 2, v___x_2835_);
lean_ctor_set(v___x_2827_, 1, v___x_2829_);
lean_ctor_set(v___x_2827_, 0, v___x_2834_);
v___x_2838_ = v___x_2827_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2834_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___x_2829_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v___x_2835_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
lean_ctor_set_uint8(v___x_2838_, sizeof(void*)*3, v___x_2836_);
return v___x_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object* v_00_u03b1_2843_, lean_object* v_00_u03b2_2844_, lean_object* v_self_2845_, lean_object* v_other_2846_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l_Lake_Job_mix___redArg(v_self_2845_, v_other_2846_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(lean_object* v_as_2848_, size_t v_i_2849_, size_t v_stop_2850_, lean_object* v_b_2851_){
_start:
{
uint8_t v___x_2852_; 
v___x_2852_ = lean_usize_dec_eq(v_i_2849_, v_stop_2850_);
if (v___x_2852_ == 0)
{
size_t v___x_2853_; size_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2853_ = ((size_t)1ULL);
v___x_2854_ = lean_usize_sub(v_i_2849_, v___x_2853_);
v___x_2855_ = lean_array_uget_borrowed(v_as_2848_, v___x_2854_);
lean_inc(v___x_2855_);
v___x_2856_ = l_Lake_Job_mix___redArg(v___x_2855_, v_b_2851_);
v_i_2849_ = v___x_2854_;
v_b_2851_ = v___x_2856_;
goto _start;
}
else
{
return v_b_2851_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2858_, lean_object* v_i_2859_, lean_object* v_stop_2860_, lean_object* v_b_2861_){
_start:
{
size_t v_i_boxed_2862_; size_t v_stop_boxed_2863_; lean_object* v_res_2864_; 
v_i_boxed_2862_ = lean_unbox_usize(v_i_2859_);
lean_dec(v_i_2859_);
v_stop_boxed_2863_ = lean_unbox_usize(v_stop_2860_);
lean_dec(v_stop_2860_);
v_res_2864_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2858_, v_i_boxed_2862_, v_stop_boxed_2863_, v_b_2861_);
lean_dec_ref(v_as_2858_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(lean_object* v_init_2865_, lean_object* v_l_2866_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; uint8_t v___x_2870_; 
v___x_2867_ = lean_array_mk(v_l_2866_);
v___x_2868_ = lean_array_get_size(v___x_2867_);
v___x_2869_ = lean_unsigned_to_nat(0u);
v___x_2870_ = lean_nat_dec_lt(v___x_2869_, v___x_2868_);
if (v___x_2870_ == 0)
{
lean_dec_ref(v___x_2867_);
return v_init_2865_;
}
else
{
size_t v___x_2871_; size_t v___x_2872_; lean_object* v___x_2873_; 
v___x_2871_ = lean_usize_of_nat(v___x_2868_);
v___x_2872_ = ((size_t)0ULL);
v___x_2873_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v___x_2867_, v___x_2871_, v___x_2872_, v_init_2865_);
lean_dec_ref(v___x_2867_);
return v___x_2873_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object* v_jobs_2874_, lean_object* v_traceCaption_2875_){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; uint8_t v___x_2880_; uint8_t v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2876_ = lean_box(0);
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_unsigned_to_nat(0u);
v___x_2879_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2880_ = 0;
v___x_2881_ = 0;
v___x_2882_ = l_Lake_BuildTrace_nil(v_traceCaption_2875_);
v___x_2883_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2883_, 0, v___x_2879_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
lean_ctor_set(v___x_2883_, 2, v___x_2878_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*3, v___x_2880_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*3 + 1, v___x_2881_);
lean_ctor_set_uint8(v___x_2883_, sizeof(void*)*3 + 2, v___x_2881_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2876_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = lean_task_pure(v___x_2884_);
v___x_2886_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2887_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2887_, 0, v___x_2885_);
lean_ctor_set(v___x_2887_, 1, v___x_2877_);
lean_ctor_set(v___x_2887_, 2, v___x_2886_);
lean_ctor_set_uint8(v___x_2887_, sizeof(void*)*3, v___x_2881_);
v___x_2888_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v___x_2887_, v_jobs_2874_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object* v_00_u03b1_2889_, lean_object* v_jobs_2890_, lean_object* v_traceCaption_2891_){
_start:
{
lean_object* v___x_2892_; 
v___x_2892_ = l_Lake_Job_mixList___redArg(v_jobs_2890_, v_traceCaption_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0(lean_object* v_00_u03b1_2893_, lean_object* v_init_2894_, lean_object* v_l_2895_){
_start:
{
lean_object* v___x_2896_; 
v___x_2896_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v_init_2894_, v_l_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(lean_object* v_00_u03b1_2897_, lean_object* v_as_2898_, size_t v_i_2899_, size_t v_stop_2900_, lean_object* v_b_2901_){
_start:
{
lean_object* v___x_2902_; 
v___x_2902_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2898_, v_i_2899_, v_stop_2900_, v_b_2901_);
return v___x_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2903_, lean_object* v_as_2904_, lean_object* v_i_2905_, lean_object* v_stop_2906_, lean_object* v_b_2907_){
_start:
{
size_t v_i_boxed_2908_; size_t v_stop_boxed_2909_; lean_object* v_res_2910_; 
v_i_boxed_2908_ = lean_unbox_usize(v_i_2905_);
lean_dec(v_i_2905_);
v_stop_boxed_2909_ = lean_unbox_usize(v_stop_2906_);
lean_dec(v_stop_2906_);
v_res_2910_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(v_00_u03b1_2903_, v_as_2904_, v_i_boxed_2908_, v_stop_boxed_2909_, v_b_2907_);
lean_dec_ref(v_as_2904_);
return v_res_2910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(lean_object* v_as_2911_, size_t v_i_2912_, size_t v_stop_2913_, lean_object* v_b_2914_){
_start:
{
uint8_t v___x_2915_; 
v___x_2915_ = lean_usize_dec_eq(v_i_2912_, v_stop_2913_);
if (v___x_2915_ == 0)
{
lean_object* v___x_2916_; lean_object* v___x_2917_; size_t v___x_2918_; size_t v___x_2919_; 
v___x_2916_ = lean_array_uget_borrowed(v_as_2911_, v_i_2912_);
lean_inc(v___x_2916_);
v___x_2917_ = l_Lake_Job_mix___redArg(v_b_2914_, v___x_2916_);
v___x_2918_ = ((size_t)1ULL);
v___x_2919_ = lean_usize_add(v_i_2912_, v___x_2918_);
v_i_2912_ = v___x_2919_;
v_b_2914_ = v___x_2917_;
goto _start;
}
else
{
return v_b_2914_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg___boxed(lean_object* v_as_2921_, lean_object* v_i_2922_, lean_object* v_stop_2923_, lean_object* v_b_2924_){
_start:
{
size_t v_i_boxed_2925_; size_t v_stop_boxed_2926_; lean_object* v_res_2927_; 
v_i_boxed_2925_ = lean_unbox_usize(v_i_2922_);
lean_dec(v_i_2922_);
v_stop_boxed_2926_ = lean_unbox_usize(v_stop_2923_);
lean_dec(v_stop_2923_);
v_res_2927_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2921_, v_i_boxed_2925_, v_stop_boxed_2926_, v_b_2924_);
lean_dec_ref(v_as_2921_);
return v_res_2927_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object* v_jobs_2928_, lean_object* v_traceCaption_2929_){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; uint8_t v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v___x_2930_ = lean_box(0);
v___x_2931_ = lean_box(0);
v___x_2932_ = lean_unsigned_to_nat(0u);
v___x_2933_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2934_ = 0;
v___x_2935_ = 0;
v___x_2936_ = l_Lake_BuildTrace_nil(v_traceCaption_2929_);
v___x_2937_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2937_, 0, v___x_2933_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
lean_ctor_set(v___x_2937_, 2, v___x_2932_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*3, v___x_2934_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*3 + 1, v___x_2935_);
lean_ctor_set_uint8(v___x_2937_, sizeof(void*)*3 + 2, v___x_2935_);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2930_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = lean_task_pure(v___x_2938_);
v___x_2940_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2941_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2941_, 0, v___x_2939_);
lean_ctor_set(v___x_2941_, 1, v___x_2931_);
lean_ctor_set(v___x_2941_, 2, v___x_2940_);
lean_ctor_set_uint8(v___x_2941_, sizeof(void*)*3, v___x_2935_);
v___x_2942_ = lean_array_get_size(v_jobs_2928_);
v___x_2943_ = lean_nat_dec_lt(v___x_2932_, v___x_2942_);
if (v___x_2943_ == 0)
{
return v___x_2941_;
}
else
{
size_t v___x_2944_; size_t v___x_2945_; lean_object* v___x_2946_; 
v___x_2944_ = ((size_t)0ULL);
v___x_2945_ = lean_usize_of_nat(v___x_2942_);
v___x_2946_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2928_, v___x_2944_, v___x_2945_, v___x_2941_);
return v___x_2946_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object* v_jobs_2947_, lean_object* v_traceCaption_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Lake_Job_mixArray___redArg(v_jobs_2947_, v_traceCaption_2948_);
lean_dec_ref(v_jobs_2947_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object* v_00_u03b1_2950_, lean_object* v_jobs_2951_, lean_object* v_traceCaption_2952_){
_start:
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lake_Job_mixArray___redArg(v_jobs_2951_, v_traceCaption_2952_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object* v_00_u03b1_2954_, lean_object* v_jobs_2955_, lean_object* v_traceCaption_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lake_Job_mixArray(v_00_u03b1_2954_, v_jobs_2955_, v_traceCaption_2956_);
lean_dec_ref(v_jobs_2955_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_object* v_00_u03b1_2958_, lean_object* v_as_2959_, size_t v_i_2960_, size_t v_stop_2961_, lean_object* v_b_2962_){
_start:
{
lean_object* v___x_2963_; 
v___x_2963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2959_, v_i_2960_, v_stop_2961_, v_b_2962_);
return v___x_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(lean_object* v_00_u03b1_2964_, lean_object* v_as_2965_, lean_object* v_i_2966_, lean_object* v_stop_2967_, lean_object* v_b_2968_){
_start:
{
size_t v_i_boxed_2969_; size_t v_stop_boxed_2970_; lean_object* v_res_2971_; 
v_i_boxed_2969_ = lean_unbox_usize(v_i_2966_);
lean_dec(v_i_2966_);
v_stop_boxed_2970_ = lean_unbox_usize(v_stop_2967_);
lean_dec(v_stop_2967_);
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(v_00_u03b1_2964_, v_as_2965_, v_i_boxed_2969_, v_stop_boxed_2970_, v_b_2968_);
lean_dec_ref(v_as_2965_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object* v___x_2972_, lean_object* v_rx_2973_, lean_object* v_ry_2974_){
_start:
{
lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2981_; lean_object* v___y_2982_; 
if (lean_obj_tag(v_rx_2973_) == 0)
{
if (lean_obj_tag(v_ry_2974_) == 0)
{
lean_object* v_a_2984_; lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3002_; 
lean_dec(v___x_2972_);
v_a_2984_ = lean_ctor_get(v_rx_2973_, 0);
v_a_2985_ = lean_ctor_get(v_rx_2973_, 1);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_rx_2973_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2987_ = v_rx_2973_;
v_isShared_2988_ = v_isSharedCheck_3002_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_inc(v_a_2984_);
lean_dec(v_rx_2973_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3002_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v_a_2989_; lean_object* v_a_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3001_; 
v_a_2989_ = lean_ctor_get(v_ry_2974_, 0);
v_a_2990_ = lean_ctor_get(v_ry_2974_, 1);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_ry_2974_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2992_ = v_ry_2974_;
v_isShared_2993_ = v_isSharedCheck_3001_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_a_2990_);
lean_inc(v_a_2989_);
lean_dec(v_ry_2974_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3001_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2995_; 
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 1);
lean_ctor_set(v___x_2987_, 1, v_a_2989_);
v___x_2995_ = v___x_2987_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_a_2984_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_a_2989_);
v___x_2995_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2996_ = l_Lake_JobState_merge(v_a_2985_, v_a_2990_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 1, v___x_2996_);
lean_ctor_set(v___x_2992_, 0, v___x_2995_);
v___x_2998_ = v___x_2992_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_2999_, 1, v___x_2996_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
else
{
lean_object* v_a_3003_; 
v_a_3003_ = lean_ctor_get(v_rx_2973_, 1);
lean_inc(v_a_3003_);
lean_dec_ref_known(v_rx_2973_, 2);
v___y_2981_ = v_ry_2974_;
v___y_2982_ = v_a_3003_;
goto v___jp_2980_;
}
}
else
{
lean_object* v_a_3004_; 
v_a_3004_ = lean_ctor_get(v_rx_2973_, 1);
lean_inc(v_a_3004_);
lean_dec_ref(v_rx_2973_);
v___y_2981_ = v_ry_2974_;
v___y_2982_ = v_a_3004_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object* v_b_3005_, lean_object* v___x_3006_, uint8_t v___x_3007_, lean_object* v_rx_3008_){
_start:
{
lean_object* v_task_3009_; lean_object* v___f_3010_; lean_object* v___x_3011_; 
v_task_3009_ = lean_ctor_get(v_b_3005_, 0);
lean_inc_ref(v_task_3009_);
lean_dec_ref(v_b_3005_);
lean_inc(v___x_3006_);
v___f_3010_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3010_, 0, v___x_3006_);
lean_closure_set(v___f_3010_, 1, v_rx_3008_);
v___x_3011_ = lean_task_map(v___f_3010_, v_task_3009_, v___x_3006_, v___x_3007_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_b_3012_, lean_object* v___x_3013_, lean_object* v___x_3014_, lean_object* v_rx_3015_){
_start:
{
uint8_t v___x_480__boxed_3016_; lean_object* v_res_3017_; 
v___x_480__boxed_3016_ = lean_unbox(v___x_3014_);
v_res_3017_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_3012_, v___x_3013_, v___x_480__boxed_3016_, v_rx_3015_);
return v_res_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(lean_object* v_as_3018_, size_t v_i_3019_, size_t v_stop_3020_, lean_object* v_b_3021_){
_start:
{
uint8_t v___x_3022_; 
v___x_3022_ = lean_usize_dec_eq(v_i_3019_, v_stop_3020_);
if (v___x_3022_ == 0)
{
size_t v___x_3023_; size_t v___x_3024_; lean_object* v___x_3025_; lean_object* v_task_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3041_; 
v___x_3023_ = ((size_t)1ULL);
v___x_3024_ = lean_usize_sub(v_i_3019_, v___x_3023_);
v___x_3025_ = lean_array_uget(v_as_3018_, v___x_3024_);
v_task_3026_ = lean_ctor_get(v___x_3025_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3025_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; lean_object* v_unused_3043_; 
v_unused_3042_ = lean_ctor_get(v___x_3025_, 2);
lean_dec(v_unused_3042_);
v_unused_3043_ = lean_ctor_get(v___x_3025_, 1);
lean_dec(v_unused_3043_);
v___x_3028_ = v___x_3025_;
v_isShared_3029_ = v_isSharedCheck_3041_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_task_3026_);
lean_dec(v___x_3025_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3041_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; lean_object* v___x_3033_; lean_object* v___f_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
v___x_3030_ = lean_box(0);
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = 1;
v___x_3033_ = lean_box(v___x_3032_);
v___f_3034_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3034_, 0, v_b_3021_);
lean_closure_set(v___f_3034_, 1, v___x_3031_);
lean_closure_set(v___f_3034_, 2, v___x_3033_);
v___x_3035_ = lean_task_bind(v_task_3026_, v___f_3034_, v___x_3031_, v___x_3032_);
v___x_3036_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_3029_ == 0)
{
lean_ctor_set(v___x_3028_, 2, v___x_3036_);
lean_ctor_set(v___x_3028_, 1, v___x_3030_);
lean_ctor_set(v___x_3028_, 0, v___x_3035_);
v___x_3038_ = v___x_3028_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3040_, 1, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3040_, 2, v___x_3036_);
v___x_3038_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
lean_ctor_set_uint8(v___x_3038_, sizeof(void*)*3, v___x_3022_);
v_i_3019_ = v___x_3024_;
v_b_3021_ = v___x_3038_;
goto _start;
}
}
}
else
{
return v_b_3021_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object* v_as_3044_, lean_object* v_i_3045_, lean_object* v_stop_3046_, lean_object* v_b_3047_){
_start:
{
size_t v_i_boxed_3048_; size_t v_stop_boxed_3049_; lean_object* v_res_3050_; 
v_i_boxed_3048_ = lean_unbox_usize(v_i_3045_);
lean_dec(v_i_3045_);
v_stop_boxed_3049_ = lean_unbox_usize(v_stop_3046_);
lean_dec(v_stop_3046_);
v_res_3050_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_3044_, v_i_boxed_3048_, v_stop_boxed_3049_, v_b_3047_);
lean_dec_ref(v_as_3044_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(lean_object* v_init_3051_, lean_object* v_l_3052_){
_start:
{
lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; uint8_t v___x_3056_; 
v___x_3053_ = lean_array_mk(v_l_3052_);
v___x_3054_ = lean_array_get_size(v___x_3053_);
v___x_3055_ = lean_unsigned_to_nat(0u);
v___x_3056_ = lean_nat_dec_lt(v___x_3055_, v___x_3054_);
if (v___x_3056_ == 0)
{
lean_dec_ref(v___x_3053_);
return v_init_3051_;
}
else
{
size_t v___x_3057_; size_t v___x_3058_; lean_object* v___x_3059_; 
v___x_3057_ = lean_usize_of_nat(v___x_3054_);
v___x_3058_ = ((size_t)0ULL);
v___x_3059_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v___x_3053_, v___x_3057_, v___x_3058_, v_init_3051_);
lean_dec_ref(v___x_3053_);
return v___x_3059_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object* v_jobs_3060_, lean_object* v_traceCaption_3061_){
_start:
{
lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___x_3066_; uint8_t v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3062_ = lean_box(0);
v___x_3063_ = lean_box(0);
v___x_3064_ = lean_unsigned_to_nat(0u);
v___x_3065_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3066_ = 0;
v___x_3067_ = 0;
v___x_3068_ = l_Lake_BuildTrace_nil(v_traceCaption_3061_);
v___x_3069_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3069_, 0, v___x_3065_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
lean_ctor_set(v___x_3069_, 2, v___x_3064_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3, v___x_3066_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 1, v___x_3067_);
lean_ctor_set_uint8(v___x_3069_, sizeof(void*)*3 + 2, v___x_3067_);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3062_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
v___x_3071_ = lean_task_pure(v___x_3070_);
v___x_3072_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3073_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3073_, 0, v___x_3071_);
lean_ctor_set(v___x_3073_, 1, v___x_3063_);
lean_ctor_set(v___x_3073_, 2, v___x_3072_);
lean_ctor_set_uint8(v___x_3073_, sizeof(void*)*3, v___x_3067_);
v___x_3074_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v___x_3073_, v_jobs_3060_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object* v_00_u03b1_3075_, lean_object* v_jobs_3076_, lean_object* v_traceCaption_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Lake_Job_collectList___redArg(v_jobs_3076_, v_traceCaption_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0(lean_object* v_00_u03b1_3079_, lean_object* v_init_3080_, lean_object* v_l_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v_init_3080_, v_l_3081_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_object* v_00_u03b1_3083_, lean_object* v_as_3084_, size_t v_i_3085_, size_t v_stop_3086_, lean_object* v_b_3087_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_3084_, v_i_3085_, v_stop_3086_, v_b_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3089_, lean_object* v_as_3090_, lean_object* v_i_3091_, lean_object* v_stop_3092_, lean_object* v_b_3093_){
_start:
{
size_t v_i_boxed_3094_; size_t v_stop_boxed_3095_; lean_object* v_res_3096_; 
v_i_boxed_3094_ = lean_unbox_usize(v_i_3091_);
lean_dec(v_i_3091_);
v_stop_boxed_3095_ = lean_unbox_usize(v_stop_3092_);
lean_dec(v_stop_3092_);
v_res_3096_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(v_00_u03b1_3089_, v_as_3090_, v_i_boxed_3094_, v_stop_boxed_3095_, v_b_3093_);
lean_dec_ref(v_as_3090_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object* v___x_3097_, lean_object* v_rx_3098_, lean_object* v_ry_3099_){
_start:
{
lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3106_; lean_object* v___y_3107_; 
if (lean_obj_tag(v_rx_3098_) == 0)
{
if (lean_obj_tag(v_ry_3099_) == 0)
{
lean_object* v_a_3109_; lean_object* v_a_3110_; lean_object* v_a_3111_; lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3121_; 
lean_dec(v___x_3097_);
v_a_3109_ = lean_ctor_get(v_rx_3098_, 0);
lean_inc(v_a_3109_);
v_a_3110_ = lean_ctor_get(v_rx_3098_, 1);
lean_inc(v_a_3110_);
lean_dec_ref_known(v_rx_3098_, 2);
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
v___x_3116_ = lean_array_push(v_a_3109_, v_a_3111_);
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
v_a_3122_ = lean_ctor_get(v_rx_3098_, 1);
lean_inc(v_a_3122_);
lean_dec_ref_known(v_rx_3098_, 2);
v___y_3106_ = v_ry_3099_;
v___y_3107_ = v_a_3122_;
goto v___jp_3105_;
}
}
else
{
lean_object* v_a_3123_; 
v_a_3123_ = lean_ctor_get(v_rx_3098_, 1);
lean_inc(v_a_3123_);
lean_dec_ref(v_rx_3098_);
v___y_3106_ = v_ry_3099_;
v___y_3107_ = v_a_3123_;
goto v___jp_3105_;
}
v___jp_3100_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = l_Lake_JobState_merge(v___y_3101_, v___y_3102_);
v___x_3104_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3104_, 0, v___x_3097_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object* v___x_3124_, lean_object* v___x_3125_, uint8_t v___x_3126_, lean_object* v_rx_3127_){
_start:
{
lean_object* v_task_3128_; lean_object* v___f_3129_; lean_object* v___x_3130_; 
v_task_3128_ = lean_ctor_get(v___x_3124_, 0);
lean_inc_ref(v_task_3128_);
lean_dec_ref(v___x_3124_);
lean_inc(v___x_3125_);
v___f_3129_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3129_, 0, v___x_3125_);
lean_closure_set(v___f_3129_, 1, v_rx_3127_);
v___x_3130_ = lean_task_map(v___f_3129_, v_task_3128_, v___x_3125_, v___x_3126_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object* v___x_3131_, lean_object* v___x_3132_, lean_object* v___x_3133_, lean_object* v_rx_3134_){
_start:
{
uint8_t v___x_413__boxed_3135_; lean_object* v_res_3136_; 
v___x_413__boxed_3135_ = lean_unbox(v___x_3133_);
v_res_3136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_3131_, v___x_3132_, v___x_413__boxed_3135_, v_rx_3134_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(lean_object* v_as_3137_, size_t v_i_3138_, size_t v_stop_3139_, lean_object* v_b_3140_){
_start:
{
uint8_t v___x_3141_; 
v___x_3141_ = lean_usize_dec_eq(v_i_3138_, v_stop_3139_);
if (v___x_3141_ == 0)
{
lean_object* v_task_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3160_; 
v_task_3142_ = lean_ctor_get(v_b_3140_, 0);
v_isSharedCheck_3160_ = !lean_is_exclusive(v_b_3140_);
if (v_isSharedCheck_3160_ == 0)
{
lean_object* v_unused_3161_; lean_object* v_unused_3162_; 
v_unused_3161_ = lean_ctor_get(v_b_3140_, 2);
lean_dec(v_unused_3161_);
v_unused_3162_ = lean_ctor_get(v_b_3140_, 1);
lean_dec(v_unused_3162_);
v___x_3144_ = v_b_3140_;
v_isShared_3145_ = v_isSharedCheck_3160_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_task_3142_);
lean_dec(v_b_3140_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3160_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___f_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3155_; 
v___x_3146_ = lean_box(0);
v___x_3147_ = lean_array_uget_borrowed(v_as_3137_, v_i_3138_);
v___x_3148_ = lean_unsigned_to_nat(0u);
v___x_3149_ = 1;
v___x_3150_ = lean_box(v___x_3149_);
lean_inc(v___x_3147_);
v___f_3151_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3151_, 0, v___x_3147_);
lean_closure_set(v___f_3151_, 1, v___x_3148_);
lean_closure_set(v___f_3151_, 2, v___x_3150_);
v___x_3152_ = lean_task_bind(v_task_3142_, v___f_3151_, v___x_3148_, v___x_3149_);
v___x_3153_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 2, v___x_3153_);
lean_ctor_set(v___x_3144_, 1, v___x_3146_);
lean_ctor_set(v___x_3144_, 0, v___x_3152_);
v___x_3155_ = v___x_3144_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3159_; 
v_reuseFailAlloc_3159_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3159_, 0, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3159_, 1, v___x_3146_);
lean_ctor_set(v_reuseFailAlloc_3159_, 2, v___x_3153_);
v___x_3155_ = v_reuseFailAlloc_3159_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
size_t v___x_3156_; size_t v___x_3157_; 
lean_ctor_set_uint8(v___x_3155_, sizeof(void*)*3, v___x_3141_);
v___x_3156_ = ((size_t)1ULL);
v___x_3157_ = lean_usize_add(v_i_3138_, v___x_3156_);
v_i_3138_ = v___x_3157_;
v_b_3140_ = v___x_3155_;
goto _start;
}
}
}
else
{
return v_b_3140_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(lean_object* v_as_3163_, lean_object* v_i_3164_, lean_object* v_stop_3165_, lean_object* v_b_3166_){
_start:
{
size_t v_i_boxed_3167_; size_t v_stop_boxed_3168_; lean_object* v_res_3169_; 
v_i_boxed_3167_ = lean_unbox_usize(v_i_3164_);
lean_dec(v_i_3164_);
v_stop_boxed_3168_ = lean_unbox_usize(v_stop_3165_);
lean_dec(v_stop_3165_);
v_res_3169_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3163_, v_i_boxed_3167_, v_stop_boxed_3168_, v_b_3166_);
lean_dec_ref(v_as_3163_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object* v_jobs_3170_, lean_object* v_traceCaption_3171_){
_start:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; uint8_t v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; uint8_t v___x_3185_; 
v___x_3172_ = lean_array_get_size(v_jobs_3170_);
v___x_3173_ = lean_mk_empty_array_with_capacity(v___x_3172_);
v___x_3174_ = lean_box(0);
v___x_3175_ = lean_unsigned_to_nat(0u);
v___x_3176_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3177_ = 0;
v___x_3178_ = 0;
v___x_3179_ = l_Lake_BuildTrace_nil(v_traceCaption_3171_);
v___x_3180_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3180_, 0, v___x_3176_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
lean_ctor_set(v___x_3180_, 2, v___x_3175_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*3, v___x_3177_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*3 + 1, v___x_3178_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*3 + 2, v___x_3178_);
v___x_3181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3173_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = lean_task_pure(v___x_3181_);
v___x_3183_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3184_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3184_, 0, v___x_3182_);
lean_ctor_set(v___x_3184_, 1, v___x_3174_);
lean_ctor_set(v___x_3184_, 2, v___x_3183_);
lean_ctor_set_uint8(v___x_3184_, sizeof(void*)*3, v___x_3178_);
v___x_3185_ = lean_nat_dec_lt(v___x_3175_, v___x_3172_);
if (v___x_3185_ == 0)
{
return v___x_3184_;
}
else
{
size_t v___x_3186_; size_t v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = ((size_t)0ULL);
v___x_3187_ = lean_usize_of_nat(v___x_3172_);
v___x_3188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_3170_, v___x_3186_, v___x_3187_, v___x_3184_);
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object* v_jobs_3189_, lean_object* v_traceCaption_3190_){
_start:
{
lean_object* v_res_3191_; 
v_res_3191_ = l_Lake_Job_collectArray___redArg(v_jobs_3189_, v_traceCaption_3190_);
lean_dec_ref(v_jobs_3189_);
return v_res_3191_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object* v_00_u03b1_3192_, lean_object* v_jobs_3193_, lean_object* v_traceCaption_3194_){
_start:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lake_Job_collectArray___redArg(v_jobs_3193_, v_traceCaption_3194_);
return v___x_3195_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object* v_00_u03b1_3196_, lean_object* v_jobs_3197_, lean_object* v_traceCaption_3198_){
_start:
{
lean_object* v_res_3199_; 
v_res_3199_ = l_Lake_Job_collectArray(v_00_u03b1_3196_, v_jobs_3197_, v_traceCaption_3198_);
lean_dec_ref(v_jobs_3197_);
return v_res_3199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_object* v_00_u03b1_3200_, lean_object* v_as_3201_, size_t v_i_3202_, size_t v_stop_3203_, lean_object* v_b_3204_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3201_, v_i_3202_, v_stop_3203_, v_b_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(lean_object* v_00_u03b1_3206_, lean_object* v_as_3207_, lean_object* v_i_3208_, lean_object* v_stop_3209_, lean_object* v_b_3210_){
_start:
{
size_t v_i_boxed_3211_; size_t v_stop_boxed_3212_; lean_object* v_res_3213_; 
v_i_boxed_3211_ = lean_unbox_usize(v_i_3208_);
lean_dec(v_i_3208_);
v_stop_boxed_3212_ = lean_unbox_usize(v_stop_3209_);
lean_dec(v_stop_3209_);
v_res_3213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(v_00_u03b1_3206_, v_as_3207_, v_i_boxed_3211_, v_stop_boxed_3212_, v_b_3210_);
lean_dec_ref(v_as_3207_);
return v_res_3213_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg(){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = lean_box(0);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg___boxed(lean_object* v___dummy_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg();
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(lean_object* v_00_u03b1_3218_, lean_object* v_inst_3219_){
_start:
{
lean_object* v___x_3220_; 
v___x_3220_ = lean_box(0);
return v___x_3220_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0(lean_object* v___x_3221_, lean_object* v_rx_3222_, lean_object* v_i_3223_, lean_object* v_ry_3224_){
_start:
{
lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3231_; lean_object* v___y_3232_; 
if (lean_obj_tag(v_rx_3222_) == 0)
{
if (lean_obj_tag(v_ry_3224_) == 0)
{
lean_object* v_a_3234_; lean_object* v_a_3235_; lean_object* v_a_3236_; lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3246_; 
lean_dec(v___x_3221_);
v_a_3234_ = lean_ctor_get(v_rx_3222_, 0);
lean_inc(v_a_3234_);
v_a_3235_ = lean_ctor_get(v_rx_3222_, 1);
lean_inc(v_a_3235_);
lean_dec_ref_known(v_rx_3222_, 2);
v_a_3236_ = lean_ctor_get(v_ry_3224_, 0);
v_a_3237_ = lean_ctor_get(v_ry_3224_, 1);
v_isSharedCheck_3246_ = !lean_is_exclusive(v_ry_3224_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3239_ = v_ry_3224_;
v_isShared_3240_ = v_isSharedCheck_3246_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_inc(v_a_3236_);
lean_dec(v_ry_3224_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3246_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3241_ = lean_array_fset(v_a_3234_, v_i_3223_, v_a_3236_);
v___x_3242_ = l_Lake_JobState_merge(v_a_3235_, v_a_3237_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 1, v___x_3242_);
lean_ctor_set(v___x_3239_, 0, v___x_3241_);
v___x_3244_ = v___x_3239_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
else
{
lean_object* v_a_3247_; 
v_a_3247_ = lean_ctor_get(v_rx_3222_, 1);
lean_inc(v_a_3247_);
lean_dec_ref_known(v_rx_3222_, 2);
v___y_3231_ = v_ry_3224_;
v___y_3232_ = v_a_3247_;
goto v___jp_3230_;
}
}
else
{
lean_object* v_a_3248_; 
v_a_3248_ = lean_ctor_get(v_rx_3222_, 1);
lean_inc(v_a_3248_);
lean_dec_ref(v_rx_3222_);
v___y_3231_ = v_ry_3224_;
v___y_3232_ = v_a_3248_;
goto v___jp_3230_;
}
v___jp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = l_Lake_JobState_merge(v___y_3226_, v___y_3227_);
v___x_3229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3221_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
return v___x_3229_;
}
v___jp_3230_:
{
lean_object* v_a_3233_; 
v_a_3233_ = lean_ctor_get(v___y_3231_, 1);
lean_inc(v_a_3233_);
lean_dec_ref(v___y_3231_);
v___y_3226_ = v___y_3232_;
v___y_3227_ = v_a_3233_;
goto v___jp_3225_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0___boxed(lean_object* v___x_3249_, lean_object* v_rx_3250_, lean_object* v_i_3251_, lean_object* v_ry_3252_){
_start:
{
lean_object* v_res_3253_; 
v_res_3253_ = l_Lake_Job_collectVector___redArg___lam__0(v___x_3249_, v_rx_3250_, v_i_3251_, v_ry_3252_);
lean_dec(v_i_3251_);
return v_res_3253_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1(lean_object* v___x_3254_, lean_object* v___x_3255_, lean_object* v_i_3256_, uint8_t v___x_3257_, lean_object* v_rx_3258_){
_start:
{
lean_object* v_task_3259_; lean_object* v___f_3260_; lean_object* v___x_3261_; 
v_task_3259_ = lean_ctor_get(v___x_3254_, 0);
lean_inc_ref(v_task_3259_);
lean_dec_ref(v___x_3254_);
lean_inc(v___x_3255_);
v___f_3260_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3260_, 0, v___x_3255_);
lean_closure_set(v___f_3260_, 1, v_rx_3258_);
lean_closure_set(v___f_3260_, 2, v_i_3256_);
v___x_3261_ = lean_task_map(v___f_3260_, v_task_3259_, v___x_3255_, v___x_3257_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1___boxed(lean_object* v___x_3262_, lean_object* v___x_3263_, lean_object* v_i_3264_, lean_object* v___x_3265_, lean_object* v_rx_3266_){
_start:
{
uint8_t v___x_191__boxed_3267_; lean_object* v_res_3268_; 
v___x_191__boxed_3267_ = lean_unbox(v___x_3265_);
v_res_3268_ = l_Lake_Job_collectVector___redArg___lam__1(v___x_3262_, v___x_3263_, v_i_3264_, v___x_191__boxed_3267_, v_rx_3266_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2(lean_object* v_jobs_3269_, lean_object* v___x_3270_, lean_object* v_i_3271_, lean_object* v_h_3272_, lean_object* v_job_3273_){
_start:
{
lean_object* v_task_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3289_; 
v_task_3274_ = lean_ctor_get(v_job_3273_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_job_3273_);
if (v_isSharedCheck_3289_ == 0)
{
lean_object* v_unused_3290_; lean_object* v_unused_3291_; 
v_unused_3290_ = lean_ctor_get(v_job_3273_, 2);
lean_dec(v_unused_3290_);
v_unused_3291_ = lean_ctor_get(v_job_3273_, 1);
lean_dec(v_unused_3291_);
v___x_3276_ = v_job_3273_;
v_isShared_3277_ = v_isSharedCheck_3289_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_task_3274_);
lean_dec(v_job_3273_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3289_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3278_; lean_object* v___x_3279_; uint8_t v___x_3280_; lean_object* v___x_3281_; lean_object* v___f_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; uint8_t v___x_3285_; lean_object* v___x_3287_; 
v___x_3278_ = lean_array_fget_borrowed(v_jobs_3269_, v_i_3271_);
v___x_3279_ = lean_unsigned_to_nat(0u);
v___x_3280_ = 1;
v___x_3281_ = lean_box(v___x_3280_);
lean_inc(v___x_3278_);
v___f_3282_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3282_, 0, v___x_3278_);
lean_closure_set(v___f_3282_, 1, v___x_3279_);
lean_closure_set(v___f_3282_, 2, v_i_3271_);
lean_closure_set(v___f_3282_, 3, v___x_3281_);
v___x_3283_ = lean_task_bind(v_task_3274_, v___f_3282_, v___x_3279_, v___x_3280_);
v___x_3284_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3285_ = 0;
if (v_isShared_3277_ == 0)
{
lean_ctor_set(v___x_3276_, 2, v___x_3284_);
lean_ctor_set(v___x_3276_, 1, v___x_3270_);
lean_ctor_set(v___x_3276_, 0, v___x_3283_);
v___x_3287_ = v___x_3276_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3283_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v___x_3270_);
lean_ctor_set(v_reuseFailAlloc_3288_, 2, v___x_3284_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
lean_ctor_set_uint8(v___x_3287_, sizeof(void*)*3, v___x_3285_);
return v___x_3287_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2___boxed(lean_object* v_jobs_3292_, lean_object* v___x_3293_, lean_object* v_i_3294_, lean_object* v_h_3295_, lean_object* v_job_3296_){
_start:
{
lean_object* v_res_3297_; 
v_res_3297_ = l_Lake_Job_collectVector___redArg___lam__2(v_jobs_3292_, v___x_3293_, v_i_3294_, v_h_3295_, v_job_3296_);
lean_dec_ref(v_jobs_3292_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg(lean_object* v_n_3298_, lean_object* v_jobs_3299_, lean_object* v_traceCaption_3300_){
_start:
{
lean_object* v_placeholder_3301_; lean_object* v___x_3302_; lean_object* v___f_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; uint8_t v___x_3307_; uint8_t v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
v_placeholder_3301_ = lean_box(0);
v___x_3302_ = lean_box(0);
v___f_3303_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3303_, 0, v_jobs_3299_);
lean_closure_set(v___f_3303_, 1, v___x_3302_);
lean_inc_n(v_n_3298_, 2);
v___x_3304_ = lean_mk_array(v_n_3298_, v_placeholder_3301_);
v___x_3305_ = lean_unsigned_to_nat(0u);
v___x_3306_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3307_ = 0;
v___x_3308_ = 0;
v___x_3309_ = l_Lake_BuildTrace_nil(v_traceCaption_3300_);
v___x_3310_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3310_, 0, v___x_3306_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
lean_ctor_set(v___x_3310_, 2, v___x_3305_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*3, v___x_3307_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*3 + 1, v___x_3308_);
lean_ctor_set_uint8(v___x_3310_, sizeof(void*)*3 + 2, v___x_3308_);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3304_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = lean_task_pure(v___x_3311_);
v___x_3313_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3314_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3302_);
lean_ctor_set(v___x_3314_, 2, v___x_3313_);
lean_ctor_set_uint8(v___x_3314_, sizeof(void*)*3, v___x_3308_);
v___x_3315_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3298_, v___f_3303_, v_n_3298_, lean_box(0), v___x_3314_);
lean_dec(v_n_3298_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector(lean_object* v_n_3316_, lean_object* v_00_u03b1_3317_, lean_object* v_inst_3318_, lean_object* v_jobs_3319_, lean_object* v_traceCaption_3320_){
_start:
{
lean_object* v___x_3321_; 
v___x_3321_ = l_Lake_Job_collectVector___redArg(v_n_3316_, v_jobs_3319_, v_traceCaption_3320_);
return v___x_3321_;
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
