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
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lake_instMonadStateOfJobStateJobM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
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
v___x_92_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
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
v___x_98_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_98_, 0, lean_box(0));
lean_closure_set(v___x_98_, 1, v___x_95_);
v___f_99_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_99_, 0, v___f_96_);
lean_closure_set(v___f_99_, 1, v___f_88_);
v___f_100_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_100_, 0, v___f_97_);
lean_closure_set(v___f_100_, 1, v___f_88_);
v___x_101_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
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
uint8_t v_action_131_; uint8_t v_wantsRebuild_132_; uint8_t v_canceled_133_; lean_object* v_trace_134_; lean_object* v_buildTime_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_144_; 
v_action_131_ = lean_ctor_get_uint8(v___y_129_, sizeof(void*)*3);
v_wantsRebuild_132_ = lean_ctor_get_uint8(v___y_129_, sizeof(void*)*3 + 1);
v_canceled_133_ = lean_ctor_get_uint8(v___y_129_, sizeof(void*)*3 + 2);
v_trace_134_ = lean_ctor_get(v___y_129_, 1);
v_buildTime_135_ = lean_ctor_get(v___y_129_, 2);
v_isSharedCheck_144_ = !lean_is_exclusive(v___y_129_);
if (v_isSharedCheck_144_ == 0)
{
lean_object* v_unused_145_; 
v_unused_145_ = lean_ctor_get(v___y_129_, 0);
lean_dec(v_unused_145_);
v___x_137_ = v___y_129_;
v_isShared_138_ = v_isSharedCheck_144_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_buildTime_135_);
lean_inc(v_trace_134_);
lean_dec(v___y_129_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_144_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v___x_139_; lean_object* v___x_141_; 
v___x_139_ = lean_box(0);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v_log_123_);
v___x_141_ = v___x_137_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_log_123_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_trace_134_);
lean_ctor_set(v_reuseFailAlloc_143_, 2, v_buildTime_135_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, sizeof(void*)*3, v_action_131_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, sizeof(void*)*3 + 1, v_wantsRebuild_132_);
lean_ctor_set_uint8(v_reuseFailAlloc_143_, sizeof(void*)*3 + 2, v_canceled_133_);
v___x_141_ = v_reuseFailAlloc_143_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
lean_object* v___x_142_; 
v___x_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_139_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
return v___x_142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1___boxed(lean_object* v_log_146_, lean_object* v___y_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_, lean_object* v___y_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lake_instMonadStateOfLogJobM___lam__1(v_log_146_, v___y_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
lean_dec_ref(v___y_151_);
lean_dec(v___y_150_);
lean_dec(v___y_149_);
lean_dec(v___y_148_);
lean_dec_ref(v___y_147_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2(lean_object* v_00_u03b1_155_, lean_object* v_f_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_){
_start:
{
lean_object* v_log_164_; uint8_t v_action_165_; uint8_t v_wantsRebuild_166_; uint8_t v_canceled_167_; lean_object* v_trace_168_; lean_object* v_buildTime_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_186_; 
v_log_164_ = lean_ctor_get(v___y_162_, 0);
v_action_165_ = lean_ctor_get_uint8(v___y_162_, sizeof(void*)*3);
v_wantsRebuild_166_ = lean_ctor_get_uint8(v___y_162_, sizeof(void*)*3 + 1);
v_canceled_167_ = lean_ctor_get_uint8(v___y_162_, sizeof(void*)*3 + 2);
v_trace_168_ = lean_ctor_get(v___y_162_, 1);
v_buildTime_169_ = lean_ctor_get(v___y_162_, 2);
v_isSharedCheck_186_ = !lean_is_exclusive(v___y_162_);
if (v_isSharedCheck_186_ == 0)
{
v___x_171_ = v___y_162_;
v_isShared_172_ = v_isSharedCheck_186_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_buildTime_169_);
lean_inc(v_trace_168_);
lean_inc(v_log_164_);
lean_dec(v___y_162_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_186_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v_fst_174_; lean_object* v_snd_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_185_; 
v___x_173_ = lean_apply_1(v_f_156_, v_log_164_);
v_fst_174_ = lean_ctor_get(v___x_173_, 0);
v_snd_175_ = lean_ctor_get(v___x_173_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_173_);
if (v_isSharedCheck_185_ == 0)
{
v___x_177_ = v___x_173_;
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_snd_175_);
lean_inc(v_fst_174_);
lean_dec(v___x_173_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_185_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 0, v_snd_175_);
v___x_180_ = v___x_171_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_snd_175_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v_trace_168_);
lean_ctor_set(v_reuseFailAlloc_184_, 2, v_buildTime_169_);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, sizeof(void*)*3, v_action_165_);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, sizeof(void*)*3 + 1, v_wantsRebuild_166_);
lean_ctor_set_uint8(v_reuseFailAlloc_184_, sizeof(void*)*3 + 2, v_canceled_167_);
v___x_180_ = v_reuseFailAlloc_184_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
lean_object* v___x_182_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 1, v___x_180_);
v___x_182_ = v___x_177_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_fst_174_);
lean_ctor_set(v_reuseFailAlloc_183_, 1, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2___boxed(lean_object* v_00_u03b1_187_, lean_object* v_f_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lake_instMonadStateOfLogJobM___lam__2(v_00_u03b1_187_, v_f_188_, v___y_189_, v___y_190_, v___y_191_, v___y_192_, v___y_193_, v___y_194_);
lean_dec_ref(v___y_193_);
lean_dec(v___y_192_);
lean_dec(v___y_191_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0(lean_object* v_00_u03b1_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_){
_start:
{
lean_object* v_log_217_; uint8_t v_action_218_; uint8_t v_wantsRebuild_219_; uint8_t v_canceled_220_; lean_object* v_trace_221_; lean_object* v_buildTime_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_234_; 
v_log_217_ = lean_ctor_get(v___y_215_, 0);
v_action_218_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*3);
v_wantsRebuild_219_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*3 + 1);
v_canceled_220_ = lean_ctor_get_uint8(v___y_215_, sizeof(void*)*3 + 2);
v_trace_221_ = lean_ctor_get(v___y_215_, 1);
v_buildTime_222_ = lean_ctor_get(v___y_215_, 2);
v_isSharedCheck_234_ = !lean_is_exclusive(v___y_215_);
if (v_isSharedCheck_234_ == 0)
{
v___x_224_ = v___y_215_;
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_buildTime_222_);
lean_inc(v_trace_221_);
lean_inc(v_log_217_);
lean_dec(v___y_215_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_234_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_231_; 
v___x_226_ = 3;
v___x_227_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_227_, 0, v___y_209_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1, v___x_226_);
v___x_228_ = lean_array_get_size(v_log_217_);
v___x_229_ = lean_array_push(v_log_217_, v___x_227_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 0, v___x_229_);
v___x_231_ = v___x_224_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_233_; 
v_reuseFailAlloc_233_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_233_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_233_, 1, v_trace_221_);
lean_ctor_set(v_reuseFailAlloc_233_, 2, v_buildTime_222_);
lean_ctor_set_uint8(v_reuseFailAlloc_233_, sizeof(void*)*3, v_action_218_);
lean_ctor_set_uint8(v_reuseFailAlloc_233_, sizeof(void*)*3 + 1, v_wantsRebuild_219_);
lean_ctor_set_uint8(v_reuseFailAlloc_233_, sizeof(void*)*3 + 2, v_canceled_220_);
v___x_231_ = v_reuseFailAlloc_233_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
lean_object* v___x_232_; 
v___x_232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_228_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0___boxed(lean_object* v_00_u03b1_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
lean_object* v_res_244_; 
v_res_244_ = l_Lake_instMonadErrorJobM___lam__0(v_00_u03b1_235_, v___y_236_, v___y_237_, v___y_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec(v___y_240_);
lean_dec(v___y_239_);
lean_dec(v___y_238_);
lean_dec_ref(v___y_237_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0(lean_object* v_00_u03b1_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v_log_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_log_255_ = lean_ctor_get(v___y_253_, 0);
v___x_256_ = lean_array_get_size(v_log_255_);
v___x_257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set(v___x_257_, 1, v___y_253_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0___boxed(lean_object* v_00_u03b1_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lake_instAlternativeJobM___lam__0(v_00_u03b1_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1(lean_object* v_00_u03b1_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___x_277_; 
lean_inc_ref(v___y_274_);
lean_inc(v___y_273_);
lean_inc(v___y_272_);
lean_inc(v___y_271_);
lean_inc_ref(v___y_270_);
v___x_277_ = lean_apply_7(v___y_268_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_, lean_box(0));
if (lean_obj_tag(v___x_277_) == 0)
{
lean_dec_ref(v___y_270_);
lean_dec_ref(v___y_269_);
return v___x_277_;
}
else
{
lean_object* v_a_278_; lean_object* v_a_279_; lean_object* v_log_280_; uint8_t v_action_281_; uint8_t v_wantsRebuild_282_; uint8_t v_canceled_283_; lean_object* v_trace_284_; lean_object* v_buildTime_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_295_; 
v_a_278_ = lean_ctor_get(v___x_277_, 1);
lean_inc(v_a_278_);
v_a_279_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_a_279_);
lean_dec_ref_known(v___x_277_, 2);
v_log_280_ = lean_ctor_get(v_a_278_, 0);
v_action_281_ = lean_ctor_get_uint8(v_a_278_, sizeof(void*)*3);
v_wantsRebuild_282_ = lean_ctor_get_uint8(v_a_278_, sizeof(void*)*3 + 1);
v_canceled_283_ = lean_ctor_get_uint8(v_a_278_, sizeof(void*)*3 + 2);
v_trace_284_ = lean_ctor_get(v_a_278_, 1);
v_buildTime_285_ = lean_ctor_get(v_a_278_, 2);
v_isSharedCheck_295_ = !lean_is_exclusive(v_a_278_);
if (v_isSharedCheck_295_ == 0)
{
v___x_287_ = v_a_278_;
v_isShared_288_ = v_isSharedCheck_295_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_buildTime_285_);
lean_inc(v_trace_284_);
lean_inc(v_log_280_);
lean_dec(v_a_278_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_295_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_291_; 
v___x_289_ = l_Array_shrink___redArg(v_log_280_, v_a_279_);
lean_dec(v_a_279_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 0, v___x_289_);
v___x_291_ = v___x_287_;
goto v_reusejp_290_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_289_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_trace_284_);
lean_ctor_set(v_reuseFailAlloc_294_, 2, v_buildTime_285_);
lean_ctor_set_uint8(v_reuseFailAlloc_294_, sizeof(void*)*3, v_action_281_);
lean_ctor_set_uint8(v_reuseFailAlloc_294_, sizeof(void*)*3 + 1, v_wantsRebuild_282_);
lean_ctor_set_uint8(v_reuseFailAlloc_294_, sizeof(void*)*3 + 2, v_canceled_283_);
v___x_291_ = v_reuseFailAlloc_294_;
goto v_reusejp_290_;
}
v_reusejp_290_:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_box(0);
lean_inc_ref(v___y_274_);
lean_inc(v___y_273_);
lean_inc(v___y_272_);
lean_inc(v___y_271_);
v___x_293_ = lean_apply_8(v___y_269_, v___x_292_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_, v___x_291_, lean_box(0));
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1___boxed(lean_object* v_00_u03b1_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v_res_306_; 
v_res_306_ = l_Lake_instAlternativeJobM___lam__1(v_00_u03b1_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_);
lean_dec_ref(v___y_303_);
lean_dec(v___y_302_);
lean_dec(v___y_301_);
lean_dec(v___y_300_);
return v_res_306_;
}
}
static lean_object* _init_l_Lake_instAlternativeJobM(void){
_start:
{
lean_object* v___x_309_; lean_object* v_toApplicative_310_; lean_object* v_toBind_311_; lean_object* v_toFunctor_312_; lean_object* v_toPure_313_; lean_object* v___f_314_; lean_object* v___f_315_; lean_object* v___f_316_; lean_object* v___f_317_; lean_object* v___x_318_; lean_object* v___f_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v_toApplicative_327_; lean_object* v___f_328_; lean_object* v___f_329_; lean_object* v___x_330_; 
v___x_309_ = l_instMonadBaseIO;
v_toApplicative_310_ = lean_ctor_get(v___x_309_, 0);
v_toBind_311_ = lean_ctor_get(v___x_309_, 1);
v_toFunctor_312_ = lean_ctor_get(v_toApplicative_310_, 0);
v_toPure_313_ = lean_ctor_get(v_toApplicative_310_, 1);
lean_inc_n(v_toBind_311_, 3);
lean_inc_n(v_toPure_313_, 5);
v___f_314_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_314_, 0, v_toPure_313_);
lean_closure_set(v___f_314_, 1, v_toBind_311_);
v___f_315_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_315_, 0, v_toPure_313_);
lean_closure_set(v___f_315_, 1, v_toBind_311_);
lean_inc_ref(v___f_314_);
v___f_316_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_316_, 0, v_toPure_313_);
lean_closure_set(v___f_316_, 1, v___f_314_);
lean_inc_ref_n(v_toFunctor_312_, 2);
v___f_317_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_317_, 0, v_toFunctor_312_);
lean_closure_set(v___f_317_, 1, v_toPure_313_);
lean_closure_set(v___f_317_, 2, v_toBind_311_);
v___x_318_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_312_);
v___f_319_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_319_, 0, v_toPure_313_);
v___x_320_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___f_319_);
lean_ctor_set(v___x_320_, 2, v___f_317_);
lean_ctor_set(v___x_320_, 3, v___f_316_);
lean_ctor_set(v___x_320_, 4, v___f_315_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___f_314_);
v___x_322_ = l_ReaderT_instMonad___redArg(v___x_321_);
v___x_323_ = l_StateRefT_x27_instMonad___redArg(v___x_322_);
v___x_324_ = l_ReaderT_instMonad___redArg(v___x_323_);
v___x_325_ = l_ReaderT_instMonad___redArg(v___x_324_);
v___x_326_ = l_Lake_EquipT_instMonad___redArg(v___x_325_);
v_toApplicative_327_ = lean_ctor_get(v___x_326_, 0);
lean_inc_ref(v_toApplicative_327_);
lean_dec_ref(v___x_326_);
v___f_328_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__0));
v___f_329_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__1));
v___x_330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_330_, 0, v_toApplicative_327_);
lean_ctor_set(v___x_330_, 1, v___f_328_);
lean_ctor_set(v___x_330_, 2, v___f_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0(lean_object* v_00_u03b1_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_){
_start:
{
lean_object* v_log_340_; uint8_t v_action_341_; uint8_t v_wantsRebuild_342_; uint8_t v_canceled_343_; lean_object* v_trace_344_; lean_object* v_buildTime_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_374_; 
v_log_340_ = lean_ctor_get(v___y_338_, 0);
v_action_341_ = lean_ctor_get_uint8(v___y_338_, sizeof(void*)*3);
v_wantsRebuild_342_ = lean_ctor_get_uint8(v___y_338_, sizeof(void*)*3 + 1);
v_canceled_343_ = lean_ctor_get_uint8(v___y_338_, sizeof(void*)*3 + 2);
v_trace_344_ = lean_ctor_get(v___y_338_, 1);
v_buildTime_345_ = lean_ctor_get(v___y_338_, 2);
v_isSharedCheck_374_ = !lean_is_exclusive(v___y_338_);
if (v_isSharedCheck_374_ == 0)
{
v___x_347_ = v___y_338_;
v_isShared_348_ = v_isSharedCheck_374_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_buildTime_345_);
lean_inc(v_trace_344_);
lean_inc(v_log_340_);
lean_dec(v___y_338_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_374_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_349_; 
v___x_349_ = lean_apply_2(v___y_332_, v_log_340_, lean_box(0));
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_361_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_a_351_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_361_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_361_ == 0)
{
v___x_353_ = v___x_349_;
v_isShared_354_ = v_isSharedCheck_361_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_361_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v_a_351_);
v___x_356_ = v___x_347_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_a_351_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v_trace_344_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_buildTime_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*3, v_action_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*3 + 1, v_wantsRebuild_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_360_, sizeof(void*)*3 + 2, v_canceled_343_);
v___x_356_ = v_reuseFailAlloc_360_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_358_; 
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_356_);
v___x_358_ = v___x_353_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_350_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_356_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_362_; lean_object* v_a_363_; lean_object* v___x_365_; uint8_t v_isShared_366_; uint8_t v_isSharedCheck_373_; 
v_a_362_ = lean_ctor_get(v___x_349_, 0);
v_a_363_ = lean_ctor_get(v___x_349_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_373_ == 0)
{
v___x_365_ = v___x_349_;
v_isShared_366_ = v_isSharedCheck_373_;
goto v_resetjp_364_;
}
else
{
lean_inc(v_a_363_);
lean_inc(v_a_362_);
lean_dec(v___x_349_);
v___x_365_ = lean_box(0);
v_isShared_366_ = v_isSharedCheck_373_;
goto v_resetjp_364_;
}
v_resetjp_364_:
{
lean_object* v___x_368_; 
if (v_isShared_348_ == 0)
{
lean_ctor_set(v___x_347_, 0, v_a_363_);
v___x_368_ = v___x_347_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_a_363_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_trace_344_);
lean_ctor_set(v_reuseFailAlloc_372_, 2, v_buildTime_345_);
lean_ctor_set_uint8(v_reuseFailAlloc_372_, sizeof(void*)*3, v_action_341_);
lean_ctor_set_uint8(v_reuseFailAlloc_372_, sizeof(void*)*3 + 1, v_wantsRebuild_342_);
lean_ctor_set_uint8(v_reuseFailAlloc_372_, sizeof(void*)*3 + 2, v_canceled_343_);
v___x_368_ = v_reuseFailAlloc_372_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_370_; 
if (v_isShared_366_ == 0)
{
lean_ctor_set(v___x_365_, 1, v___x_368_);
v___x_370_ = v___x_365_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_362_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v___x_368_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(lean_object* v_00_u03b1_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lake_instMonadLiftLogIOJobM___lam__0(v_00_u03b1_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_);
lean_dec_ref(v___y_381_);
lean_dec(v___y_380_);
lean_dec(v___y_379_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg(uint8_t v_action_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_log_390_; uint8_t v_action_391_; uint8_t v_wantsRebuild_392_; uint8_t v_canceled_393_; lean_object* v_trace_394_; lean_object* v_buildTime_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_405_; 
v_log_390_ = lean_ctor_get(v_a_388_, 0);
v_action_391_ = lean_ctor_get_uint8(v_a_388_, sizeof(void*)*3);
v_wantsRebuild_392_ = lean_ctor_get_uint8(v_a_388_, sizeof(void*)*3 + 1);
v_canceled_393_ = lean_ctor_get_uint8(v_a_388_, sizeof(void*)*3 + 2);
v_trace_394_ = lean_ctor_get(v_a_388_, 1);
v_buildTime_395_ = lean_ctor_get(v_a_388_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v_a_388_);
if (v_isSharedCheck_405_ == 0)
{
v___x_397_ = v_a_388_;
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_buildTime_395_);
lean_inc(v_trace_394_);
lean_inc(v_log_390_);
lean_dec(v_a_388_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; uint8_t v___x_400_; lean_object* v___x_402_; 
v___x_399_ = lean_box(0);
v___x_400_ = l_Lake_JobAction_merge(v_action_391_, v_action_387_);
if (v_isShared_398_ == 0)
{
v___x_402_ = v___x_397_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_log_390_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_trace_394_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v_buildTime_395_);
lean_ctor_set_uint8(v_reuseFailAlloc_404_, sizeof(void*)*3 + 1, v_wantsRebuild_392_);
lean_ctor_set_uint8(v_reuseFailAlloc_404_, sizeof(void*)*3 + 2, v_canceled_393_);
v___x_402_ = v_reuseFailAlloc_404_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
lean_object* v___x_403_; 
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*3, v___x_400_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_399_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg___boxed(lean_object* v_action_406_, lean_object* v_a_407_, lean_object* v_a_408_){
_start:
{
uint8_t v_action_boxed_409_; lean_object* v_res_410_; 
v_action_boxed_409_ = lean_unbox(v_action_406_);
v_res_410_ = l_Lake_updateAction___redArg(v_action_boxed_409_, v_a_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction(uint8_t v_action_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_log_419_; uint8_t v_action_420_; uint8_t v_wantsRebuild_421_; uint8_t v_canceled_422_; lean_object* v_trace_423_; lean_object* v_buildTime_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_434_; 
v_log_419_ = lean_ctor_get(v_a_417_, 0);
v_action_420_ = lean_ctor_get_uint8(v_a_417_, sizeof(void*)*3);
v_wantsRebuild_421_ = lean_ctor_get_uint8(v_a_417_, sizeof(void*)*3 + 1);
v_canceled_422_ = lean_ctor_get_uint8(v_a_417_, sizeof(void*)*3 + 2);
v_trace_423_ = lean_ctor_get(v_a_417_, 1);
v_buildTime_424_ = lean_ctor_get(v_a_417_, 2);
v_isSharedCheck_434_ = !lean_is_exclusive(v_a_417_);
if (v_isSharedCheck_434_ == 0)
{
v___x_426_ = v_a_417_;
v_isShared_427_ = v_isSharedCheck_434_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_buildTime_424_);
lean_inc(v_trace_423_);
lean_inc(v_log_419_);
lean_dec(v_a_417_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_434_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; uint8_t v___x_429_; lean_object* v___x_431_; 
v___x_428_ = lean_box(0);
v___x_429_ = l_Lake_JobAction_merge(v_action_420_, v_action_411_);
if (v_isShared_427_ == 0)
{
v___x_431_ = v___x_426_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_log_419_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_trace_423_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_buildTime_424_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*3 + 1, v_wantsRebuild_421_);
lean_ctor_set_uint8(v_reuseFailAlloc_433_, sizeof(void*)*3 + 2, v_canceled_422_);
v___x_431_ = v_reuseFailAlloc_433_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
lean_object* v___x_432_; 
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*3, v___x_429_);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_428_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
return v___x_432_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___boxed(lean_object* v_action_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_){
_start:
{
uint8_t v_action_boxed_443_; lean_object* v_res_444_; 
v_action_boxed_443_ = lean_unbox(v_action_435_);
v_res_444_ = l_Lake_updateAction(v_action_boxed_443_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec(v_a_438_);
lean_dec(v_a_437_);
lean_dec_ref(v_a_436_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg(lean_object* v_a_445_){
_start:
{
lean_object* v_trace_447_; lean_object* v___x_448_; 
v_trace_447_ = lean_ctor_get(v_a_445_, 1);
lean_inc_ref(v_trace_447_);
v___x_448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_448_, 0, v_trace_447_);
lean_ctor_set(v___x_448_, 1, v_a_445_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg___boxed(lean_object* v_a_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lake_getTrace___redArg(v_a_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace(lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_trace_459_; lean_object* v___x_460_; 
v_trace_459_ = lean_ctor_get(v_a_457_, 1);
lean_inc_ref(v_trace_459_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v_trace_459_);
lean_ctor_set(v___x_460_, 1, v_a_457_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___boxed(lean_object* v_a_461_, lean_object* v_a_462_, lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Lake_getTrace(v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_, v_a_466_);
lean_dec_ref(v_a_465_);
lean_dec(v_a_464_);
lean_dec(v_a_463_);
lean_dec(v_a_462_);
lean_dec_ref(v_a_461_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg(lean_object* v_trace_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_log_472_; uint8_t v_action_473_; uint8_t v_wantsRebuild_474_; uint8_t v_canceled_475_; lean_object* v_buildTime_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_485_; 
v_log_472_ = lean_ctor_get(v_a_470_, 0);
v_action_473_ = lean_ctor_get_uint8(v_a_470_, sizeof(void*)*3);
v_wantsRebuild_474_ = lean_ctor_get_uint8(v_a_470_, sizeof(void*)*3 + 1);
v_canceled_475_ = lean_ctor_get_uint8(v_a_470_, sizeof(void*)*3 + 2);
v_buildTime_476_ = lean_ctor_get(v_a_470_, 2);
v_isSharedCheck_485_ = !lean_is_exclusive(v_a_470_);
if (v_isSharedCheck_485_ == 0)
{
lean_object* v_unused_486_; 
v_unused_486_ = lean_ctor_get(v_a_470_, 1);
lean_dec(v_unused_486_);
v___x_478_ = v_a_470_;
v_isShared_479_ = v_isSharedCheck_485_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_buildTime_476_);
lean_inc(v_log_472_);
lean_dec(v_a_470_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_485_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
v___x_480_ = lean_box(0);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v_trace_469_);
v___x_482_ = v___x_478_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_484_; 
v_reuseFailAlloc_484_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_484_, 0, v_log_472_);
lean_ctor_set(v_reuseFailAlloc_484_, 1, v_trace_469_);
lean_ctor_set(v_reuseFailAlloc_484_, 2, v_buildTime_476_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*3, v_action_473_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*3 + 1, v_wantsRebuild_474_);
lean_ctor_set_uint8(v_reuseFailAlloc_484_, sizeof(void*)*3 + 2, v_canceled_475_);
v___x_482_ = v_reuseFailAlloc_484_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; 
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_480_);
lean_ctor_set(v___x_483_, 1, v___x_482_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg___boxed(lean_object* v_trace_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Lake_setTrace___redArg(v_trace_487_, v_a_488_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace(lean_object* v_trace_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_log_499_; uint8_t v_action_500_; uint8_t v_wantsRebuild_501_; uint8_t v_canceled_502_; lean_object* v_buildTime_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_512_; 
v_log_499_ = lean_ctor_get(v_a_497_, 0);
v_action_500_ = lean_ctor_get_uint8(v_a_497_, sizeof(void*)*3);
v_wantsRebuild_501_ = lean_ctor_get_uint8(v_a_497_, sizeof(void*)*3 + 1);
v_canceled_502_ = lean_ctor_get_uint8(v_a_497_, sizeof(void*)*3 + 2);
v_buildTime_503_ = lean_ctor_get(v_a_497_, 2);
v_isSharedCheck_512_ = !lean_is_exclusive(v_a_497_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v_a_497_, 1);
lean_dec(v_unused_513_);
v___x_505_ = v_a_497_;
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_buildTime_503_);
lean_inc(v_log_499_);
lean_dec(v_a_497_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_512_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_507_; lean_object* v___x_509_; 
v___x_507_ = lean_box(0);
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 1, v_trace_491_);
v___x_509_ = v___x_505_;
goto v_reusejp_508_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v_log_499_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_trace_491_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_buildTime_503_);
lean_ctor_set_uint8(v_reuseFailAlloc_511_, sizeof(void*)*3, v_action_500_);
lean_ctor_set_uint8(v_reuseFailAlloc_511_, sizeof(void*)*3 + 1, v_wantsRebuild_501_);
lean_ctor_set_uint8(v_reuseFailAlloc_511_, sizeof(void*)*3 + 2, v_canceled_502_);
v___x_509_ = v_reuseFailAlloc_511_;
goto v_reusejp_508_;
}
v_reusejp_508_:
{
lean_object* v___x_510_; 
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_507_);
lean_ctor_set(v___x_510_, 1, v___x_509_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___boxed(lean_object* v_trace_514_, lean_object* v_a_515_, lean_object* v_a_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lake_setTrace(v_trace_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_);
lean_dec_ref(v_a_519_);
lean_dec(v_a_518_);
lean_dec(v_a_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_a_515_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg(lean_object* v_caption_523_, lean_object* v_a_524_){
_start:
{
lean_object* v_log_526_; uint8_t v_action_527_; uint8_t v_wantsRebuild_528_; uint8_t v_canceled_529_; lean_object* v_buildTime_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_540_; 
v_log_526_ = lean_ctor_get(v_a_524_, 0);
v_action_527_ = lean_ctor_get_uint8(v_a_524_, sizeof(void*)*3);
v_wantsRebuild_528_ = lean_ctor_get_uint8(v_a_524_, sizeof(void*)*3 + 1);
v_canceled_529_ = lean_ctor_get_uint8(v_a_524_, sizeof(void*)*3 + 2);
v_buildTime_530_ = lean_ctor_get(v_a_524_, 2);
v_isSharedCheck_540_ = !lean_is_exclusive(v_a_524_);
if (v_isSharedCheck_540_ == 0)
{
lean_object* v_unused_541_; 
v_unused_541_ = lean_ctor_get(v_a_524_, 1);
lean_dec(v_unused_541_);
v___x_532_ = v_a_524_;
v_isShared_533_ = v_isSharedCheck_540_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_buildTime_530_);
lean_inc(v_log_526_);
lean_dec(v_a_524_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_540_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_534_ = l_Lake_BuildTrace_nil(v_caption_523_);
v___x_535_ = lean_box(0);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v___x_534_);
v___x_537_ = v___x_532_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_539_; 
v_reuseFailAlloc_539_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_539_, 0, v_log_526_);
lean_ctor_set(v_reuseFailAlloc_539_, 1, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_539_, 2, v_buildTime_530_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, sizeof(void*)*3, v_action_527_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, sizeof(void*)*3 + 1, v_wantsRebuild_528_);
lean_ctor_set_uint8(v_reuseFailAlloc_539_, sizeof(void*)*3 + 2, v_canceled_529_);
v___x_537_ = v_reuseFailAlloc_539_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
lean_object* v___x_538_; 
v___x_538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_535_);
lean_ctor_set(v___x_538_, 1, v___x_537_);
return v___x_538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg___boxed(lean_object* v_caption_542_, lean_object* v_a_543_, lean_object* v_a_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lake_newTrace___redArg(v_caption_542_, v_a_543_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace(lean_object* v_caption_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_){
_start:
{
lean_object* v_log_554_; uint8_t v_action_555_; uint8_t v_wantsRebuild_556_; uint8_t v_canceled_557_; lean_object* v_buildTime_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_568_; 
v_log_554_ = lean_ctor_get(v_a_552_, 0);
v_action_555_ = lean_ctor_get_uint8(v_a_552_, sizeof(void*)*3);
v_wantsRebuild_556_ = lean_ctor_get_uint8(v_a_552_, sizeof(void*)*3 + 1);
v_canceled_557_ = lean_ctor_get_uint8(v_a_552_, sizeof(void*)*3 + 2);
v_buildTime_558_ = lean_ctor_get(v_a_552_, 2);
v_isSharedCheck_568_ = !lean_is_exclusive(v_a_552_);
if (v_isSharedCheck_568_ == 0)
{
lean_object* v_unused_569_; 
v_unused_569_ = lean_ctor_get(v_a_552_, 1);
lean_dec(v_unused_569_);
v___x_560_ = v_a_552_;
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_buildTime_558_);
lean_inc(v_log_554_);
lean_dec(v_a_552_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_568_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_562_ = l_Lake_BuildTrace_nil(v_caption_546_);
v___x_563_ = lean_box(0);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 1, v___x_562_);
v___x_565_ = v___x_560_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v_log_554_);
lean_ctor_set(v_reuseFailAlloc_567_, 1, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_567_, 2, v_buildTime_558_);
lean_ctor_set_uint8(v_reuseFailAlloc_567_, sizeof(void*)*3, v_action_555_);
lean_ctor_set_uint8(v_reuseFailAlloc_567_, sizeof(void*)*3 + 1, v_wantsRebuild_556_);
lean_ctor_set_uint8(v_reuseFailAlloc_567_, sizeof(void*)*3 + 2, v_canceled_557_);
v___x_565_ = v_reuseFailAlloc_567_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; 
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_563_);
lean_ctor_set(v___x_566_, 1, v___x_565_);
return v___x_566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___boxed(lean_object* v_caption_570_, lean_object* v_a_571_, lean_object* v_a_572_, lean_object* v_a_573_, lean_object* v_a_574_, lean_object* v_a_575_, lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lake_newTrace(v_caption_570_, v_a_571_, v_a_572_, v_a_573_, v_a_574_, v_a_575_, v_a_576_);
lean_dec_ref(v_a_575_);
lean_dec(v_a_574_);
lean_dec(v_a_573_);
lean_dec(v_a_572_);
lean_dec_ref(v_a_571_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg(lean_object* v_f_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_log_582_; uint8_t v_action_583_; uint8_t v_wantsRebuild_584_; uint8_t v_canceled_585_; lean_object* v_trace_586_; lean_object* v_buildTime_587_; lean_object* v___x_589_; uint8_t v_isShared_590_; uint8_t v_isSharedCheck_597_; 
v_log_582_ = lean_ctor_get(v_a_580_, 0);
v_action_583_ = lean_ctor_get_uint8(v_a_580_, sizeof(void*)*3);
v_wantsRebuild_584_ = lean_ctor_get_uint8(v_a_580_, sizeof(void*)*3 + 1);
v_canceled_585_ = lean_ctor_get_uint8(v_a_580_, sizeof(void*)*3 + 2);
v_trace_586_ = lean_ctor_get(v_a_580_, 1);
v_buildTime_587_ = lean_ctor_get(v_a_580_, 2);
v_isSharedCheck_597_ = !lean_is_exclusive(v_a_580_);
if (v_isSharedCheck_597_ == 0)
{
v___x_589_ = v_a_580_;
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
else
{
lean_inc(v_buildTime_587_);
lean_inc(v_trace_586_);
lean_inc(v_log_582_);
lean_dec(v_a_580_);
v___x_589_ = lean_box(0);
v_isShared_590_ = v_isSharedCheck_597_;
goto v_resetjp_588_;
}
v_resetjp_588_:
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_591_ = lean_box(0);
v___x_592_ = lean_apply_1(v_f_579_, v_trace_586_);
if (v_isShared_590_ == 0)
{
lean_ctor_set(v___x_589_, 1, v___x_592_);
v___x_594_ = v___x_589_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_log_582_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___x_592_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v_buildTime_587_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*3, v_action_583_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*3 + 1, v_wantsRebuild_584_);
lean_ctor_set_uint8(v_reuseFailAlloc_596_, sizeof(void*)*3 + 2, v_canceled_585_);
v___x_594_ = v_reuseFailAlloc_596_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; 
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_591_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
return v___x_595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg___boxed(lean_object* v_f_598_, lean_object* v_a_599_, lean_object* v_a_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lake_modifyTrace___redArg(v_f_598_, v_a_599_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace(lean_object* v_f_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_, lean_object* v_a_606_, lean_object* v_a_607_, lean_object* v_a_608_){
_start:
{
lean_object* v_log_610_; uint8_t v_action_611_; uint8_t v_wantsRebuild_612_; uint8_t v_canceled_613_; lean_object* v_trace_614_; lean_object* v_buildTime_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_625_; 
v_log_610_ = lean_ctor_get(v_a_608_, 0);
v_action_611_ = lean_ctor_get_uint8(v_a_608_, sizeof(void*)*3);
v_wantsRebuild_612_ = lean_ctor_get_uint8(v_a_608_, sizeof(void*)*3 + 1);
v_canceled_613_ = lean_ctor_get_uint8(v_a_608_, sizeof(void*)*3 + 2);
v_trace_614_ = lean_ctor_get(v_a_608_, 1);
v_buildTime_615_ = lean_ctor_get(v_a_608_, 2);
v_isSharedCheck_625_ = !lean_is_exclusive(v_a_608_);
if (v_isSharedCheck_625_ == 0)
{
v___x_617_ = v_a_608_;
v_isShared_618_ = v_isSharedCheck_625_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_buildTime_615_);
lean_inc(v_trace_614_);
lean_inc(v_log_610_);
lean_dec(v_a_608_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_625_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_622_; 
v___x_619_ = lean_box(0);
v___x_620_ = lean_apply_1(v_f_602_, v_trace_614_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 1, v___x_620_);
v___x_622_ = v___x_617_;
goto v_reusejp_621_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_log_610_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v___x_620_);
lean_ctor_set(v_reuseFailAlloc_624_, 2, v_buildTime_615_);
lean_ctor_set_uint8(v_reuseFailAlloc_624_, sizeof(void*)*3, v_action_611_);
lean_ctor_set_uint8(v_reuseFailAlloc_624_, sizeof(void*)*3 + 1, v_wantsRebuild_612_);
lean_ctor_set_uint8(v_reuseFailAlloc_624_, sizeof(void*)*3 + 2, v_canceled_613_);
v___x_622_ = v_reuseFailAlloc_624_;
goto v_reusejp_621_;
}
v_reusejp_621_:
{
lean_object* v___x_623_; 
v___x_623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_623_, 0, v___x_619_);
lean_ctor_set(v___x_623_, 1, v___x_622_);
return v___x_623_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___boxed(lean_object* v_f_626_, lean_object* v_a_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_, lean_object* v_a_632_, lean_object* v_a_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Lake_modifyTrace(v_f_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_);
lean_dec_ref(v_a_631_);
lean_dec(v_a_630_);
lean_dec(v_a_629_);
lean_dec(v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg(lean_object* v_caption_635_, lean_object* v_a_636_){
_start:
{
lean_object* v_trace_638_; lean_object* v_log_639_; uint8_t v_action_640_; uint8_t v_wantsRebuild_641_; uint8_t v_canceled_642_; lean_object* v_buildTime_643_; lean_object* v___x_645_; uint8_t v_isShared_646_; uint8_t v_isSharedCheck_663_; 
v_trace_638_ = lean_ctor_get(v_a_636_, 1);
v_log_639_ = lean_ctor_get(v_a_636_, 0);
v_action_640_ = lean_ctor_get_uint8(v_a_636_, sizeof(void*)*3);
v_wantsRebuild_641_ = lean_ctor_get_uint8(v_a_636_, sizeof(void*)*3 + 1);
v_canceled_642_ = lean_ctor_get_uint8(v_a_636_, sizeof(void*)*3 + 2);
v_buildTime_643_ = lean_ctor_get(v_a_636_, 2);
v_isSharedCheck_663_ = !lean_is_exclusive(v_a_636_);
if (v_isSharedCheck_663_ == 0)
{
v___x_645_ = v_a_636_;
v_isShared_646_ = v_isSharedCheck_663_;
goto v_resetjp_644_;
}
else
{
lean_inc(v_buildTime_643_);
lean_inc(v_trace_638_);
lean_inc(v_log_639_);
lean_dec(v_a_636_);
v___x_645_ = lean_box(0);
v_isShared_646_ = v_isSharedCheck_663_;
goto v_resetjp_644_;
}
v_resetjp_644_:
{
lean_object* v_inputs_647_; uint64_t v_hash_648_; lean_object* v_mtime_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_661_; 
v_inputs_647_ = lean_ctor_get(v_trace_638_, 1);
v_hash_648_ = lean_ctor_get_uint64(v_trace_638_, sizeof(void*)*3);
v_mtime_649_ = lean_ctor_get(v_trace_638_, 2);
v_isSharedCheck_661_ = !lean_is_exclusive(v_trace_638_);
if (v_isSharedCheck_661_ == 0)
{
lean_object* v_unused_662_; 
v_unused_662_ = lean_ctor_get(v_trace_638_, 0);
lean_dec(v_unused_662_);
v___x_651_ = v_trace_638_;
v_isShared_652_ = v_isSharedCheck_661_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_mtime_649_);
lean_inc(v_inputs_647_);
lean_dec(v_trace_638_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_661_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_653_ = lean_box(0);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v_caption_635_);
v___x_655_ = v___x_651_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_caption_635_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_inputs_647_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_mtime_649_);
lean_ctor_set_uint64(v_reuseFailAlloc_660_, sizeof(void*)*3, v_hash_648_);
v___x_655_ = v_reuseFailAlloc_660_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
lean_object* v___x_657_; 
if (v_isShared_646_ == 0)
{
lean_ctor_set(v___x_645_, 1, v___x_655_);
v___x_657_ = v___x_645_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_log_639_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v___x_655_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_buildTime_643_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*3, v_action_640_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*3 + 1, v_wantsRebuild_641_);
lean_ctor_set_uint8(v_reuseFailAlloc_659_, sizeof(void*)*3 + 2, v_canceled_642_);
v___x_657_ = v_reuseFailAlloc_659_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
lean_object* v___x_658_; 
v___x_658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_653_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
return v___x_658_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg___boxed(lean_object* v_caption_664_, lean_object* v_a_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Lake_setTraceCaption___redArg(v_caption_664_, v_a_665_);
return v_res_667_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption(lean_object* v_caption_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_trace_676_; lean_object* v_log_677_; uint8_t v_action_678_; uint8_t v_wantsRebuild_679_; uint8_t v_canceled_680_; lean_object* v_buildTime_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_701_; 
v_trace_676_ = lean_ctor_get(v_a_674_, 1);
v_log_677_ = lean_ctor_get(v_a_674_, 0);
v_action_678_ = lean_ctor_get_uint8(v_a_674_, sizeof(void*)*3);
v_wantsRebuild_679_ = lean_ctor_get_uint8(v_a_674_, sizeof(void*)*3 + 1);
v_canceled_680_ = lean_ctor_get_uint8(v_a_674_, sizeof(void*)*3 + 2);
v_buildTime_681_ = lean_ctor_get(v_a_674_, 2);
v_isSharedCheck_701_ = !lean_is_exclusive(v_a_674_);
if (v_isSharedCheck_701_ == 0)
{
v___x_683_ = v_a_674_;
v_isShared_684_ = v_isSharedCheck_701_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_buildTime_681_);
lean_inc(v_trace_676_);
lean_inc(v_log_677_);
lean_dec(v_a_674_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_701_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v_inputs_685_; uint64_t v_hash_686_; lean_object* v_mtime_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_699_; 
v_inputs_685_ = lean_ctor_get(v_trace_676_, 1);
v_hash_686_ = lean_ctor_get_uint64(v_trace_676_, sizeof(void*)*3);
v_mtime_687_ = lean_ctor_get(v_trace_676_, 2);
v_isSharedCheck_699_ = !lean_is_exclusive(v_trace_676_);
if (v_isSharedCheck_699_ == 0)
{
lean_object* v_unused_700_; 
v_unused_700_ = lean_ctor_get(v_trace_676_, 0);
lean_dec(v_unused_700_);
v___x_689_ = v_trace_676_;
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_mtime_687_);
lean_inc(v_inputs_685_);
lean_dec(v_trace_676_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_699_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v___x_691_; lean_object* v___x_693_; 
v___x_691_ = lean_box(0);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v_caption_668_);
v___x_693_ = v___x_689_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_caption_668_);
lean_ctor_set(v_reuseFailAlloc_698_, 1, v_inputs_685_);
lean_ctor_set(v_reuseFailAlloc_698_, 2, v_mtime_687_);
lean_ctor_set_uint64(v_reuseFailAlloc_698_, sizeof(void*)*3, v_hash_686_);
v___x_693_ = v_reuseFailAlloc_698_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
lean_object* v___x_695_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 1, v___x_693_);
v___x_695_ = v___x_683_;
goto v_reusejp_694_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_log_677_);
lean_ctor_set(v_reuseFailAlloc_697_, 1, v___x_693_);
lean_ctor_set(v_reuseFailAlloc_697_, 2, v_buildTime_681_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*3, v_action_678_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*3 + 1, v_wantsRebuild_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_697_, sizeof(void*)*3 + 2, v_canceled_680_);
v___x_695_ = v_reuseFailAlloc_697_;
goto v_reusejp_694_;
}
v_reusejp_694_:
{
lean_object* v___x_696_; 
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_691_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
return v___x_696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___boxed(lean_object* v_caption_702_, lean_object* v_a_703_, lean_object* v_a_704_, lean_object* v_a_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Lake_setTraceCaption(v_caption_702_, v_a_703_, v_a_704_, v_a_705_, v_a_706_, v_a_707_, v_a_708_);
lean_dec_ref(v_a_707_);
lean_dec(v_a_706_);
lean_dec(v_a_705_);
lean_dec(v_a_704_);
lean_dec_ref(v_a_703_);
return v_res_710_;
}
}
static lean_object* _init_l_Lake_takeTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_712_ = ((lean_object*)(l_Lake_takeTrace___redArg___closed__0));
v___x_713_ = l_Lake_BuildTrace_nil(v___x_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg(lean_object* v_a_714_){
_start:
{
lean_object* v_log_716_; uint8_t v_action_717_; uint8_t v_wantsRebuild_718_; uint8_t v_canceled_719_; lean_object* v_trace_720_; lean_object* v_buildTime_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_730_; 
v_log_716_ = lean_ctor_get(v_a_714_, 0);
v_action_717_ = lean_ctor_get_uint8(v_a_714_, sizeof(void*)*3);
v_wantsRebuild_718_ = lean_ctor_get_uint8(v_a_714_, sizeof(void*)*3 + 1);
v_canceled_719_ = lean_ctor_get_uint8(v_a_714_, sizeof(void*)*3 + 2);
v_trace_720_ = lean_ctor_get(v_a_714_, 1);
v_buildTime_721_ = lean_ctor_get(v_a_714_, 2);
v_isSharedCheck_730_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_730_ == 0)
{
v___x_723_ = v_a_714_;
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_buildTime_721_);
lean_inc(v_trace_720_);
lean_inc(v_log_716_);
lean_dec(v_a_714_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_730_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_725_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v___x_725_);
v___x_727_ = v___x_723_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_log_716_);
lean_ctor_set(v_reuseFailAlloc_729_, 1, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_729_, 2, v_buildTime_721_);
lean_ctor_set_uint8(v_reuseFailAlloc_729_, sizeof(void*)*3, v_action_717_);
lean_ctor_set_uint8(v_reuseFailAlloc_729_, sizeof(void*)*3 + 1, v_wantsRebuild_718_);
lean_ctor_set_uint8(v_reuseFailAlloc_729_, sizeof(void*)*3 + 2, v_canceled_719_);
v___x_727_ = v_reuseFailAlloc_729_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v_trace_720_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
return v___x_728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg___boxed(lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lake_takeTrace___redArg(v_a_731_);
return v_res_733_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace(lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v_log_741_; uint8_t v_action_742_; uint8_t v_wantsRebuild_743_; uint8_t v_canceled_744_; lean_object* v_trace_745_; lean_object* v_buildTime_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_755_; 
v_log_741_ = lean_ctor_get(v_a_739_, 0);
v_action_742_ = lean_ctor_get_uint8(v_a_739_, sizeof(void*)*3);
v_wantsRebuild_743_ = lean_ctor_get_uint8(v_a_739_, sizeof(void*)*3 + 1);
v_canceled_744_ = lean_ctor_get_uint8(v_a_739_, sizeof(void*)*3 + 2);
v_trace_745_ = lean_ctor_get(v_a_739_, 1);
v_buildTime_746_ = lean_ctor_get(v_a_739_, 2);
v_isSharedCheck_755_ = !lean_is_exclusive(v_a_739_);
if (v_isSharedCheck_755_ == 0)
{
v___x_748_ = v_a_739_;
v_isShared_749_ = v_isSharedCheck_755_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_buildTime_746_);
lean_inc(v_trace_745_);
lean_inc(v_log_741_);
lean_dec(v_a_739_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_755_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 1, v___x_750_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_log_741_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___x_750_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v_buildTime_746_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*3, v_action_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*3 + 1, v_wantsRebuild_743_);
lean_ctor_set_uint8(v_reuseFailAlloc_754_, sizeof(void*)*3 + 2, v_canceled_744_);
v___x_752_ = v_reuseFailAlloc_754_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
lean_object* v___x_753_; 
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v_trace_745_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___boxed(lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lake_takeTrace(v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
lean_dec_ref(v_a_760_);
lean_dec(v_a_759_);
lean_dec(v_a_758_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg(lean_object* v_trace_764_, lean_object* v_a_765_){
_start:
{
lean_object* v_log_767_; uint8_t v_action_768_; uint8_t v_wantsRebuild_769_; uint8_t v_canceled_770_; lean_object* v_trace_771_; lean_object* v_buildTime_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_780_; 
v_log_767_ = lean_ctor_get(v_a_765_, 0);
v_action_768_ = lean_ctor_get_uint8(v_a_765_, sizeof(void*)*3);
v_wantsRebuild_769_ = lean_ctor_get_uint8(v_a_765_, sizeof(void*)*3 + 1);
v_canceled_770_ = lean_ctor_get_uint8(v_a_765_, sizeof(void*)*3 + 2);
v_trace_771_ = lean_ctor_get(v_a_765_, 1);
v_buildTime_772_ = lean_ctor_get(v_a_765_, 2);
v_isSharedCheck_780_ = !lean_is_exclusive(v_a_765_);
if (v_isSharedCheck_780_ == 0)
{
v___x_774_ = v_a_765_;
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_buildTime_772_);
lean_inc(v_trace_771_);
lean_inc(v_log_767_);
lean_dec(v_a_765_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_780_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
lean_ctor_set(v___x_774_, 1, v_trace_764_);
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_log_767_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_trace_764_);
lean_ctor_set(v_reuseFailAlloc_779_, 2, v_buildTime_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, sizeof(void*)*3, v_action_768_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, sizeof(void*)*3 + 1, v_wantsRebuild_769_);
lean_ctor_set_uint8(v_reuseFailAlloc_779_, sizeof(void*)*3 + 2, v_canceled_770_);
v___x_777_ = v_reuseFailAlloc_779_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_778_; 
v___x_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_778_, 0, v_trace_771_);
lean_ctor_set(v___x_778_, 1, v___x_777_);
return v___x_778_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg___boxed(lean_object* v_trace_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lake_swapTrace___redArg(v_trace_781_, v_a_782_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace(lean_object* v_trace_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_log_793_; uint8_t v_action_794_; uint8_t v_wantsRebuild_795_; uint8_t v_canceled_796_; lean_object* v_trace_797_; lean_object* v_buildTime_798_; lean_object* v___x_800_; uint8_t v_isShared_801_; uint8_t v_isSharedCheck_806_; 
v_log_793_ = lean_ctor_get(v_a_791_, 0);
v_action_794_ = lean_ctor_get_uint8(v_a_791_, sizeof(void*)*3);
v_wantsRebuild_795_ = lean_ctor_get_uint8(v_a_791_, sizeof(void*)*3 + 1);
v_canceled_796_ = lean_ctor_get_uint8(v_a_791_, sizeof(void*)*3 + 2);
v_trace_797_ = lean_ctor_get(v_a_791_, 1);
v_buildTime_798_ = lean_ctor_get(v_a_791_, 2);
v_isSharedCheck_806_ = !lean_is_exclusive(v_a_791_);
if (v_isSharedCheck_806_ == 0)
{
v___x_800_ = v_a_791_;
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
else
{
lean_inc(v_buildTime_798_);
lean_inc(v_trace_797_);
lean_inc(v_log_793_);
lean_dec(v_a_791_);
v___x_800_ = lean_box(0);
v_isShared_801_ = v_isSharedCheck_806_;
goto v_resetjp_799_;
}
v_resetjp_799_:
{
lean_object* v___x_803_; 
if (v_isShared_801_ == 0)
{
lean_ctor_set(v___x_800_, 1, v_trace_785_);
v___x_803_ = v___x_800_;
goto v_reusejp_802_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_log_793_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_trace_785_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_buildTime_798_);
lean_ctor_set_uint8(v_reuseFailAlloc_805_, sizeof(void*)*3, v_action_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_805_, sizeof(void*)*3 + 1, v_wantsRebuild_795_);
lean_ctor_set_uint8(v_reuseFailAlloc_805_, sizeof(void*)*3 + 2, v_canceled_796_);
v___x_803_ = v_reuseFailAlloc_805_;
goto v_reusejp_802_;
}
v_reusejp_802_:
{
lean_object* v___x_804_; 
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v_trace_797_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___boxed(lean_object* v_trace_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Lake_swapTrace(v_trace_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_);
lean_dec_ref(v_a_812_);
lean_dec(v_a_811_);
lean_dec(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg(lean_object* v_trace_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_log_819_; uint8_t v_action_820_; uint8_t v_wantsRebuild_821_; uint8_t v_canceled_822_; lean_object* v_trace_823_; lean_object* v_buildTime_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_834_; 
v_log_819_ = lean_ctor_get(v_a_817_, 0);
v_action_820_ = lean_ctor_get_uint8(v_a_817_, sizeof(void*)*3);
v_wantsRebuild_821_ = lean_ctor_get_uint8(v_a_817_, sizeof(void*)*3 + 1);
v_canceled_822_ = lean_ctor_get_uint8(v_a_817_, sizeof(void*)*3 + 2);
v_trace_823_ = lean_ctor_get(v_a_817_, 1);
v_buildTime_824_ = lean_ctor_get(v_a_817_, 2);
v_isSharedCheck_834_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_834_ == 0)
{
v___x_826_ = v_a_817_;
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_buildTime_824_);
lean_inc(v_trace_823_);
lean_inc(v_log_819_);
lean_dec(v_a_817_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_828_ = lean_box(0);
v___x_829_ = l_Lake_BuildTrace_mix(v_trace_823_, v_trace_816_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v___x_829_);
v___x_831_ = v___x_826_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_log_819_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v___x_829_);
lean_ctor_set(v_reuseFailAlloc_833_, 2, v_buildTime_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_833_, sizeof(void*)*3, v_action_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_833_, sizeof(void*)*3 + 1, v_wantsRebuild_821_);
lean_ctor_set_uint8(v_reuseFailAlloc_833_, sizeof(void*)*3 + 2, v_canceled_822_);
v___x_831_ = v_reuseFailAlloc_833_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
lean_object* v___x_832_; 
v___x_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_828_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
return v___x_832_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg___boxed(lean_object* v_trace_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lake_addTrace___redArg(v_trace_835_, v_a_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace(lean_object* v_trace_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_log_847_; uint8_t v_action_848_; uint8_t v_wantsRebuild_849_; uint8_t v_canceled_850_; lean_object* v_trace_851_; lean_object* v_buildTime_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_862_; 
v_log_847_ = lean_ctor_get(v_a_845_, 0);
v_action_848_ = lean_ctor_get_uint8(v_a_845_, sizeof(void*)*3);
v_wantsRebuild_849_ = lean_ctor_get_uint8(v_a_845_, sizeof(void*)*3 + 1);
v_canceled_850_ = lean_ctor_get_uint8(v_a_845_, sizeof(void*)*3 + 2);
v_trace_851_ = lean_ctor_get(v_a_845_, 1);
v_buildTime_852_ = lean_ctor_get(v_a_845_, 2);
v_isSharedCheck_862_ = !lean_is_exclusive(v_a_845_);
if (v_isSharedCheck_862_ == 0)
{
v___x_854_ = v_a_845_;
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_buildTime_852_);
lean_inc(v_trace_851_);
lean_inc(v_log_847_);
lean_dec(v_a_845_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = lean_box(0);
v___x_857_ = l_Lake_BuildTrace_mix(v_trace_851_, v_trace_839_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_log_847_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_buildTime_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*3, v_action_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*3 + 1, v_wantsRebuild_849_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*3 + 2, v_canceled_850_);
v___x_859_ = v_reuseFailAlloc_861_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; 
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_856_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
return v___x_860_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___boxed(lean_object* v_trace_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lake_addTrace(v_trace_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec(v_a_866_);
lean_dec(v_a_865_);
lean_dec_ref(v_a_864_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg(lean_object* v_caption_872_, lean_object* v_x_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_log_881_; uint8_t v_action_882_; uint8_t v_wantsRebuild_883_; uint8_t v_canceled_884_; lean_object* v_trace_885_; lean_object* v_buildTime_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_918_; 
v_log_881_ = lean_ctor_get(v_a_879_, 0);
v_action_882_ = lean_ctor_get_uint8(v_a_879_, sizeof(void*)*3);
v_wantsRebuild_883_ = lean_ctor_get_uint8(v_a_879_, sizeof(void*)*3 + 1);
v_canceled_884_ = lean_ctor_get_uint8(v_a_879_, sizeof(void*)*3 + 2);
v_trace_885_ = lean_ctor_get(v_a_879_, 1);
v_buildTime_886_ = lean_ctor_get(v_a_879_, 2);
v_isSharedCheck_918_ = !lean_is_exclusive(v_a_879_);
if (v_isSharedCheck_918_ == 0)
{
v___x_888_ = v_a_879_;
v_isShared_889_ = v_isSharedCheck_918_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_buildTime_886_);
lean_inc(v_trace_885_);
lean_inc(v_log_881_);
lean_dec(v_a_879_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_918_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = l_Lake_BuildTrace_nil(v_caption_872_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 1, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_log_881_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_917_, 2, v_buildTime_886_);
lean_ctor_set_uint8(v_reuseFailAlloc_917_, sizeof(void*)*3, v_action_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_917_, sizeof(void*)*3 + 1, v_wantsRebuild_883_);
lean_ctor_set_uint8(v_reuseFailAlloc_917_, sizeof(void*)*3 + 2, v_canceled_884_);
v___x_892_ = v_reuseFailAlloc_917_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
lean_object* v___x_893_; 
lean_inc_ref(v_a_878_);
lean_inc(v_a_877_);
lean_inc(v_a_876_);
lean_inc(v_a_875_);
v___x_893_ = lean_apply_7(v_x_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v___x_892_, lean_box(0));
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_916_; 
v_a_894_ = lean_ctor_get(v___x_893_, 1);
v_a_895_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_916_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_916_ == 0)
{
v___x_897_ = v___x_893_;
v_isShared_898_ = v_isSharedCheck_916_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_894_);
lean_inc(v_a_895_);
lean_dec(v___x_893_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_916_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v_log_899_; uint8_t v_action_900_; uint8_t v_wantsRebuild_901_; uint8_t v_canceled_902_; lean_object* v_trace_903_; lean_object* v_buildTime_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_915_; 
v_log_899_ = lean_ctor_get(v_a_894_, 0);
v_action_900_ = lean_ctor_get_uint8(v_a_894_, sizeof(void*)*3);
v_wantsRebuild_901_ = lean_ctor_get_uint8(v_a_894_, sizeof(void*)*3 + 1);
v_canceled_902_ = lean_ctor_get_uint8(v_a_894_, sizeof(void*)*3 + 2);
v_trace_903_ = lean_ctor_get(v_a_894_, 1);
v_buildTime_904_ = lean_ctor_get(v_a_894_, 2);
v_isSharedCheck_915_ = !lean_is_exclusive(v_a_894_);
if (v_isSharedCheck_915_ == 0)
{
v___x_906_ = v_a_894_;
v_isShared_907_ = v_isSharedCheck_915_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_buildTime_904_);
lean_inc(v_trace_903_);
lean_inc(v_log_899_);
lean_dec(v_a_894_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_915_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_908_; lean_object* v___x_910_; 
v___x_908_ = l_Lake_BuildTrace_mix(v_trace_885_, v_trace_903_);
if (v_isShared_907_ == 0)
{
lean_ctor_set(v___x_906_, 1, v___x_908_);
v___x_910_ = v___x_906_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_914_; 
v_reuseFailAlloc_914_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_914_, 0, v_log_899_);
lean_ctor_set(v_reuseFailAlloc_914_, 1, v___x_908_);
lean_ctor_set(v_reuseFailAlloc_914_, 2, v_buildTime_904_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*3, v_action_900_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*3 + 1, v_wantsRebuild_901_);
lean_ctor_set_uint8(v_reuseFailAlloc_914_, sizeof(void*)*3 + 2, v_canceled_902_);
v___x_910_ = v_reuseFailAlloc_914_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
lean_object* v___x_912_; 
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v___x_910_);
v___x_912_ = v___x_897_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_895_);
lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_910_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
}
else
{
lean_dec_ref(v_trace_885_);
return v___x_893_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg___boxed(lean_object* v_caption_919_, lean_object* v_x_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l_Lake_addSubTrace___redArg(v_caption_919_, v_x_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec(v_a_923_);
lean_dec(v_a_922_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace(lean_object* v_00_u03b1_929_, lean_object* v_caption_930_, lean_object* v_x_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v_log_939_; uint8_t v_action_940_; uint8_t v_wantsRebuild_941_; uint8_t v_canceled_942_; lean_object* v_trace_943_; lean_object* v_buildTime_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_976_; 
v_log_939_ = lean_ctor_get(v_a_937_, 0);
v_action_940_ = lean_ctor_get_uint8(v_a_937_, sizeof(void*)*3);
v_wantsRebuild_941_ = lean_ctor_get_uint8(v_a_937_, sizeof(void*)*3 + 1);
v_canceled_942_ = lean_ctor_get_uint8(v_a_937_, sizeof(void*)*3 + 2);
v_trace_943_ = lean_ctor_get(v_a_937_, 1);
v_buildTime_944_ = lean_ctor_get(v_a_937_, 2);
v_isSharedCheck_976_ = !lean_is_exclusive(v_a_937_);
if (v_isSharedCheck_976_ == 0)
{
v___x_946_ = v_a_937_;
v_isShared_947_ = v_isSharedCheck_976_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_buildTime_944_);
lean_inc(v_trace_943_);
lean_inc(v_log_939_);
lean_dec(v_a_937_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_976_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; lean_object* v___x_950_; 
v___x_948_ = l_Lake_BuildTrace_nil(v_caption_930_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_948_);
v___x_950_ = v___x_946_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_log_939_);
lean_ctor_set(v_reuseFailAlloc_975_, 1, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_975_, 2, v_buildTime_944_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*3, v_action_940_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*3 + 1, v_wantsRebuild_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_975_, sizeof(void*)*3 + 2, v_canceled_942_);
v___x_950_ = v_reuseFailAlloc_975_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
lean_object* v___x_951_; 
lean_inc_ref(v_a_936_);
lean_inc(v_a_935_);
lean_inc(v_a_934_);
lean_inc(v_a_933_);
v___x_951_ = lean_apply_7(v_x_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v___x_950_, lean_box(0));
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_974_; 
v_a_952_ = lean_ctor_get(v___x_951_, 1);
v_a_953_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_974_ == 0)
{
v___x_955_ = v___x_951_;
v_isShared_956_ = v_isSharedCheck_974_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_952_);
lean_inc(v_a_953_);
lean_dec(v___x_951_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_974_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v_log_957_; uint8_t v_action_958_; uint8_t v_wantsRebuild_959_; uint8_t v_canceled_960_; lean_object* v_trace_961_; lean_object* v_buildTime_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_973_; 
v_log_957_ = lean_ctor_get(v_a_952_, 0);
v_action_958_ = lean_ctor_get_uint8(v_a_952_, sizeof(void*)*3);
v_wantsRebuild_959_ = lean_ctor_get_uint8(v_a_952_, sizeof(void*)*3 + 1);
v_canceled_960_ = lean_ctor_get_uint8(v_a_952_, sizeof(void*)*3 + 2);
v_trace_961_ = lean_ctor_get(v_a_952_, 1);
v_buildTime_962_ = lean_ctor_get(v_a_952_, 2);
v_isSharedCheck_973_ = !lean_is_exclusive(v_a_952_);
if (v_isSharedCheck_973_ == 0)
{
v___x_964_ = v_a_952_;
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_buildTime_962_);
lean_inc(v_trace_961_);
lean_inc(v_log_957_);
lean_dec(v_a_952_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = l_Lake_BuildTrace_mix(v_trace_943_, v_trace_961_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 1, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_log_957_);
lean_ctor_set(v_reuseFailAlloc_972_, 1, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_972_, 2, v_buildTime_962_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3, v_action_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 1, v_wantsRebuild_959_);
lean_ctor_set_uint8(v_reuseFailAlloc_972_, sizeof(void*)*3 + 2, v_canceled_960_);
v___x_968_ = v_reuseFailAlloc_972_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_970_; 
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 1, v___x_968_);
v___x_970_ = v___x_955_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_953_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
else
{
lean_dec_ref(v_trace_943_);
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___boxed(lean_object* v_00_u03b1_977_, lean_object* v_caption_978_, lean_object* v_x_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lake_addSubTrace(v_00_u03b1_977_, v_caption_978_, v_x_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_);
lean_dec_ref(v_a_984_);
lean_dec(v_a_983_);
lean_dec(v_a_982_);
lean_dec(v_a_981_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg(lean_object* v_f_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_, lean_object* v_a_993_, lean_object* v_a_994_){
_start:
{
lean_object* v___x_996_; 
lean_inc_ref(v_a_994_);
lean_inc_ref(v_a_993_);
lean_inc(v_a_992_);
lean_inc(v_a_991_);
lean_inc(v_a_990_);
v___x_996_ = lean_apply_7(v_f_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_, v_a_993_, v_a_994_, lean_box(0));
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg___boxed(lean_object* v_f_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lake_SpawnM_ofFn___redArg(v_f_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec_ref(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec(v_a_999_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn(lean_object* v_00_u03b1_1006_, lean_object* v_f_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_){
_start:
{
lean_object* v___x_1015_; 
lean_inc_ref(v_a_1013_);
lean_inc_ref(v_a_1012_);
lean_inc(v_a_1011_);
lean_inc(v_a_1010_);
lean_inc(v_a_1009_);
v___x_1015_ = lean_apply_7(v_f_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, lean_box(0));
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_f_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lake_SpawnM_ofFn(v_00_u03b1_1016_, v_f_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec_ref(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec(v_a_1019_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg(lean_object* v_self_1026_, lean_object* v_fetch_1027_, lean_object* v_pkg_x3f_1028_, lean_object* v_stack_1029_, lean_object* v_store_1030_, lean_object* v_ctx_1031_, lean_object* v_s_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_apply_7(v_self_1026_, v_fetch_1027_, v_pkg_x3f_1028_, v_stack_1029_, v_store_1030_, v_ctx_1031_, v_s_1032_, lean_box(0));
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg___boxed(lean_object* v_self_1035_, lean_object* v_fetch_1036_, lean_object* v_pkg_x3f_1037_, lean_object* v_stack_1038_, lean_object* v_store_1039_, lean_object* v_ctx_1040_, lean_object* v_s_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lake_SpawnM_toFn___redArg(v_self_1035_, v_fetch_1036_, v_pkg_x3f_1037_, v_stack_1038_, v_store_1039_, v_ctx_1040_, v_s_1041_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn(lean_object* v_00_u03b1_1044_, lean_object* v_self_1045_, lean_object* v_fetch_1046_, lean_object* v_pkg_x3f_1047_, lean_object* v_stack_1048_, lean_object* v_store_1049_, lean_object* v_ctx_1050_, lean_object* v_s_1051_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_apply_7(v_self_1045_, v_fetch_1046_, v_pkg_x3f_1047_, v_stack_1048_, v_store_1049_, v_ctx_1050_, v_s_1051_, lean_box(0));
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___boxed(lean_object* v_00_u03b1_1054_, lean_object* v_self_1055_, lean_object* v_fetch_1056_, lean_object* v_pkg_x3f_1057_, lean_object* v_stack_1058_, lean_object* v_store_1059_, lean_object* v_ctx_1060_, lean_object* v_s_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lake_SpawnM_toFn(v_00_u03b1_1054_, v_self_1055_, v_fetch_1056_, v_pkg_x3f_1057_, v_stack_1058_, v_store_1059_, v_ctx_1060_, v_s_1061_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg(lean_object* v_x_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_trace_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v_trace_1072_ = lean_ctor_get(v_a_1070_, 1);
lean_inc_ref(v_trace_1072_);
lean_inc_ref(v_a_1069_);
lean_inc(v_a_1068_);
lean_inc(v_a_1067_);
lean_inc(v_a_1066_);
v___x_1073_ = lean_apply_7(v_x_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_trace_1072_, lean_box(0));
v___x_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1074_, 0, v___x_1073_);
lean_ctor_set(v___x_1074_, 1, v_a_1070_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg___boxed(lean_object* v_x_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_res_1083_; 
v_res_1083_ = l_Lake_JobM_runSpawnM___redArg(v_x_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_);
lean_dec_ref(v_a_1080_);
lean_dec(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec(v_a_1077_);
return v_res_1083_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM(lean_object* v_00_u03b1_1084_, lean_object* v_x_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_trace_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_trace_1093_ = lean_ctor_get(v_a_1091_, 1);
lean_inc_ref(v_trace_1093_);
lean_inc_ref(v_a_1090_);
lean_inc(v_a_1089_);
lean_inc(v_a_1088_);
lean_inc(v_a_1087_);
v___x_1094_ = lean_apply_7(v_x_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_trace_1093_, lean_box(0));
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v_a_1091_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___boxed(lean_object* v_00_u03b1_1096_, lean_object* v_x_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v_res_1105_; 
v_res_1105_ = l_Lake_JobM_runSpawnM(v_00_u03b1_1096_, v_x_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_);
lean_dec_ref(v_a_1102_);
lean_dec(v_a_1101_);
lean_dec(v_a_1100_);
lean_dec(v_a_1099_);
return v_res_1105_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg(lean_object* v_x_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
uint8_t v___x_1116_; uint8_t v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1116_ = 0;
v___x_1117_ = 0;
v___x_1118_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1120_, 0, v_a_1114_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
lean_ctor_set(v___x_1120_, 2, v___x_1119_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*3, v___x_1116_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*3 + 1, v___x_1117_);
lean_ctor_set_uint8(v___x_1120_, sizeof(void*)*3 + 2, v___x_1117_);
lean_inc_ref(v_a_1113_);
lean_inc(v_a_1112_);
lean_inc(v_a_1111_);
lean_inc(v_a_1110_);
v___x_1121_ = lean_apply_7(v_x_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v___x_1120_, lean_box(0));
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1131_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 1);
v_a_1123_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1125_ = v___x_1121_;
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1122_);
lean_inc(v_a_1123_);
lean_dec(v___x_1121_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1131_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v_log_1127_; lean_object* v___x_1129_; 
v_log_1127_ = lean_ctor_get(v_a_1122_, 0);
lean_inc_ref(v_log_1127_);
lean_dec(v_a_1122_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v_log_1127_);
v___x_1129_ = v___x_1125_;
goto v_reusejp_1128_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_a_1123_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_log_1127_);
v___x_1129_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1128_;
}
v_reusejp_1128_:
{
return v___x_1129_;
}
}
}
else
{
lean_object* v_a_1132_; lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_a_1132_ = lean_ctor_get(v___x_1121_, 1);
v_a_1133_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v___x_1121_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1132_);
lean_inc(v_a_1133_);
lean_dec(v___x_1121_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v_log_1137_; lean_object* v___x_1139_; 
v_log_1137_ = lean_ctor_get(v_a_1132_, 0);
lean_inc_ref(v_log_1137_);
lean_dec(v_a_1132_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 1, v_log_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1133_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_log_1137_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg___boxed(lean_object* v_x_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lake_FetchM_runJobM___redArg(v_x_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_, v_a_1148_);
lean_dec_ref(v_a_1147_);
lean_dec(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec(v_a_1144_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM(lean_object* v_00_u03b1_1151_, lean_object* v_x_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_){
_start:
{
uint8_t v___x_1160_; uint8_t v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v___x_1160_ = 0;
v___x_1161_ = 0;
v___x_1162_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1164_, 0, v_a_1158_);
lean_ctor_set(v___x_1164_, 1, v___x_1162_);
lean_ctor_set(v___x_1164_, 2, v___x_1163_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*3, v___x_1160_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*3 + 1, v___x_1161_);
lean_ctor_set_uint8(v___x_1164_, sizeof(void*)*3 + 2, v___x_1161_);
lean_inc_ref(v_a_1157_);
lean_inc(v_a_1156_);
lean_inc(v_a_1155_);
lean_inc(v_a_1154_);
v___x_1165_ = lean_apply_7(v_x_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v___x_1164_, lean_box(0));
if (lean_obj_tag(v___x_1165_) == 0)
{
lean_object* v_a_1166_; lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1175_; 
v_a_1166_ = lean_ctor_get(v___x_1165_, 1);
v_a_1167_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1169_ = v___x_1165_;
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1166_);
lean_inc(v_a_1167_);
lean_dec(v___x_1165_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1175_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_log_1171_; lean_object* v___x_1173_; 
v_log_1171_ = lean_ctor_get(v_a_1166_, 0);
lean_inc_ref(v_log_1171_);
lean_dec(v_a_1166_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v_log_1171_);
v___x_1173_ = v___x_1169_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1167_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_log_1171_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
else
{
lean_object* v_a_1176_; lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1185_; 
v_a_1176_ = lean_ctor_get(v___x_1165_, 1);
v_a_1177_ = lean_ctor_get(v___x_1165_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1165_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1179_ = v___x_1165_;
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1176_);
lean_inc(v_a_1177_);
lean_dec(v___x_1165_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_log_1181_; lean_object* v___x_1183_; 
v_log_1181_ = lean_ctor_get(v_a_1176_, 0);
lean_inc_ref(v_log_1181_);
lean_dec(v_a_1176_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 1, v_log_1181_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1177_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_log_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___boxed(lean_object* v_00_u03b1_1186_, lean_object* v_x_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lake_FetchM_runJobM(v_00_u03b1_1186_, v_x_1187_, v_a_1188_, v_a_1189_, v_a_1190_, v_a_1191_, v_a_1192_, v_a_1193_);
lean_dec_ref(v_a_1192_);
lean_dec(v_a_1191_);
lean_dec(v_a_1190_);
lean_dec(v_a_1189_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg(lean_object* v_x_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_log_1206_; uint8_t v_action_1207_; uint8_t v_wantsRebuild_1208_; uint8_t v_canceled_1209_; lean_object* v_trace_1210_; lean_object* v_buildTime_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1240_; 
v_log_1206_ = lean_ctor_get(v_a_1204_, 0);
v_action_1207_ = lean_ctor_get_uint8(v_a_1204_, sizeof(void*)*3);
v_wantsRebuild_1208_ = lean_ctor_get_uint8(v_a_1204_, sizeof(void*)*3 + 1);
v_canceled_1209_ = lean_ctor_get_uint8(v_a_1204_, sizeof(void*)*3 + 2);
v_trace_1210_ = lean_ctor_get(v_a_1204_, 1);
v_buildTime_1211_ = lean_ctor_get(v_a_1204_, 2);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_a_1204_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1213_ = v_a_1204_;
v_isShared_1214_ = v_isSharedCheck_1240_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_buildTime_1211_);
lean_inc(v_trace_1210_);
lean_inc(v_log_1206_);
lean_dec(v_a_1204_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1240_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v___x_1215_; 
lean_inc_ref(v_a_1203_);
lean_inc(v_a_1202_);
lean_inc(v_a_1201_);
lean_inc(v_a_1200_);
v___x_1215_ = lean_apply_7(v_x_1198_, v_a_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_, v_log_1206_, lean_box(0));
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1227_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
v_a_1217_ = lean_ctor_get(v___x_1215_, 1);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1219_ = v___x_1215_;
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_inc(v_a_1216_);
lean_dec(v___x_1215_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1227_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_a_1217_);
v___x_1222_ = v___x_1213_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1217_);
lean_ctor_set(v_reuseFailAlloc_1226_, 1, v_trace_1210_);
lean_ctor_set(v_reuseFailAlloc_1226_, 2, v_buildTime_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*3, v_action_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*3 + 1, v_wantsRebuild_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1226_, sizeof(void*)*3 + 2, v_canceled_1209_);
v___x_1222_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
lean_object* v___x_1224_; 
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 1, v___x_1222_);
v___x_1224_ = v___x_1219_;
goto v_reusejp_1223_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v_a_1216_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___x_1222_);
v___x_1224_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1223_;
}
v_reusejp_1223_:
{
return v___x_1224_;
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1239_; 
v_a_1228_ = lean_ctor_get(v___x_1215_, 0);
v_a_1229_ = lean_ctor_get(v___x_1215_, 1);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1231_ = v___x_1215_;
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_inc(v_a_1228_);
lean_dec(v___x_1215_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1239_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1214_ == 0)
{
lean_ctor_set(v___x_1213_, 0, v_a_1229_);
v___x_1234_ = v___x_1213_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1229_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v_trace_1210_);
lean_ctor_set(v_reuseFailAlloc_1238_, 2, v_buildTime_1211_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*3, v_action_1207_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*3 + 1, v_wantsRebuild_1208_);
lean_ctor_set_uint8(v_reuseFailAlloc_1238_, sizeof(void*)*3 + 2, v_canceled_1209_);
v___x_1234_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1236_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 1, v___x_1234_);
v___x_1236_ = v___x_1231_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1228_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v___x_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg___boxed(lean_object* v_x_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_, lean_object* v_a_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lake_JobM_runFetchM___redArg(v_x_1241_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_, v_a_1246_, v_a_1247_);
lean_dec_ref(v_a_1246_);
lean_dec(v_a_1245_);
lean_dec(v_a_1244_);
lean_dec(v_a_1243_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM(lean_object* v_00_u03b1_1250_, lean_object* v_x_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v_log_1259_; uint8_t v_action_1260_; uint8_t v_wantsRebuild_1261_; uint8_t v_canceled_1262_; lean_object* v_trace_1263_; lean_object* v_buildTime_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1293_; 
v_log_1259_ = lean_ctor_get(v_a_1257_, 0);
v_action_1260_ = lean_ctor_get_uint8(v_a_1257_, sizeof(void*)*3);
v_wantsRebuild_1261_ = lean_ctor_get_uint8(v_a_1257_, sizeof(void*)*3 + 1);
v_canceled_1262_ = lean_ctor_get_uint8(v_a_1257_, sizeof(void*)*3 + 2);
v_trace_1263_ = lean_ctor_get(v_a_1257_, 1);
v_buildTime_1264_ = lean_ctor_get(v_a_1257_, 2);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_a_1257_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1266_ = v_a_1257_;
v_isShared_1267_ = v_isSharedCheck_1293_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_buildTime_1264_);
lean_inc(v_trace_1263_);
lean_inc(v_log_1259_);
lean_dec(v_a_1257_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1293_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1268_; 
lean_inc_ref(v_a_1256_);
lean_inc(v_a_1255_);
lean_inc(v_a_1254_);
lean_inc(v_a_1253_);
v___x_1268_ = lean_apply_7(v_x_1251_, v_a_1252_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_log_1259_, lean_box(0));
if (lean_obj_tag(v___x_1268_) == 0)
{
lean_object* v_a_1269_; lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1280_; 
v_a_1269_ = lean_ctor_get(v___x_1268_, 0);
v_a_1270_ = lean_ctor_get(v___x_1268_, 1);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1272_ = v___x_1268_;
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_inc(v_a_1269_);
lean_dec(v___x_1268_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1280_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_a_1270_);
v___x_1275_ = v___x_1266_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_a_1270_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v_trace_1263_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_buildTime_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*3, v_action_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*3 + 1, v_wantsRebuild_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1279_, sizeof(void*)*3 + 2, v_canceled_1262_);
v___x_1275_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1277_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 1, v___x_1275_);
v___x_1277_ = v___x_1272_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1269_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1292_; 
v_a_1281_ = lean_ctor_get(v___x_1268_, 0);
v_a_1282_ = lean_ctor_get(v___x_1268_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1268_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1284_ = v___x_1268_;
v_isShared_1285_ = v_isSharedCheck_1292_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_inc(v_a_1281_);
lean_dec(v___x_1268_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1292_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v_a_1282_);
v___x_1287_ = v___x_1266_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1282_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v_trace_1263_);
lean_ctor_set(v_reuseFailAlloc_1291_, 2, v_buildTime_1264_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*3, v_action_1260_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*3 + 1, v_wantsRebuild_1261_);
lean_ctor_set_uint8(v_reuseFailAlloc_1291_, sizeof(void*)*3 + 2, v_canceled_1262_);
v___x_1287_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
lean_object* v___x_1289_; 
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v___x_1287_);
v___x_1289_ = v___x_1284_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1281_);
lean_ctor_set(v_reuseFailAlloc_1290_, 1, v___x_1287_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_x_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Lake_JobM_runFetchM(v_00_u03b1_1294_, v_x_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_);
lean_dec_ref(v_a_1300_);
lean_dec(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec(v_a_1297_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0(lean_object* v_inst_1306_, lean_object* v_caption_1307_, uint8_t v_optional_1308_, lean_object* v_toPure_1309_, lean_object* v_____do__lift_1310_){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; 
v___x_1311_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1311_, 0, v_____do__lift_1310_);
lean_ctor_set(v___x_1311_, 1, v_inst_1306_);
lean_ctor_set(v___x_1311_, 2, v_caption_1307_);
lean_ctor_set_uint8(v___x_1311_, sizeof(void*)*3, v_optional_1308_);
v___x_1312_ = lean_apply_2(v_toPure_1309_, lean_box(0), v___x_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0___boxed(lean_object* v_inst_1313_, lean_object* v_caption_1314_, lean_object* v_optional_1315_, lean_object* v_toPure_1316_, lean_object* v_____do__lift_1317_){
_start:
{
uint8_t v_optional_boxed_1318_; lean_object* v_res_1319_; 
v_optional_boxed_1318_ = lean_unbox(v_optional_1315_);
v_res_1319_ = l_Lake_Job_bindTask___redArg___lam__0(v_inst_1313_, v_caption_1314_, v_optional_boxed_1318_, v_toPure_1316_, v_____do__lift_1317_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg(lean_object* v_inst_1320_, lean_object* v_inst_1321_, lean_object* v_f_1322_, lean_object* v_self_1323_){
_start:
{
lean_object* v_toApplicative_1324_; lean_object* v_toBind_1325_; lean_object* v_task_1326_; lean_object* v_caption_1327_; uint8_t v_optional_1328_; lean_object* v_toPure_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___f_1332_; lean_object* v___x_1333_; 
v_toApplicative_1324_ = lean_ctor_get(v_inst_1320_, 0);
lean_inc_ref(v_toApplicative_1324_);
v_toBind_1325_ = lean_ctor_get(v_inst_1320_, 1);
lean_inc(v_toBind_1325_);
lean_dec_ref(v_inst_1320_);
v_task_1326_ = lean_ctor_get(v_self_1323_, 0);
lean_inc_ref(v_task_1326_);
v_caption_1327_ = lean_ctor_get(v_self_1323_, 2);
lean_inc_ref(v_caption_1327_);
v_optional_1328_ = lean_ctor_get_uint8(v_self_1323_, sizeof(void*)*3);
lean_dec_ref(v_self_1323_);
v_toPure_1329_ = lean_ctor_get(v_toApplicative_1324_, 1);
lean_inc(v_toPure_1329_);
lean_dec_ref(v_toApplicative_1324_);
v___x_1330_ = lean_apply_1(v_f_1322_, v_task_1326_);
v___x_1331_ = lean_box(v_optional_1328_);
v___f_1332_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1332_, 0, v_inst_1321_);
lean_closure_set(v___f_1332_, 1, v_caption_1327_);
lean_closure_set(v___f_1332_, 2, v___x_1331_);
lean_closure_set(v___f_1332_, 3, v_toPure_1329_);
v___x_1333_ = lean_apply_4(v_toBind_1325_, lean_box(0), lean_box(0), v___x_1330_, v___f_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask(lean_object* v_m_1334_, lean_object* v_00_u03b2_1335_, lean_object* v_00_u03b1_1336_, lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_f_1339_, lean_object* v_self_1340_){
_start:
{
lean_object* v_toApplicative_1341_; lean_object* v_toBind_1342_; lean_object* v_task_1343_; lean_object* v_caption_1344_; uint8_t v_optional_1345_; lean_object* v_toPure_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___f_1349_; lean_object* v___x_1350_; 
v_toApplicative_1341_ = lean_ctor_get(v_inst_1337_, 0);
lean_inc_ref(v_toApplicative_1341_);
v_toBind_1342_ = lean_ctor_get(v_inst_1337_, 1);
lean_inc(v_toBind_1342_);
lean_dec_ref(v_inst_1337_);
v_task_1343_ = lean_ctor_get(v_self_1340_, 0);
lean_inc_ref(v_task_1343_);
v_caption_1344_ = lean_ctor_get(v_self_1340_, 2);
lean_inc_ref(v_caption_1344_);
v_optional_1345_ = lean_ctor_get_uint8(v_self_1340_, sizeof(void*)*3);
lean_dec_ref(v_self_1340_);
v_toPure_1346_ = lean_ctor_get(v_toApplicative_1341_, 1);
lean_inc(v_toPure_1346_);
lean_dec_ref(v_toApplicative_1341_);
v___x_1347_ = lean_apply_1(v_f_1339_, v_task_1343_);
v___x_1348_ = lean_box(v_optional_1345_);
v___f_1349_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1349_, 0, v_inst_1338_);
lean_closure_set(v___f_1349_, 1, v_caption_1344_);
lean_closure_set(v___f_1349_, 2, v___x_1348_);
lean_closure_set(v___f_1349_, 3, v_toPure_1346_);
v___x_1350_ = lean_apply_4(v_toBind_1342_, lean_box(0), lean_box(0), v___x_1347_, v___f_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Job_sync_spec__0(lean_object* v_msg_1352_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_1354_ = lean_panic_fn_borrowed(v___x_1353_, v_msg_1352_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0(lean_object* v_val_1355_, lean_object* v_val_1356_, lean_object* v_a_x3f_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1360_ = lean_get_set_stdout(v_val_1355_);
lean_dec_ref(v___x_1360_);
v___x_1361_ = lean_box(0);
v___x_1362_ = lean_get_set_stderr(v_val_1356_);
lean_dec_ref(v___x_1362_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1361_);
lean_ctor_set(v___x_1363_, 1, v___y_1358_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0___boxed(lean_object* v_val_1364_, lean_object* v_val_1365_, lean_object* v_a_x3f_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lake_Job_sync___redArg___lam__0(v_val_1364_, v_val_1365_, v_a_x3f_1366_, v___y_1367_);
lean_dec(v_a_x3f_1366_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1(lean_object* v_a_1370_, lean_object* v_____r_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
lean_object* v___x_1379_; 
v___x_1379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_a_1370_);
lean_ctor_set(v___x_1379_, 1, v___y_1377_);
return v___x_1379_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1___boxed(lean_object* v_a_1380_, lean_object* v_____r_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Lake_Job_sync___redArg___lam__1(v_a_1380_, v_____r_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
return v_res_1389_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__0(void){
_start:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1390_ = lean_unsigned_to_nat(0u);
v___x_1391_ = l_ByteArray_empty;
v___x_1392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
lean_ctor_set(v___x_1392_, 1, v___x_1390_);
return v___x_1392_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__2(void){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1395_ = lean_unsigned_to_nat(0u);
v___x_1396_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1397_ = 0;
v___x_1398_ = 0;
v___x_1399_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1400_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
lean_ctor_set(v___x_1400_, 1, v___x_1396_);
lean_ctor_set(v___x_1400_, 2, v___x_1395_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*3, v___x_1398_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*3 + 1, v___x_1397_);
lean_ctor_set_uint8(v___x_1400_, sizeof(void*)*3 + 2, v___x_1397_);
return v___x_1400_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__7(void){
_start:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1405_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__6));
v___x_1406_ = lean_unsigned_to_nat(46u);
v___x_1407_ = lean_unsigned_to_nat(193u);
v___x_1408_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__5));
v___x_1409_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__4));
v___x_1410_ = l_mkPanicMessageWithDecl(v___x_1409_, v___x_1408_, v___x_1407_, v___x_1406_, v___x_1405_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg(lean_object* v_inst_1411_, lean_object* v_act_1412_, lean_object* v_caption_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_, lean_object* v_a_1418_){
_start:
{
lean_object* v_val_1421_; lean_object* v_a_1426_; lean_object* v_a_1427_; lean_object* v___y_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1433_ = lean_st_mk_ref(v___x_1432_);
lean_inc(v___x_1433_);
v___x_1434_ = l_IO_FS_Stream_ofBuffer(v___x_1433_);
lean_inc_ref(v___x_1434_);
v___x_1435_ = lean_get_set_stdout(v___x_1434_);
v___x_1436_ = lean_get_set_stderr(v___x_1434_);
v___x_1437_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__2, &l_Lake_Job_sync___redArg___closed__2_once, _init_l_Lake_Job_sync___redArg___closed__2);
lean_inc_ref(v_a_1418_);
lean_inc(v_a_1417_);
lean_inc(v_a_1416_);
lean_inc(v_a_1415_);
lean_inc_ref(v_a_1414_);
v___x_1438_ = lean_apply_7(v_act_1412_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v___x_1437_, lean_box(0));
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; lean_object* v_a_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_a_1443_; lean_object* v_log_1444_; uint8_t v_action_1445_; uint8_t v_wantsRebuild_1446_; uint8_t v_canceled_1447_; lean_object* v_trace_1448_; lean_object* v_buildTime_1449_; lean_object* v___x_1450_; lean_object* v___y_1452_; lean_object* v_data_1477_; uint8_t v___x_1478_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_n(v_a_1439_, 2);
v_a_1440_ = lean_ctor_get(v___x_1438_, 1);
lean_inc(v_a_1440_);
lean_dec_ref_known(v___x_1438_, 2);
v___x_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1441_, 0, v_a_1439_);
v___x_1442_ = l_Lake_Job_sync___redArg___lam__0(v___x_1435_, v___x_1436_, v___x_1441_, v_a_1440_);
lean_dec_ref_known(v___x_1441_, 1);
v_a_1443_ = lean_ctor_get(v___x_1442_, 1);
lean_inc(v_a_1443_);
lean_dec_ref(v___x_1442_);
v_log_1444_ = lean_ctor_get(v_a_1443_, 0);
v_action_1445_ = lean_ctor_get_uint8(v_a_1443_, sizeof(void*)*3);
v_wantsRebuild_1446_ = lean_ctor_get_uint8(v_a_1443_, sizeof(void*)*3 + 1);
v_canceled_1447_ = lean_ctor_get_uint8(v_a_1443_, sizeof(void*)*3 + 2);
v_trace_1448_ = lean_ctor_get(v_a_1443_, 1);
v_buildTime_1449_ = lean_ctor_get(v_a_1443_, 2);
v___x_1450_ = lean_st_ref_get(v___x_1433_);
lean_dec(v___x_1433_);
v_data_1477_ = lean_ctor_get(v___x_1450_, 0);
lean_inc_ref(v_data_1477_);
lean_dec(v___x_1450_);
v___x_1478_ = lean_string_validate_utf8(v_data_1477_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
lean_dec_ref(v_data_1477_);
v___x_1479_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1480_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1479_);
v___y_1452_ = v___x_1480_;
goto v___jp_1451_;
}
else
{
lean_object* v___x_1481_; 
v___x_1481_ = lean_string_from_utf8_unchecked(v_data_1477_);
v___y_1452_ = v___x_1481_;
goto v___jp_1451_;
}
v___jp_1451_:
{
lean_object* v___x_1453_; uint8_t v___x_1454_; 
v___x_1453_ = lean_string_utf8_byte_size(v___y_1452_);
v___x_1454_ = lean_nat_dec_eq(v___x_1453_, v___x_1431_);
if (v___x_1454_ == 0)
{
lean_object* v___x_1456_; uint8_t v_isShared_1457_; uint8_t v_isSharedCheck_1471_; 
lean_inc(v_buildTime_1449_);
lean_inc_ref(v_trace_1448_);
lean_inc_ref(v_log_1444_);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_a_1443_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; lean_object* v_unused_1473_; lean_object* v_unused_1474_; 
v_unused_1472_ = lean_ctor_get(v_a_1443_, 2);
lean_dec(v_unused_1472_);
v_unused_1473_ = lean_ctor_get(v_a_1443_, 1);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_a_1443_, 0);
lean_dec(v_unused_1474_);
v___x_1456_ = v_a_1443_;
v_isShared_1457_ = v_isSharedCheck_1471_;
goto v_resetjp_1455_;
}
else
{
lean_dec(v_a_1443_);
v___x_1456_ = lean_box(0);
v_isShared_1457_ = v_isSharedCheck_1471_;
goto v_resetjp_1455_;
}
v_resetjp_1455_:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; 
v___x_1458_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1459_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1459_, 0, v___y_1452_);
lean_ctor_set(v___x_1459_, 1, v___x_1431_);
lean_ctor_set(v___x_1459_, 2, v___x_1453_);
v___x_1460_ = l_String_Slice_trimAscii(v___x_1459_);
v___x_1461_ = l_String_Slice_toString(v___x_1460_);
lean_dec_ref(v___x_1460_);
v___x_1462_ = lean_string_append(v___x_1458_, v___x_1461_);
lean_dec_ref(v___x_1461_);
v___x_1463_ = 1;
v___x_1464_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1464_, 0, v___x_1462_);
lean_ctor_set_uint8(v___x_1464_, sizeof(void*)*1, v___x_1463_);
v___x_1465_ = lean_box(0);
v___x_1466_ = lean_array_push(v_log_1444_, v___x_1464_);
if (v_isShared_1457_ == 0)
{
lean_ctor_set(v___x_1456_, 0, v___x_1466_);
v___x_1468_ = v___x_1456_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v___x_1466_);
lean_ctor_set(v_reuseFailAlloc_1470_, 1, v_trace_1448_);
lean_ctor_set(v_reuseFailAlloc_1470_, 2, v_buildTime_1449_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*3, v_action_1445_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*3 + 1, v_wantsRebuild_1446_);
lean_ctor_set_uint8(v_reuseFailAlloc_1470_, sizeof(void*)*3 + 2, v_canceled_1447_);
v___x_1468_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Lake_Job_sync___redArg___lam__1(v_a_1439_, v___x_1465_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v___x_1468_);
lean_dec_ref(v_a_1414_);
v___y_1430_ = v___x_1469_;
goto v___jp_1429_;
}
}
}
else
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
lean_dec_ref(v___y_1452_);
v___x_1475_ = lean_box(0);
v___x_1476_ = l_Lake_Job_sync___redArg___lam__1(v_a_1439_, v___x_1475_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1443_);
lean_dec_ref(v_a_1414_);
v___y_1430_ = v___x_1476_;
goto v___jp_1429_;
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v_a_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v_a_1486_; 
lean_dec(v___x_1433_);
lean_dec_ref(v_a_1414_);
v_a_1482_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1482_);
v_a_1483_ = lean_ctor_get(v___x_1438_, 1);
lean_inc(v_a_1483_);
lean_dec_ref_known(v___x_1438_, 2);
v___x_1484_ = lean_box(0);
v___x_1485_ = l_Lake_Job_sync___redArg___lam__0(v___x_1435_, v___x_1436_, v___x_1484_, v_a_1483_);
v_a_1486_ = lean_ctor_get(v___x_1485_, 1);
lean_inc(v_a_1486_);
lean_dec_ref(v___x_1485_);
v_a_1426_ = v_a_1482_;
v_a_1427_ = v_a_1486_;
goto v___jp_1425_;
}
v___jp_1420_:
{
lean_object* v___x_1422_; uint8_t v___x_1423_; lean_object* v___x_1424_; 
v___x_1422_ = lean_task_pure(v_val_1421_);
v___x_1423_ = 0;
v___x_1424_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1424_, 0, v___x_1422_);
lean_ctor_set(v___x_1424_, 1, v_inst_1411_);
lean_ctor_set(v___x_1424_, 2, v_caption_1413_);
lean_ctor_set_uint8(v___x_1424_, sizeof(void*)*3, v___x_1423_);
return v___x_1424_;
}
v___jp_1425_:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_a_1426_);
lean_ctor_set(v___x_1428_, 1, v_a_1427_);
v_val_1421_ = v___x_1428_;
goto v___jp_1420_;
}
v___jp_1429_:
{
v_val_1421_ = v___y_1430_;
goto v___jp_1420_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___boxed(lean_object* v_inst_1487_, lean_object* v_act_1488_, lean_object* v_caption_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_, lean_object* v_a_1492_, lean_object* v_a_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lake_Job_sync___redArg(v_inst_1487_, v_act_1488_, v_caption_1489_, v_a_1490_, v_a_1491_, v_a_1492_, v_a_1493_, v_a_1494_);
lean_dec_ref(v_a_1494_);
lean_dec(v_a_1493_);
lean_dec(v_a_1492_);
lean_dec(v_a_1491_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync(lean_object* v_00_u03b1_1497_, lean_object* v_inst_1498_, lean_object* v_act_1499_, lean_object* v_caption_1500_, lean_object* v_a_1501_, lean_object* v_a_1502_, lean_object* v_a_1503_, lean_object* v_a_1504_, lean_object* v_a_1505_, lean_object* v_a_1506_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lake_Job_sync___redArg(v_inst_1498_, v_act_1499_, v_caption_1500_, v_a_1501_, v_a_1502_, v_a_1503_, v_a_1504_, v_a_1505_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___boxed(lean_object* v_00_u03b1_1509_, lean_object* v_inst_1510_, lean_object* v_act_1511_, lean_object* v_caption_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lake_Job_sync(v_00_u03b1_1509_, v_inst_1510_, v_act_1511_, v_caption_1512_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
lean_dec_ref(v_a_1518_);
lean_dec_ref(v_a_1517_);
lean_dec(v_a_1516_);
lean_dec(v_a_1515_);
lean_dec(v_a_1514_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1(lean_object* v___x_1521_, lean_object* v___x_1522_, uint8_t v___x_1523_, uint8_t v___x_1524_, lean_object* v___x_1525_, lean_object* v___x_1526_, lean_object* v_act_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_a_1535_; lean_object* v_a_1536_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1538_ = lean_st_mk_ref(v___x_1521_);
lean_inc(v___x_1538_);
v___x_1539_ = l_IO_FS_Stream_ofBuffer(v___x_1538_);
lean_inc_ref(v___x_1539_);
v___x_1540_ = lean_get_set_stdout(v___x_1539_);
v___x_1541_ = lean_get_set_stderr(v___x_1539_);
lean_inc(v___x_1526_);
v___x_1542_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1542_, 0, v___x_1522_);
lean_ctor_set(v___x_1542_, 1, v___x_1525_);
lean_ctor_set(v___x_1542_, 2, v___x_1526_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*3, v___x_1523_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*3 + 1, v___x_1524_);
lean_ctor_set_uint8(v___x_1542_, sizeof(void*)*3 + 2, v___x_1524_);
lean_inc_ref(v_a_1532_);
lean_inc(v_a_1531_);
lean_inc(v_a_1530_);
lean_inc(v_a_1529_);
v___x_1543_ = lean_apply_7(v_act_1527_, v_a_1528_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_, v___x_1542_, lean_box(0));
if (lean_obj_tag(v___x_1543_) == 0)
{
lean_object* v_a_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1591_; 
v_a_1544_ = lean_ctor_get(v___x_1543_, 0);
v_a_1545_ = lean_ctor_get(v___x_1543_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1543_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1547_ = v___x_1543_;
v_isShared_1548_ = v_isSharedCheck_1591_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_inc(v_a_1544_);
lean_dec(v___x_1543_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1591_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___y_1550_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v_a_1556_; lean_object* v_log_1557_; uint8_t v_action_1558_; uint8_t v_wantsRebuild_1559_; uint8_t v_canceled_1560_; lean_object* v_trace_1561_; lean_object* v_buildTime_1562_; lean_object* v___x_1563_; lean_object* v___y_1565_; lean_object* v_data_1586_; uint8_t v___x_1587_; 
lean_inc(v_a_1544_);
v___x_1554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1554_, 0, v_a_1544_);
v___x_1555_ = l_Lake_Job_sync___redArg___lam__0(v___x_1540_, v___x_1541_, v___x_1554_, v_a_1545_);
lean_dec_ref_known(v___x_1554_, 1);
v_a_1556_ = lean_ctor_get(v___x_1555_, 1);
lean_inc(v_a_1556_);
lean_dec_ref(v___x_1555_);
v_log_1557_ = lean_ctor_get(v_a_1556_, 0);
v_action_1558_ = lean_ctor_get_uint8(v_a_1556_, sizeof(void*)*3);
v_wantsRebuild_1559_ = lean_ctor_get_uint8(v_a_1556_, sizeof(void*)*3 + 1);
v_canceled_1560_ = lean_ctor_get_uint8(v_a_1556_, sizeof(void*)*3 + 2);
v_trace_1561_ = lean_ctor_get(v_a_1556_, 1);
v_buildTime_1562_ = lean_ctor_get(v_a_1556_, 2);
v___x_1563_ = lean_st_ref_get(v___x_1538_);
lean_dec(v___x_1538_);
v_data_1586_ = lean_ctor_get(v___x_1563_, 0);
lean_inc_ref(v_data_1586_);
lean_dec(v___x_1563_);
v___x_1587_ = lean_string_validate_utf8(v_data_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; lean_object* v___x_1589_; 
lean_dec_ref(v_data_1586_);
v___x_1588_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1589_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1588_);
v___y_1565_ = v___x_1589_;
goto v___jp_1564_;
}
else
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_string_from_utf8_unchecked(v_data_1586_);
v___y_1565_ = v___x_1590_;
goto v___jp_1564_;
}
v___jp_1549_:
{
lean_object* v___x_1552_; 
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 1, v___y_1550_);
v___x_1552_ = v___x_1547_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1544_);
lean_ctor_set(v_reuseFailAlloc_1553_, 1, v___y_1550_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
v___jp_1564_:
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_string_utf8_byte_size(v___y_1565_);
v___x_1567_ = lean_nat_dec_eq(v___x_1566_, v___x_1526_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1582_; 
lean_inc(v_buildTime_1562_);
lean_inc_ref(v_trace_1561_);
lean_inc_ref(v_log_1557_);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_a_1556_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; lean_object* v_unused_1584_; lean_object* v_unused_1585_; 
v_unused_1583_ = lean_ctor_get(v_a_1556_, 2);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_a_1556_, 1);
lean_dec(v_unused_1584_);
v_unused_1585_ = lean_ctor_get(v_a_1556_, 0);
lean_dec(v_unused_1585_);
v___x_1569_ = v_a_1556_;
v_isShared_1570_ = v_isSharedCheck_1582_;
goto v_resetjp_1568_;
}
else
{
lean_dec(v_a_1556_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1582_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1571_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1572_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1572_, 0, v___y_1565_);
lean_ctor_set(v___x_1572_, 1, v___x_1526_);
lean_ctor_set(v___x_1572_, 2, v___x_1566_);
v___x_1573_ = l_String_Slice_trimAscii(v___x_1572_);
v___x_1574_ = l_String_Slice_toString(v___x_1573_);
lean_dec_ref(v___x_1573_);
v___x_1575_ = lean_string_append(v___x_1571_, v___x_1574_);
lean_dec_ref(v___x_1574_);
v___x_1576_ = 1;
v___x_1577_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1577_, 0, v___x_1575_);
lean_ctor_set_uint8(v___x_1577_, sizeof(void*)*1, v___x_1576_);
v___x_1578_ = lean_array_push(v_log_1557_, v___x_1577_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1578_);
v___x_1580_ = v___x_1569_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v_trace_1561_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_buildTime_1562_);
lean_ctor_set_uint8(v_reuseFailAlloc_1581_, sizeof(void*)*3, v_action_1558_);
lean_ctor_set_uint8(v_reuseFailAlloc_1581_, sizeof(void*)*3 + 1, v_wantsRebuild_1559_);
lean_ctor_set_uint8(v_reuseFailAlloc_1581_, sizeof(void*)*3 + 2, v_canceled_1560_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
v___y_1550_ = v___x_1580_;
goto v___jp_1549_;
}
}
}
else
{
lean_dec_ref(v___y_1565_);
lean_dec(v___x_1526_);
v___y_1550_ = v_a_1556_;
goto v___jp_1549_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v_a_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v_a_1596_; 
lean_dec(v___x_1538_);
lean_dec(v___x_1526_);
v_a_1592_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_a_1592_);
v_a_1593_ = lean_ctor_get(v___x_1543_, 1);
lean_inc(v_a_1593_);
lean_dec_ref_known(v___x_1543_, 2);
v___x_1594_ = lean_box(0);
v___x_1595_ = l_Lake_Job_sync___redArg___lam__0(v___x_1540_, v___x_1541_, v___x_1594_, v_a_1593_);
v_a_1596_ = lean_ctor_get(v___x_1595_, 1);
lean_inc(v_a_1596_);
lean_dec_ref(v___x_1595_);
v_a_1535_ = v_a_1592_;
v_a_1536_ = v_a_1596_;
goto v___jp_1534_;
}
v___jp_1534_:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1537_, 0, v_a_1535_);
lean_ctor_set(v___x_1537_, 1, v_a_1536_);
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1___boxed(lean_object* v___x_1597_, lean_object* v___x_1598_, lean_object* v___x_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v___x_1602_, lean_object* v_act_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v___y_1609_){
_start:
{
uint8_t v___x_23069__boxed_1610_; uint8_t v___x_23070__boxed_1611_; lean_object* v_res_1612_; 
v___x_23069__boxed_1610_ = lean_unbox(v___x_1599_);
v___x_23070__boxed_1611_ = lean_unbox(v___x_1600_);
v_res_1612_ = l_Lake_Job_async___redArg___lam__1(v___x_1597_, v___x_1598_, v___x_23069__boxed_1610_, v___x_23070__boxed_1611_, v___x_1601_, v___x_1602_, v_act_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec_ref(v_a_1608_);
lean_dec(v_a_1607_);
lean_dec(v_a_1606_);
lean_dec(v_a_1605_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg(lean_object* v_inst_1613_, lean_object* v_act_1614_, lean_object* v_prio_1615_, lean_object* v_caption_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; uint8_t v___x_1626_; uint8_t v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___f_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1625_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1626_ = 0;
v___x_1627_ = 0;
v___x_1628_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1629_ = lean_box(v___x_1626_);
v___x_1630_ = lean_box(v___x_1627_);
lean_inc_ref(v_a_1621_);
lean_inc(v_a_1620_);
lean_inc(v_a_1619_);
lean_inc(v_a_1618_);
v___f_1631_ = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__1___boxed), 13, 12);
lean_closure_set(v___f_1631_, 0, v___x_1624_);
lean_closure_set(v___f_1631_, 1, v___x_1625_);
lean_closure_set(v___f_1631_, 2, v___x_1629_);
lean_closure_set(v___f_1631_, 3, v___x_1630_);
lean_closure_set(v___f_1631_, 4, v___x_1628_);
lean_closure_set(v___f_1631_, 5, v___x_1623_);
lean_closure_set(v___f_1631_, 6, v_act_1614_);
lean_closure_set(v___f_1631_, 7, v_a_1617_);
lean_closure_set(v___f_1631_, 8, v_a_1618_);
lean_closure_set(v___f_1631_, 9, v_a_1619_);
lean_closure_set(v___f_1631_, 10, v_a_1620_);
lean_closure_set(v___f_1631_, 11, v_a_1621_);
v___x_1632_ = lean_io_as_task(v___f_1631_, v_prio_1615_);
v___x_1633_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v_inst_1613_);
lean_ctor_set(v___x_1633_, 2, v_caption_1616_);
lean_ctor_set_uint8(v___x_1633_, sizeof(void*)*3, v___x_1627_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___boxed(lean_object* v_inst_1634_, lean_object* v_act_1635_, lean_object* v_prio_1636_, lean_object* v_caption_1637_, lean_object* v_a_1638_, lean_object* v_a_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lake_Job_async___redArg(v_inst_1634_, v_act_1635_, v_prio_1636_, v_caption_1637_, v_a_1638_, v_a_1639_, v_a_1640_, v_a_1641_, v_a_1642_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec(v_a_1640_);
lean_dec(v_a_1639_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async(lean_object* v_00_u03b1_1645_, lean_object* v_inst_1646_, lean_object* v_act_1647_, lean_object* v_prio_1648_, lean_object* v_caption_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lake_Job_async___redArg(v_inst_1646_, v_act_1647_, v_prio_1648_, v_caption_1649_, v_a_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___boxed(lean_object* v_00_u03b1_1658_, lean_object* v_inst_1659_, lean_object* v_act_1660_, lean_object* v_prio_1661_, lean_object* v_caption_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Lake_Job_async(v_00_u03b1_1658_, v_inst_1659_, v_act_1660_, v_prio_1661_, v_caption_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
lean_dec_ref(v_a_1668_);
lean_dec_ref(v_a_1667_);
lean_dec(v_a_1666_);
lean_dec(v_a_1665_);
lean_dec(v_a_1664_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg(lean_object* v_self_1671_){
_start:
{
lean_object* v_task_1673_; lean_object* v___x_1674_; 
v_task_1673_ = lean_ctor_get(v_self_1671_, 0);
lean_inc_ref(v_task_1673_);
lean_dec_ref(v_self_1671_);
v___x_1674_ = lean_io_wait(v_task_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg___boxed(lean_object* v_self_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lake_Job_wait___redArg(v_self_1675_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait(lean_object* v_00_u03b1_1678_, lean_object* v_self_1679_){
_start:
{
lean_object* v_task_1681_; lean_object* v___x_1682_; 
v_task_1681_ = lean_ctor_get(v_self_1679_, 0);
lean_inc_ref(v_task_1681_);
lean_dec_ref(v_self_1679_);
v___x_1682_ = lean_io_wait(v_task_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___boxed(lean_object* v_00_u03b1_1683_, lean_object* v_self_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lake_Job_wait(v_00_u03b1_1683_, v_self_1684_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg(lean_object* v_self_1687_){
_start:
{
lean_object* v_task_1689_; lean_object* v___x_1690_; 
v_task_1689_ = lean_ctor_get(v_self_1687_, 0);
lean_inc_ref(v_task_1689_);
lean_dec_ref(v_self_1687_);
v___x_1690_ = lean_io_wait(v_task_1689_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 2);
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v_a_1691_);
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; 
lean_dec_ref_known(v___x_1690_, 2);
v___x_1693_ = lean_box(0);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg___boxed(lean_object* v_self_1694_, lean_object* v_a_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lake_Job_wait_x3f___redArg(v_self_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f(lean_object* v_00_u03b1_1697_, lean_object* v_self_1698_){
_start:
{
lean_object* v_task_1700_; lean_object* v___x_1701_; 
v_task_1700_ = lean_ctor_get(v_self_1698_, 0);
lean_inc_ref(v_task_1700_);
lean_dec_ref(v_self_1698_);
v___x_1701_ = lean_io_wait(v_task_1700_);
if (lean_obj_tag(v___x_1701_) == 0)
{
lean_object* v_a_1702_; lean_object* v___x_1703_; 
v_a_1702_ = lean_ctor_get(v___x_1701_, 0);
lean_inc(v_a_1702_);
lean_dec_ref_known(v___x_1701_, 2);
v___x_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_a_1702_);
return v___x_1703_;
}
else
{
lean_object* v___x_1704_; 
lean_dec_ref_known(v___x_1701_, 2);
v___x_1704_ = lean_box(0);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___boxed(lean_object* v_00_u03b1_1705_, lean_object* v_self_1706_, lean_object* v_a_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Lake_Job_wait_x3f(v_00_u03b1_1705_, v_self_1706_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(lean_object* v_as_1709_, size_t v_i_1710_, size_t v_stop_1711_, lean_object* v_b_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_usize_dec_eq(v_i_1710_, v_stop_1711_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; size_t v___x_1719_; size_t v___x_1720_; 
v___x_1716_ = lean_array_uget_borrowed(v_as_1709_, v_i_1710_);
v___x_1717_ = lean_box(0);
lean_inc(v___x_1716_);
v___x_1718_ = lean_array_push(v___y_1713_, v___x_1716_);
v___x_1719_ = ((size_t)1ULL);
v___x_1720_ = lean_usize_add(v_i_1710_, v___x_1719_);
v_i_1710_ = v___x_1720_;
v_b_1712_ = v___x_1717_;
v___y_1713_ = v___x_1718_;
goto _start;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1722_, 0, v_b_1712_);
lean_ctor_set(v___x_1722_, 1, v___y_1713_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0___boxed(lean_object* v_as_1723_, lean_object* v_i_1724_, lean_object* v_stop_1725_, lean_object* v_b_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
size_t v_i_boxed_1729_; size_t v_stop_boxed_1730_; lean_object* v_res_1731_; 
v_i_boxed_1729_ = lean_unbox_usize(v_i_1724_);
lean_dec(v_i_1724_);
v_stop_boxed_1730_ = lean_unbox_usize(v_stop_1725_);
lean_dec(v_stop_1725_);
v_res_1731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_as_1723_, v_i_boxed_1729_, v_stop_boxed_1730_, v_b_1726_, v___y_1727_);
lean_dec_ref(v_as_1723_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg(lean_object* v_self_1732_, lean_object* v_a_1733_){
_start:
{
lean_object* v_task_1735_; lean_object* v___x_1736_; 
v_task_1735_ = lean_ctor_get(v_self_1732_, 0);
lean_inc_ref(v_task_1735_);
lean_dec_ref(v_self_1732_);
v___x_1736_ = lean_io_wait(v_task_1735_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_a_1737_; lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1765_; 
v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
v_a_1738_ = lean_ctor_get(v___x_1736_, 1);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1740_ = v___x_1736_;
v_isShared_1741_ = v_isSharedCheck_1765_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_inc(v_a_1737_);
lean_dec(v___x_1736_);
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
v_a_1743_ = v_a_1733_;
goto v___jp_1742_;
}
else
{
lean_object* v___x_1751_; size_t v___x_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1751_ = lean_box(0);
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = lean_usize_of_nat(v___x_1749_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1747_, v___x_1752_, v___x_1753_, v___x_1751_, v_a_1733_);
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
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_1766_; lean_object* v_a_1767_; lean_object* v___x_1769_; uint8_t v_isShared_1770_; uint8_t v_isSharedCheck_1794_; 
v_a_1766_ = lean_ctor_get(v___x_1736_, 0);
v_a_1767_ = lean_ctor_get(v___x_1736_, 1);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1736_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1769_ = v___x_1736_;
v_isShared_1770_ = v_isSharedCheck_1794_;
goto v_resetjp_1768_;
}
else
{
lean_inc(v_a_1767_);
lean_inc(v_a_1766_);
lean_dec(v___x_1736_);
v___x_1769_ = lean_box(0);
v_isShared_1770_ = v_isSharedCheck_1794_;
goto v_resetjp_1768_;
}
v_resetjp_1768_:
{
lean_object* v_a_1772_; lean_object* v_log_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v_log_1776_ = lean_ctor_get(v_a_1767_, 0);
lean_inc_ref(v_log_1776_);
lean_dec(v_a_1767_);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = lean_array_get_size(v_log_1776_);
v___x_1779_ = lean_nat_dec_lt(v___x_1777_, v___x_1778_);
if (v___x_1779_ == 0)
{
lean_dec_ref(v_log_1776_);
v_a_1772_ = v_a_1733_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1780_; size_t v___x_1781_; size_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1780_ = lean_box(0);
v___x_1781_ = ((size_t)0ULL);
v___x_1782_ = lean_usize_of_nat(v___x_1778_);
v___x_1783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1776_, v___x_1781_, v___x_1782_, v___x_1780_, v_a_1733_);
lean_dec_ref(v_log_1776_);
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
lean_del_object(v___x_1769_);
lean_dec(v_a_1766_);
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
lean_object* v___x_1774_; 
if (v_isShared_1770_ == 0)
{
lean_ctor_set(v___x_1769_, 1, v_a_1772_);
v___x_1774_ = v___x_1769_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1775_; 
v_reuseFailAlloc_1775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1775_, 0, v_a_1766_);
lean_ctor_set(v_reuseFailAlloc_1775_, 1, v_a_1772_);
v___x_1774_ = v_reuseFailAlloc_1775_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
return v___x_1774_;
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
lean_dec(v_a_1842_);
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
lean_dec(v_a_1893_);
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
lean_object* v_a_1949_; lean_object* v_a_1950_; lean_object* v___y_1953_; lean_object* v___y_1954_; uint8_t v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; uint8_t v___y_1962_; lean_object* v___y_1963_; lean_object* v___y_1964_; uint8_t v___y_1965_; lean_object* v___y_1966_; 
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
lean_inc(v_a_1945_);
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
v___y_1957_ = v_wantsRebuild_2010_;
v___y_1958_ = v_a_2007_;
v___y_1959_ = v___x_1994_;
v___y_1960_ = v_a_2003_;
v___y_1961_ = v_trace_2012_;
v___y_1962_ = v_canceled_2011_;
v___y_1963_ = v_log_2008_;
v___y_1964_ = v_buildTime_2013_;
v___y_1965_ = v_action_2009_;
v___y_1966_ = v___x_2018_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_string_from_utf8_unchecked(v_data_2015_);
v___y_1957_ = v_wantsRebuild_2010_;
v___y_1958_ = v_a_2007_;
v___y_1959_ = v___x_1994_;
v___y_1960_ = v_a_2003_;
v___y_1961_ = v_trace_2012_;
v___y_1962_ = v_canceled_2011_;
v___y_1963_ = v_log_2008_;
v___y_1964_ = v_buildTime_2013_;
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
v___x_1968_ = lean_nat_dec_eq(v___x_1967_, v___y_1959_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec_ref(v___y_1958_);
v___x_1969_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1970_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1970_, 0, v___y_1966_);
lean_ctor_set(v___x_1970_, 1, v___y_1959_);
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
v___x_1976_ = lean_array_push(v___y_1963_, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
lean_ctor_set(v___x_1977_, 1, v___y_1961_);
lean_ctor_set(v___x_1977_, 2, v___y_1964_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*3, v___y_1965_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*3 + 1, v___y_1957_);
lean_ctor_set_uint8(v___x_1977_, sizeof(void*)*3 + 2, v___y_1962_);
v___y_1953_ = v___y_1960_;
v___y_1954_ = v___x_1977_;
goto v___jp_1952_;
}
else
{
lean_dec_ref(v___y_1966_);
lean_dec(v___y_1964_);
lean_dec_ref(v___y_1963_);
lean_dec_ref(v___y_1961_);
lean_dec(v___y_1959_);
v___y_1953_ = v___y_1960_;
v___y_1954_ = v___y_1958_;
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
lean_dec(v_a_2064_);
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
lean_inc(v_a_2076_);
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
lean_dec(v_a_2101_);
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
lean_dec(v_a_2132_);
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
lean_dec(v___y_2223_);
lean_dec(v___y_2222_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3(lean_object* v_a_2228_, lean_object* v_prio_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_f_2235_, lean_object* v_x_2236_){
_start:
{
lean_object* v_a_2239_; lean_object* v_a_2240_; lean_object* v___y_2244_; uint8_t v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; uint8_t v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; uint8_t v___y_2262_; lean_object* v___y_2263_; 
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
lean_inc(v_a_2233_);
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
v___y_2254_ = v_action_2311_;
v___y_2255_ = v_trace_2314_;
v___y_2256_ = v___f_2306_;
v___y_2257_ = v_log_2310_;
v___y_2258_ = v_wantsRebuild_2312_;
v___y_2259_ = v_buildTime_2315_;
v___y_2260_ = v___x_2295_;
v___y_2261_ = v_a_2309_;
v___y_2262_ = v_canceled_2313_;
v___y_2263_ = v___x_2320_;
goto v___jp_2253_;
}
else
{
lean_object* v___x_2321_; 
v___x_2321_ = lean_string_from_utf8_unchecked(v_data_2317_);
v___y_2254_ = v_action_2311_;
v___y_2255_ = v_trace_2314_;
v___y_2256_ = v___f_2306_;
v___y_2257_ = v_log_2310_;
v___y_2258_ = v_wantsRebuild_2312_;
v___y_2259_ = v_buildTime_2315_;
v___y_2260_ = v___x_2295_;
v___y_2261_ = v_a_2309_;
v___y_2262_ = v_canceled_2313_;
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
v___x_2265_ = lean_nat_dec_eq(v___x_2264_, v___y_2260_);
if (v___x_2265_ == 0)
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; uint8_t v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
lean_dec_ref(v___y_2261_);
v___x_2266_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_2267_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2267_, 0, v___y_2263_);
lean_ctor_set(v___x_2267_, 1, v___y_2260_);
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
v___x_2274_ = lean_array_push(v___y_2257_, v___x_2272_);
v___x_2275_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___y_2255_);
lean_ctor_set(v___x_2275_, 2, v___y_2259_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*3, v___y_2254_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*3 + 1, v___y_2258_);
lean_ctor_set_uint8(v___x_2275_, sizeof(void*)*3 + 2, v___y_2262_);
lean_inc_ref(v_a_2228_);
lean_inc(v_a_2233_);
lean_inc(v_a_2232_);
lean_inc(v_a_2231_);
v___x_2276_ = lean_apply_8(v___y_2256_, v___x_2273_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2228_, v___x_2275_, lean_box(0));
v___y_2244_ = v___x_2276_;
goto v___jp_2243_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v___y_2255_);
v___x_2277_ = lean_box(0);
lean_inc_ref(v_a_2228_);
lean_inc(v_a_2233_);
lean_inc(v_a_2232_);
lean_inc(v_a_2231_);
v___x_2278_ = lean_apply_8(v___y_2256_, v___x_2277_, v_a_2230_, v_a_2231_, v_a_2232_, v_a_2233_, v_a_2228_, v___y_2261_, lean_box(0));
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
lean_dec(v_a_2367_);
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
lean_inc(v_a_2381_);
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
lean_dec(v_a_2406_);
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
lean_dec(v_a_2437_);
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
v___y_2538_ = v___x_2561_;
v___y_2539_ = v_ry_2530_;
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
v_a_2541_ = lean_ctor_get(v___y_2539_, 1);
lean_inc(v_a_2541_);
lean_dec_ref(v___y_2539_);
v___y_2532_ = v___y_2538_;
v___y_2533_ = v___y_2540_;
v___y_2534_ = v_a_2541_;
goto v___jp_2531_;
}
v___jp_2542_:
{
lean_object* v___x_2544_; 
v___x_2544_ = lean_unsigned_to_nat(0u);
v___y_2538_ = v___x_2544_;
v___y_2539_ = v_ry_2530_;
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
v___y_2617_ = v___x_2641_;
v___y_2618_ = v_ry_2609_;
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
v_a_2620_ = lean_ctor_get(v___y_2618_, 1);
lean_inc(v_a_2620_);
lean_dec_ref(v___y_2618_);
v___y_2611_ = v___y_2617_;
v___y_2612_ = v___y_2619_;
v___y_2613_ = v_a_2620_;
goto v___jp_2610_;
}
v___jp_2621_:
{
lean_object* v___x_2624_; 
v___x_2624_ = lean_unsigned_to_nat(0u);
v___y_2617_ = v___x_2624_;
v___y_2618_ = v_rb_2623_;
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
uint8_t v___x_2946_; 
v___x_2946_ = lean_nat_dec_le(v___x_2944_, v___x_2944_);
if (v___x_2946_ == 0)
{
if (v___x_2945_ == 0)
{
return v___x_2943_;
}
else
{
size_t v___x_2947_; size_t v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = ((size_t)0ULL);
v___x_2948_ = lean_usize_of_nat(v___x_2944_);
v___x_2949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2930_, v___x_2947_, v___x_2948_, v___x_2943_);
return v___x_2949_;
}
}
else
{
size_t v___x_2950_; size_t v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = ((size_t)0ULL);
v___x_2951_ = lean_usize_of_nat(v___x_2944_);
v___x_2952_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2930_, v___x_2950_, v___x_2951_, v___x_2943_);
return v___x_2952_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object* v_jobs_2953_, lean_object* v_traceCaption_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Lake_Job_mixArray___redArg(v_jobs_2953_, v_traceCaption_2954_);
lean_dec_ref(v_jobs_2953_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object* v_00_u03b1_2956_, lean_object* v_jobs_2957_, lean_object* v_traceCaption_2958_){
_start:
{
lean_object* v___x_2959_; 
v___x_2959_ = l_Lake_Job_mixArray___redArg(v_jobs_2957_, v_traceCaption_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object* v_00_u03b1_2960_, lean_object* v_jobs_2961_, lean_object* v_traceCaption_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lake_Job_mixArray(v_00_u03b1_2960_, v_jobs_2961_, v_traceCaption_2962_);
lean_dec_ref(v_jobs_2961_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_object* v_00_u03b1_2964_, lean_object* v_as_2965_, size_t v_i_2966_, size_t v_stop_2967_, lean_object* v_b_2968_){
_start:
{
lean_object* v___x_2969_; 
v___x_2969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2965_, v_i_2966_, v_stop_2967_, v_b_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(lean_object* v_00_u03b1_2970_, lean_object* v_as_2971_, lean_object* v_i_2972_, lean_object* v_stop_2973_, lean_object* v_b_2974_){
_start:
{
size_t v_i_boxed_2975_; size_t v_stop_boxed_2976_; lean_object* v_res_2977_; 
v_i_boxed_2975_ = lean_unbox_usize(v_i_2972_);
lean_dec(v_i_2972_);
v_stop_boxed_2976_ = lean_unbox_usize(v_stop_2973_);
lean_dec(v_stop_2973_);
v_res_2977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(v_00_u03b1_2970_, v_as_2971_, v_i_boxed_2975_, v_stop_boxed_2976_, v_b_2974_);
lean_dec_ref(v_as_2971_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object* v___x_2978_, lean_object* v_rx_2979_, lean_object* v_ry_2980_){
_start:
{
lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2987_; lean_object* v___y_2988_; 
if (lean_obj_tag(v_rx_2979_) == 0)
{
if (lean_obj_tag(v_ry_2980_) == 0)
{
lean_object* v_a_2990_; lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3008_; 
lean_dec(v___x_2978_);
v_a_2990_ = lean_ctor_get(v_rx_2979_, 0);
v_a_2991_ = lean_ctor_get(v_rx_2979_, 1);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_rx_2979_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2993_ = v_rx_2979_;
v_isShared_2994_ = v_isSharedCheck_3008_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_inc(v_a_2990_);
lean_dec(v_rx_2979_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3008_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v_a_2995_; lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3007_; 
v_a_2995_ = lean_ctor_get(v_ry_2980_, 0);
v_a_2996_ = lean_ctor_get(v_ry_2980_, 1);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_ry_2980_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2998_ = v_ry_2980_;
v_isShared_2999_ = v_isSharedCheck_3007_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_inc(v_a_2995_);
lean_dec(v_ry_2980_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3007_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set_tag(v___x_2993_, 1);
lean_ctor_set(v___x_2993_, 1, v_a_2995_);
v___x_3001_ = v___x_2993_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_2990_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_a_2995_);
v___x_3001_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3004_; 
v___x_3002_ = l_Lake_JobState_merge(v_a_2991_, v_a_2996_);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 1, v___x_3002_);
lean_ctor_set(v___x_2998_, 0, v___x_3001_);
v___x_3004_ = v___x_2998_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3005_, 1, v___x_3002_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
}
else
{
lean_object* v_a_3009_; 
v_a_3009_ = lean_ctor_get(v_rx_2979_, 1);
lean_inc(v_a_3009_);
lean_dec_ref_known(v_rx_2979_, 2);
v___y_2987_ = v_ry_2980_;
v___y_2988_ = v_a_3009_;
goto v___jp_2986_;
}
}
else
{
lean_object* v_a_3010_; 
v_a_3010_ = lean_ctor_get(v_rx_2979_, 1);
lean_inc(v_a_3010_);
lean_dec_ref(v_rx_2979_);
v___y_2987_ = v_ry_2980_;
v___y_2988_ = v_a_3010_;
goto v___jp_2986_;
}
v___jp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = l_Lake_JobState_merge(v___y_2982_, v___y_2983_);
v___x_2985_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2978_);
lean_ctor_set(v___x_2985_, 1, v___x_2984_);
return v___x_2985_;
}
v___jp_2986_:
{
lean_object* v_a_2989_; 
v_a_2989_ = lean_ctor_get(v___y_2987_, 1);
lean_inc(v_a_2989_);
lean_dec_ref(v___y_2987_);
v___y_2982_ = v___y_2988_;
v___y_2983_ = v_a_2989_;
goto v___jp_2981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object* v_b_3011_, lean_object* v___x_3012_, uint8_t v___x_3013_, lean_object* v_rx_3014_){
_start:
{
lean_object* v_task_3015_; lean_object* v___f_3016_; lean_object* v___x_3017_; 
v_task_3015_ = lean_ctor_get(v_b_3011_, 0);
lean_inc_ref(v_task_3015_);
lean_dec_ref(v_b_3011_);
lean_inc(v___x_3012_);
v___f_3016_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3016_, 0, v___x_3012_);
lean_closure_set(v___f_3016_, 1, v_rx_3014_);
v___x_3017_ = lean_task_map(v___f_3016_, v_task_3015_, v___x_3012_, v___x_3013_);
return v___x_3017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_b_3018_, lean_object* v___x_3019_, lean_object* v___x_3020_, lean_object* v_rx_3021_){
_start:
{
uint8_t v___x_480__boxed_3022_; lean_object* v_res_3023_; 
v___x_480__boxed_3022_ = lean_unbox(v___x_3020_);
v_res_3023_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_3018_, v___x_3019_, v___x_480__boxed_3022_, v_rx_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(lean_object* v_as_3024_, size_t v_i_3025_, size_t v_stop_3026_, lean_object* v_b_3027_){
_start:
{
uint8_t v___x_3028_; 
v___x_3028_ = lean_usize_dec_eq(v_i_3025_, v_stop_3026_);
if (v___x_3028_ == 0)
{
size_t v___x_3029_; size_t v___x_3030_; lean_object* v___x_3031_; lean_object* v_task_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3047_; 
v___x_3029_ = ((size_t)1ULL);
v___x_3030_ = lean_usize_sub(v_i_3025_, v___x_3029_);
v___x_3031_ = lean_array_uget(v_as_3024_, v___x_3030_);
v_task_3032_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; lean_object* v_unused_3049_; 
v_unused_3048_ = lean_ctor_get(v___x_3031_, 2);
lean_dec(v_unused_3048_);
v_unused_3049_ = lean_ctor_get(v___x_3031_, 1);
lean_dec(v_unused_3049_);
v___x_3034_ = v___x_3031_;
v_isShared_3035_ = v_isSharedCheck_3047_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_task_3032_);
lean_dec(v___x_3031_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3047_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v___f_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3044_; 
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_unsigned_to_nat(0u);
v___x_3038_ = 1;
v___x_3039_ = lean_box(v___x_3038_);
v___f_3040_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3040_, 0, v_b_3027_);
lean_closure_set(v___f_3040_, 1, v___x_3037_);
lean_closure_set(v___f_3040_, 2, v___x_3039_);
v___x_3041_ = lean_task_bind(v_task_3032_, v___f_3040_, v___x_3037_, v___x_3038_);
v___x_3042_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_3035_ == 0)
{
lean_ctor_set(v___x_3034_, 2, v___x_3042_);
lean_ctor_set(v___x_3034_, 1, v___x_3036_);
lean_ctor_set(v___x_3034_, 0, v___x_3041_);
v___x_3044_ = v___x_3034_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3046_, 1, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3046_, 2, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_ctor_set_uint8(v___x_3044_, sizeof(void*)*3, v___x_3028_);
v_i_3025_ = v___x_3030_;
v_b_3027_ = v___x_3044_;
goto _start;
}
}
}
else
{
return v_b_3027_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object* v_as_3050_, lean_object* v_i_3051_, lean_object* v_stop_3052_, lean_object* v_b_3053_){
_start:
{
size_t v_i_boxed_3054_; size_t v_stop_boxed_3055_; lean_object* v_res_3056_; 
v_i_boxed_3054_ = lean_unbox_usize(v_i_3051_);
lean_dec(v_i_3051_);
v_stop_boxed_3055_ = lean_unbox_usize(v_stop_3052_);
lean_dec(v_stop_3052_);
v_res_3056_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_3050_, v_i_boxed_3054_, v_stop_boxed_3055_, v_b_3053_);
lean_dec_ref(v_as_3050_);
return v_res_3056_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(lean_object* v_init_3057_, lean_object* v_l_3058_){
_start:
{
lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3059_ = lean_array_mk(v_l_3058_);
v___x_3060_ = lean_array_get_size(v___x_3059_);
v___x_3061_ = lean_unsigned_to_nat(0u);
v___x_3062_ = lean_nat_dec_lt(v___x_3061_, v___x_3060_);
if (v___x_3062_ == 0)
{
lean_dec_ref(v___x_3059_);
return v_init_3057_;
}
else
{
size_t v___x_3063_; size_t v___x_3064_; lean_object* v___x_3065_; 
v___x_3063_ = lean_usize_of_nat(v___x_3060_);
v___x_3064_ = ((size_t)0ULL);
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v___x_3059_, v___x_3063_, v___x_3064_, v_init_3057_);
lean_dec_ref(v___x_3059_);
return v___x_3065_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object* v_jobs_3066_, lean_object* v_traceCaption_3067_){
_start:
{
lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; uint8_t v___x_3072_; uint8_t v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_box(0);
v___x_3070_ = lean_unsigned_to_nat(0u);
v___x_3071_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3072_ = 0;
v___x_3073_ = 0;
v___x_3074_ = l_Lake_BuildTrace_nil(v_traceCaption_3067_);
v___x_3075_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3075_, 0, v___x_3071_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
lean_ctor_set(v___x_3075_, 2, v___x_3070_);
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*3, v___x_3072_);
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*3 + 1, v___x_3073_);
lean_ctor_set_uint8(v___x_3075_, sizeof(void*)*3 + 2, v___x_3073_);
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3068_);
lean_ctor_set(v___x_3076_, 1, v___x_3075_);
v___x_3077_ = lean_task_pure(v___x_3076_);
v___x_3078_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3079_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3079_, 0, v___x_3077_);
lean_ctor_set(v___x_3079_, 1, v___x_3069_);
lean_ctor_set(v___x_3079_, 2, v___x_3078_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*3, v___x_3073_);
v___x_3080_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v___x_3079_, v_jobs_3066_);
return v___x_3080_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object* v_00_u03b1_3081_, lean_object* v_jobs_3082_, lean_object* v_traceCaption_3083_){
_start:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lake_Job_collectList___redArg(v_jobs_3082_, v_traceCaption_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0(lean_object* v_00_u03b1_3085_, lean_object* v_init_3086_, lean_object* v_l_3087_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v_init_3086_, v_l_3087_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_object* v_00_u03b1_3089_, lean_object* v_as_3090_, size_t v_i_3091_, size_t v_stop_3092_, lean_object* v_b_3093_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_3090_, v_i_3091_, v_stop_3092_, v_b_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3095_, lean_object* v_as_3096_, lean_object* v_i_3097_, lean_object* v_stop_3098_, lean_object* v_b_3099_){
_start:
{
size_t v_i_boxed_3100_; size_t v_stop_boxed_3101_; lean_object* v_res_3102_; 
v_i_boxed_3100_ = lean_unbox_usize(v_i_3097_);
lean_dec(v_i_3097_);
v_stop_boxed_3101_ = lean_unbox_usize(v_stop_3098_);
lean_dec(v_stop_3098_);
v_res_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(v_00_u03b1_3095_, v_as_3096_, v_i_boxed_3100_, v_stop_boxed_3101_, v_b_3099_);
lean_dec_ref(v_as_3096_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object* v___x_3103_, lean_object* v_rx_3104_, lean_object* v_ry_3105_){
_start:
{
lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3112_; lean_object* v___y_3113_; 
if (lean_obj_tag(v_rx_3104_) == 0)
{
if (lean_obj_tag(v_ry_3105_) == 0)
{
lean_object* v_a_3115_; lean_object* v_a_3116_; lean_object* v_a_3117_; lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3127_; 
lean_dec(v___x_3103_);
v_a_3115_ = lean_ctor_get(v_rx_3104_, 0);
lean_inc(v_a_3115_);
v_a_3116_ = lean_ctor_get(v_rx_3104_, 1);
lean_inc(v_a_3116_);
lean_dec_ref_known(v_rx_3104_, 2);
v_a_3117_ = lean_ctor_get(v_ry_3105_, 0);
v_a_3118_ = lean_ctor_get(v_ry_3105_, 1);
v_isSharedCheck_3127_ = !lean_is_exclusive(v_ry_3105_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3120_ = v_ry_3105_;
v_isShared_3121_ = v_isSharedCheck_3127_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_inc(v_a_3117_);
lean_dec(v_ry_3105_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3127_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; lean_object* v___x_3125_; 
v___x_3122_ = lean_array_push(v_a_3115_, v_a_3117_);
v___x_3123_ = l_Lake_JobState_merge(v_a_3116_, v_a_3118_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 1, v___x_3123_);
lean_ctor_set(v___x_3120_, 0, v___x_3122_);
v___x_3125_ = v___x_3120_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v___x_3122_);
lean_ctor_set(v_reuseFailAlloc_3126_, 1, v___x_3123_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
else
{
lean_object* v_a_3128_; 
v_a_3128_ = lean_ctor_get(v_rx_3104_, 1);
lean_inc(v_a_3128_);
lean_dec_ref_known(v_rx_3104_, 2);
v___y_3112_ = v_ry_3105_;
v___y_3113_ = v_a_3128_;
goto v___jp_3111_;
}
}
else
{
lean_object* v_a_3129_; 
v_a_3129_ = lean_ctor_get(v_rx_3104_, 1);
lean_inc(v_a_3129_);
lean_dec_ref(v_rx_3104_);
v___y_3112_ = v_ry_3105_;
v___y_3113_ = v_a_3129_;
goto v___jp_3111_;
}
v___jp_3106_:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = l_Lake_JobState_merge(v___y_3107_, v___y_3108_);
v___x_3110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3103_);
lean_ctor_set(v___x_3110_, 1, v___x_3109_);
return v___x_3110_;
}
v___jp_3111_:
{
lean_object* v_a_3114_; 
v_a_3114_ = lean_ctor_get(v___y_3112_, 1);
lean_inc(v_a_3114_);
lean_dec_ref(v___y_3112_);
v___y_3107_ = v___y_3113_;
v___y_3108_ = v_a_3114_;
goto v___jp_3106_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object* v___x_3130_, lean_object* v___x_3131_, uint8_t v___x_3132_, lean_object* v_rx_3133_){
_start:
{
lean_object* v_task_3134_; lean_object* v___f_3135_; lean_object* v___x_3136_; 
v_task_3134_ = lean_ctor_get(v___x_3130_, 0);
lean_inc_ref(v_task_3134_);
lean_dec_ref(v___x_3130_);
lean_inc(v___x_3131_);
v___f_3135_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3135_, 0, v___x_3131_);
lean_closure_set(v___f_3135_, 1, v_rx_3133_);
v___x_3136_ = lean_task_map(v___f_3135_, v_task_3134_, v___x_3131_, v___x_3132_);
return v___x_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object* v___x_3137_, lean_object* v___x_3138_, lean_object* v___x_3139_, lean_object* v_rx_3140_){
_start:
{
uint8_t v___x_414__boxed_3141_; lean_object* v_res_3142_; 
v___x_414__boxed_3141_ = lean_unbox(v___x_3139_);
v_res_3142_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_3137_, v___x_3138_, v___x_414__boxed_3141_, v_rx_3140_);
return v_res_3142_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(lean_object* v_as_3143_, size_t v_i_3144_, size_t v_stop_3145_, lean_object* v_b_3146_){
_start:
{
uint8_t v___x_3147_; 
v___x_3147_ = lean_usize_dec_eq(v_i_3144_, v_stop_3145_);
if (v___x_3147_ == 0)
{
lean_object* v_task_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3166_; 
v_task_3148_ = lean_ctor_get(v_b_3146_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_b_3146_);
if (v_isSharedCheck_3166_ == 0)
{
lean_object* v_unused_3167_; lean_object* v_unused_3168_; 
v_unused_3167_ = lean_ctor_get(v_b_3146_, 2);
lean_dec(v_unused_3167_);
v_unused_3168_ = lean_ctor_get(v_b_3146_, 1);
lean_dec(v_unused_3168_);
v___x_3150_ = v_b_3146_;
v_isShared_3151_ = v_isSharedCheck_3166_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_task_3148_);
lean_dec(v_b_3146_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3166_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; lean_object* v___x_3156_; lean_object* v___f_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3152_ = lean_box(0);
v___x_3153_ = lean_array_uget_borrowed(v_as_3143_, v_i_3144_);
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = 1;
v___x_3156_ = lean_box(v___x_3155_);
lean_inc(v___x_3153_);
v___f_3157_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3157_, 0, v___x_3153_);
lean_closure_set(v___f_3157_, 1, v___x_3154_);
lean_closure_set(v___f_3157_, 2, v___x_3156_);
v___x_3158_ = lean_task_bind(v_task_3148_, v___f_3157_, v___x_3154_, v___x_3155_);
v___x_3159_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_3151_ == 0)
{
lean_ctor_set(v___x_3150_, 2, v___x_3159_);
lean_ctor_set(v___x_3150_, 1, v___x_3152_);
lean_ctor_set(v___x_3150_, 0, v___x_3158_);
v___x_3161_ = v___x_3150_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3165_, 1, v___x_3152_);
lean_ctor_set(v_reuseFailAlloc_3165_, 2, v___x_3159_);
v___x_3161_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
size_t v___x_3162_; size_t v___x_3163_; 
lean_ctor_set_uint8(v___x_3161_, sizeof(void*)*3, v___x_3147_);
v___x_3162_ = ((size_t)1ULL);
v___x_3163_ = lean_usize_add(v_i_3144_, v___x_3162_);
v_i_3144_ = v___x_3163_;
v_b_3146_ = v___x_3161_;
goto _start;
}
}
}
else
{
return v_b_3146_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(lean_object* v_as_3169_, lean_object* v_i_3170_, lean_object* v_stop_3171_, lean_object* v_b_3172_){
_start:
{
size_t v_i_boxed_3173_; size_t v_stop_boxed_3174_; lean_object* v_res_3175_; 
v_i_boxed_3173_ = lean_unbox_usize(v_i_3170_);
lean_dec(v_i_3170_);
v_stop_boxed_3174_ = lean_unbox_usize(v_stop_3171_);
lean_dec(v_stop_3171_);
v_res_3175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3169_, v_i_boxed_3173_, v_stop_boxed_3174_, v_b_3172_);
lean_dec_ref(v_as_3169_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object* v_jobs_3176_, lean_object* v_traceCaption_3177_){
_start:
{
lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; uint8_t v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3178_ = lean_array_get_size(v_jobs_3176_);
v___x_3179_ = lean_mk_empty_array_with_capacity(v___x_3178_);
v___x_3180_ = lean_box(0);
v___x_3181_ = lean_unsigned_to_nat(0u);
v___x_3182_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3183_ = 0;
v___x_3184_ = 0;
v___x_3185_ = l_Lake_BuildTrace_nil(v_traceCaption_3177_);
v___x_3186_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3186_, 0, v___x_3182_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
lean_ctor_set(v___x_3186_, 2, v___x_3181_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*3, v___x_3183_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*3 + 1, v___x_3184_);
lean_ctor_set_uint8(v___x_3186_, sizeof(void*)*3 + 2, v___x_3184_);
v___x_3187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3179_);
lean_ctor_set(v___x_3187_, 1, v___x_3186_);
v___x_3188_ = lean_task_pure(v___x_3187_);
v___x_3189_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3190_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3190_, 0, v___x_3188_);
lean_ctor_set(v___x_3190_, 1, v___x_3180_);
lean_ctor_set(v___x_3190_, 2, v___x_3189_);
lean_ctor_set_uint8(v___x_3190_, sizeof(void*)*3, v___x_3184_);
v___x_3191_ = lean_nat_dec_lt(v___x_3181_, v___x_3178_);
if (v___x_3191_ == 0)
{
return v___x_3190_;
}
else
{
uint8_t v___x_3192_; 
v___x_3192_ = lean_nat_dec_le(v___x_3178_, v___x_3178_);
if (v___x_3192_ == 0)
{
if (v___x_3191_ == 0)
{
return v___x_3190_;
}
else
{
size_t v___x_3193_; size_t v___x_3194_; lean_object* v___x_3195_; 
v___x_3193_ = ((size_t)0ULL);
v___x_3194_ = lean_usize_of_nat(v___x_3178_);
v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_3176_, v___x_3193_, v___x_3194_, v___x_3190_);
return v___x_3195_;
}
}
else
{
size_t v___x_3196_; size_t v___x_3197_; lean_object* v___x_3198_; 
v___x_3196_ = ((size_t)0ULL);
v___x_3197_ = lean_usize_of_nat(v___x_3178_);
v___x_3198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_3176_, v___x_3196_, v___x_3197_, v___x_3190_);
return v___x_3198_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object* v_jobs_3199_, lean_object* v_traceCaption_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Lake_Job_collectArray___redArg(v_jobs_3199_, v_traceCaption_3200_);
lean_dec_ref(v_jobs_3199_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object* v_00_u03b1_3202_, lean_object* v_jobs_3203_, lean_object* v_traceCaption_3204_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lake_Job_collectArray___redArg(v_jobs_3203_, v_traceCaption_3204_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object* v_00_u03b1_3206_, lean_object* v_jobs_3207_, lean_object* v_traceCaption_3208_){
_start:
{
lean_object* v_res_3209_; 
v_res_3209_ = l_Lake_Job_collectArray(v_00_u03b1_3206_, v_jobs_3207_, v_traceCaption_3208_);
lean_dec_ref(v_jobs_3207_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_object* v_00_u03b1_3210_, lean_object* v_as_3211_, size_t v_i_3212_, size_t v_stop_3213_, lean_object* v_b_3214_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3211_, v_i_3212_, v_stop_3213_, v_b_3214_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(lean_object* v_00_u03b1_3216_, lean_object* v_as_3217_, lean_object* v_i_3218_, lean_object* v_stop_3219_, lean_object* v_b_3220_){
_start:
{
size_t v_i_boxed_3221_; size_t v_stop_boxed_3222_; lean_object* v_res_3223_; 
v_i_boxed_3221_ = lean_unbox_usize(v_i_3218_);
lean_dec(v_i_3218_);
v_stop_boxed_3222_ = lean_unbox_usize(v_stop_3219_);
lean_dec(v_stop_3219_);
v_res_3223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(v_00_u03b1_3216_, v_as_3217_, v_i_boxed_3221_, v_stop_boxed_3222_, v_b_3220_);
lean_dec_ref(v_as_3217_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg(){
_start:
{
lean_object* v___x_3225_; 
v___x_3225_ = lean_box(0);
return v___x_3225_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg___boxed(lean_object* v___dummy_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg();
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(lean_object* v_00_u03b1_3228_, lean_object* v_inst_3229_){
_start:
{
lean_object* v___x_3230_; 
v___x_3230_ = lean_box(0);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0(lean_object* v___x_3231_, lean_object* v_rx_3232_, lean_object* v_i_3233_, lean_object* v_ry_3234_){
_start:
{
lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3241_; lean_object* v___y_3242_; 
if (lean_obj_tag(v_rx_3232_) == 0)
{
if (lean_obj_tag(v_ry_3234_) == 0)
{
lean_object* v_a_3244_; lean_object* v_a_3245_; lean_object* v_a_3246_; lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3256_; 
lean_dec(v___x_3231_);
v_a_3244_ = lean_ctor_get(v_rx_3232_, 0);
lean_inc(v_a_3244_);
v_a_3245_ = lean_ctor_get(v_rx_3232_, 1);
lean_inc(v_a_3245_);
lean_dec_ref_known(v_rx_3232_, 2);
v_a_3246_ = lean_ctor_get(v_ry_3234_, 0);
v_a_3247_ = lean_ctor_get(v_ry_3234_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_ry_3234_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3249_ = v_ry_3234_;
v_isShared_3250_ = v_isSharedCheck_3256_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_inc(v_a_3246_);
lean_dec(v_ry_3234_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3256_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3251_ = lean_array_fset(v_a_3244_, v_i_3233_, v_a_3246_);
v___x_3252_ = l_Lake_JobState_merge(v_a_3245_, v_a_3247_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v___x_3252_);
lean_ctor_set(v___x_3249_, 0, v___x_3251_);
v___x_3254_ = v___x_3249_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
else
{
lean_object* v_a_3257_; 
v_a_3257_ = lean_ctor_get(v_rx_3232_, 1);
lean_inc(v_a_3257_);
lean_dec_ref_known(v_rx_3232_, 2);
v___y_3241_ = v_ry_3234_;
v___y_3242_ = v_a_3257_;
goto v___jp_3240_;
}
}
else
{
lean_object* v_a_3258_; 
v_a_3258_ = lean_ctor_get(v_rx_3232_, 1);
lean_inc(v_a_3258_);
lean_dec_ref(v_rx_3232_);
v___y_3241_ = v_ry_3234_;
v___y_3242_ = v_a_3258_;
goto v___jp_3240_;
}
v___jp_3235_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = l_Lake_JobState_merge(v___y_3236_, v___y_3237_);
v___x_3239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3231_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
return v___x_3239_;
}
v___jp_3240_:
{
lean_object* v_a_3243_; 
v_a_3243_ = lean_ctor_get(v___y_3241_, 1);
lean_inc(v_a_3243_);
lean_dec_ref(v___y_3241_);
v___y_3236_ = v___y_3242_;
v___y_3237_ = v_a_3243_;
goto v___jp_3235_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0___boxed(lean_object* v___x_3259_, lean_object* v_rx_3260_, lean_object* v_i_3261_, lean_object* v_ry_3262_){
_start:
{
lean_object* v_res_3263_; 
v_res_3263_ = l_Lake_Job_collectVector___redArg___lam__0(v___x_3259_, v_rx_3260_, v_i_3261_, v_ry_3262_);
lean_dec(v_i_3261_);
return v_res_3263_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1(lean_object* v___x_3264_, lean_object* v___x_3265_, lean_object* v_i_3266_, uint8_t v___x_3267_, lean_object* v_rx_3268_){
_start:
{
lean_object* v_task_3269_; lean_object* v___f_3270_; lean_object* v___x_3271_; 
v_task_3269_ = lean_ctor_get(v___x_3264_, 0);
lean_inc_ref(v_task_3269_);
lean_dec_ref(v___x_3264_);
lean_inc(v___x_3265_);
v___f_3270_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3270_, 0, v___x_3265_);
lean_closure_set(v___f_3270_, 1, v_rx_3268_);
lean_closure_set(v___f_3270_, 2, v_i_3266_);
v___x_3271_ = lean_task_map(v___f_3270_, v_task_3269_, v___x_3265_, v___x_3267_);
return v___x_3271_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1___boxed(lean_object* v___x_3272_, lean_object* v___x_3273_, lean_object* v_i_3274_, lean_object* v___x_3275_, lean_object* v_rx_3276_){
_start:
{
uint8_t v___x_191__boxed_3277_; lean_object* v_res_3278_; 
v___x_191__boxed_3277_ = lean_unbox(v___x_3275_);
v_res_3278_ = l_Lake_Job_collectVector___redArg___lam__1(v___x_3272_, v___x_3273_, v_i_3274_, v___x_191__boxed_3277_, v_rx_3276_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2(lean_object* v_jobs_3279_, lean_object* v___x_3280_, lean_object* v_i_3281_, lean_object* v_h_3282_, lean_object* v_job_3283_){
_start:
{
lean_object* v_task_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3299_; 
v_task_3284_ = lean_ctor_get(v_job_3283_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v_job_3283_);
if (v_isSharedCheck_3299_ == 0)
{
lean_object* v_unused_3300_; lean_object* v_unused_3301_; 
v_unused_3300_ = lean_ctor_get(v_job_3283_, 2);
lean_dec(v_unused_3300_);
v_unused_3301_ = lean_ctor_get(v_job_3283_, 1);
lean_dec(v_unused_3301_);
v___x_3286_ = v_job_3283_;
v_isShared_3287_ = v_isSharedCheck_3299_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_task_3284_);
lean_dec(v_job_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3299_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; uint8_t v___x_3290_; lean_object* v___x_3291_; lean_object* v___f_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3297_; 
v___x_3288_ = lean_array_fget_borrowed(v_jobs_3279_, v_i_3281_);
v___x_3289_ = lean_unsigned_to_nat(0u);
v___x_3290_ = 1;
v___x_3291_ = lean_box(v___x_3290_);
lean_inc(v___x_3288_);
v___f_3292_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3292_, 0, v___x_3288_);
lean_closure_set(v___f_3292_, 1, v___x_3289_);
lean_closure_set(v___f_3292_, 2, v_i_3281_);
lean_closure_set(v___f_3292_, 3, v___x_3291_);
v___x_3293_ = lean_task_bind(v_task_3284_, v___f_3292_, v___x_3289_, v___x_3290_);
v___x_3294_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3295_ = 0;
if (v_isShared_3287_ == 0)
{
lean_ctor_set(v___x_3286_, 2, v___x_3294_);
lean_ctor_set(v___x_3286_, 1, v___x_3280_);
lean_ctor_set(v___x_3286_, 0, v___x_3293_);
v___x_3297_ = v___x_3286_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3293_);
lean_ctor_set(v_reuseFailAlloc_3298_, 1, v___x_3280_);
lean_ctor_set(v_reuseFailAlloc_3298_, 2, v___x_3294_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_ctor_set_uint8(v___x_3297_, sizeof(void*)*3, v___x_3295_);
return v___x_3297_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2___boxed(lean_object* v_jobs_3302_, lean_object* v___x_3303_, lean_object* v_i_3304_, lean_object* v_h_3305_, lean_object* v_job_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lake_Job_collectVector___redArg___lam__2(v_jobs_3302_, v___x_3303_, v_i_3304_, v_h_3305_, v_job_3306_);
lean_dec_ref(v_jobs_3302_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg(lean_object* v_n_3308_, lean_object* v_jobs_3309_, lean_object* v_traceCaption_3310_){
_start:
{
lean_object* v_placeholder_3311_; lean_object* v___x_3312_; lean_object* v___f_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; uint8_t v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_placeholder_3311_ = lean_box(0);
v___x_3312_ = lean_box(0);
v___f_3313_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3313_, 0, v_jobs_3309_);
lean_closure_set(v___f_3313_, 1, v___x_3312_);
lean_inc_n(v_n_3308_, 2);
v___x_3314_ = lean_mk_array(v_n_3308_, v_placeholder_3311_);
v___x_3315_ = lean_unsigned_to_nat(0u);
v___x_3316_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3317_ = 0;
v___x_3318_ = 0;
v___x_3319_ = l_Lake_BuildTrace_nil(v_traceCaption_3310_);
v___x_3320_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3320_, 0, v___x_3316_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
lean_ctor_set(v___x_3320_, 2, v___x_3315_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*3, v___x_3317_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*3 + 1, v___x_3318_);
lean_ctor_set_uint8(v___x_3320_, sizeof(void*)*3 + 2, v___x_3318_);
v___x_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3314_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = lean_task_pure(v___x_3321_);
v___x_3323_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3324_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3312_);
lean_ctor_set(v___x_3324_, 2, v___x_3323_);
lean_ctor_set_uint8(v___x_3324_, sizeof(void*)*3, v___x_3318_);
v___x_3325_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3308_, v___f_3313_, v_n_3308_, lean_box(0), v___x_3324_);
lean_dec(v_n_3308_);
return v___x_3325_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector(lean_object* v_n_3326_, lean_object* v_00_u03b1_3327_, lean_object* v_inst_3328_, lean_object* v_jobs_3329_, lean_object* v_traceCaption_3330_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lake_Job_collectVector___redArg(v_n_3326_, v_jobs_3329_, v_traceCaption_3330_);
return v___x_3331_;
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
