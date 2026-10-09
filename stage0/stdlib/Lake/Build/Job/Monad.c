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
lean_object* l_Lake_JobM_ofFn___redArg(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v_a_3_, lean_object* v_a_4_, lean_object* v_a_5_, lean_object* v_a_6_, lean_object* v_a_7_){
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
LEAN_EXPORT void l_Lake_JobM_ofFn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1_ = stack[0].m_obj;
lean_object* v_a_2_ = stack[1].m_obj;
lean_object* v_a_3_ = stack[2].m_obj;
lean_object* v_a_4_ = stack[3].m_obj;
lean_object* v_a_5_ = stack[4].m_obj;
lean_object* v_a_6_ = stack[5].m_obj;
lean_object* v_a_7_ = stack[6].m_obj;
lean_object* v_res_10_;
v_res_10_ = l_Lake_JobM_ofFn___redArg(v_f_1_, v_a_2_, v_a_3_, v_a_4_, v_a_5_, v_a_6_, v_a_7_);
stack->m_obj
 = v_res_10_;
}
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___redArg___boxed(lean_object* v_f_11_, lean_object* v_a_12_, lean_object* v_a_13_, lean_object* v_a_14_, lean_object* v_a_15_, lean_object* v_a_16_, lean_object* v_a_17_, lean_object* v_a_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_Lake_JobM_ofFn___redArg(v_f_11_, v_a_12_, v_a_13_, v_a_14_, v_a_15_, v_a_16_, v_a_17_);
lean_dec_ref(v_a_16_);
lean_dec(v_a_15_);
lean_dec(v_a_14_);
lean_dec(v_a_13_);
return v_res_19_;
}
}
lean_object* l_Lake_JobM_ofFn(lean_object* v_00_u03b1_20_, lean_object* v_f_21_, lean_object* v_a_22_, lean_object* v_a_23_, lean_object* v_a_24_, lean_object* v_a_25_, lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v___x_29_; 
lean_inc_ref(v_a_26_);
lean_inc(v_a_25_);
lean_inc(v_a_24_);
lean_inc(v_a_23_);
v___x_29_ = lean_apply_7(v_f_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_, lean_box(0));
return v___x_29_;
}
}
LEAN_EXPORT void l_Lake_JobM_ofFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_21_ = stack[1].m_obj;
lean_object* v_a_22_ = stack[2].m_obj;
lean_object* v_a_23_ = stack[3].m_obj;
lean_object* v_a_24_ = stack[4].m_obj;
lean_object* v_a_25_ = stack[5].m_obj;
lean_object* v_a_26_ = stack[6].m_obj;
lean_object* v_a_27_ = stack[7].m_obj;
lean_object* v_res_30_;
v_res_30_ = l_Lake_JobM_ofFn(lean_box(0), v_f_21_, v_a_22_, v_a_23_, v_a_24_, v_a_25_, v_a_26_, v_a_27_);
stack->m_obj
 = v_res_30_;
}
LEAN_EXPORT lean_object* l_Lake_JobM_ofFn___boxed(lean_object* v_00_u03b1_31_, lean_object* v_f_32_, lean_object* v_a_33_, lean_object* v_a_34_, lean_object* v_a_35_, lean_object* v_a_36_, lean_object* v_a_37_, lean_object* v_a_38_, lean_object* v_a_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lake_JobM_ofFn(v_00_u03b1_31_, v_f_32_, v_a_33_, v_a_34_, v_a_35_, v_a_36_, v_a_37_, v_a_38_);
lean_dec_ref(v_a_37_);
lean_dec(v_a_36_);
lean_dec(v_a_35_);
lean_dec(v_a_34_);
return v_res_40_;
}
}
lean_object* l_Lake_JobM_toFn___redArg(lean_object* v_self_41_, lean_object* v_fetch_42_, lean_object* v_pkg_x3f_43_, lean_object* v_stack_44_, lean_object* v_store_45_, lean_object* v_ctx_46_, lean_object* v_s_47_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_apply_7(v_self_41_, v_fetch_42_, v_pkg_x3f_43_, v_stack_44_, v_store_45_, v_ctx_46_, v_s_47_, lean_box(0));
return v___x_49_;
}
}
LEAN_EXPORT void l_Lake_JobM_toFn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_41_ = stack[0].m_obj;
lean_object* v_fetch_42_ = stack[1].m_obj;
lean_object* v_pkg_x3f_43_ = stack[2].m_obj;
lean_object* v_stack_44_ = stack[3].m_obj;
lean_object* v_store_45_ = stack[4].m_obj;
lean_object* v_ctx_46_ = stack[5].m_obj;
lean_object* v_s_47_ = stack[6].m_obj;
lean_object* v_res_50_;
v_res_50_ = l_Lake_JobM_toFn___redArg(v_self_41_, v_fetch_42_, v_pkg_x3f_43_, v_stack_44_, v_store_45_, v_ctx_46_, v_s_47_);
stack->m_obj
 = v_res_50_;
}
LEAN_EXPORT lean_object* l_Lake_JobM_toFn___redArg___boxed(lean_object* v_self_51_, lean_object* v_fetch_52_, lean_object* v_pkg_x3f_53_, lean_object* v_stack_54_, lean_object* v_store_55_, lean_object* v_ctx_56_, lean_object* v_s_57_, lean_object* v_a_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lake_JobM_toFn___redArg(v_self_51_, v_fetch_52_, v_pkg_x3f_53_, v_stack_54_, v_store_55_, v_ctx_56_, v_s_57_);
return v_res_59_;
}
}
lean_object* l_Lake_JobM_toFn(lean_object* v_00_u03b1_60_, lean_object* v_self_61_, lean_object* v_fetch_62_, lean_object* v_pkg_x3f_63_, lean_object* v_stack_64_, lean_object* v_store_65_, lean_object* v_ctx_66_, lean_object* v_s_67_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_apply_7(v_self_61_, v_fetch_62_, v_pkg_x3f_63_, v_stack_64_, v_store_65_, v_ctx_66_, v_s_67_, lean_box(0));
return v___x_69_;
}
}
LEAN_EXPORT void l_Lake_JobM_toFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_61_ = stack[1].m_obj;
lean_object* v_fetch_62_ = stack[2].m_obj;
lean_object* v_pkg_x3f_63_ = stack[3].m_obj;
lean_object* v_stack_64_ = stack[4].m_obj;
lean_object* v_store_65_ = stack[5].m_obj;
lean_object* v_ctx_66_ = stack[6].m_obj;
lean_object* v_s_67_ = stack[7].m_obj;
lean_object* v_res_70_;
v_res_70_ = l_Lake_JobM_toFn(lean_box(0), v_self_61_, v_fetch_62_, v_pkg_x3f_63_, v_stack_64_, v_store_65_, v_ctx_66_, v_s_67_);
stack->m_obj
 = v_res_70_;
}
LEAN_EXPORT lean_object* l_Lake_JobM_toFn___boxed(lean_object* v_00_u03b1_71_, lean_object* v_self_72_, lean_object* v_fetch_73_, lean_object* v_pkg_x3f_74_, lean_object* v_stack_75_, lean_object* v_store_76_, lean_object* v_ctx_77_, lean_object* v_s_78_, lean_object* v_a_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lake_JobM_toFn(v_00_u03b1_71_, v_self_72_, v_fetch_73_, v_pkg_x3f_74_, v_stack_75_, v_store_76_, v_ctx_77_, v_s_78_);
return v_res_80_;
}
}
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM___closed__1(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__0));
v___x_83_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v___x_82_);
return v___x_83_;
}
}
static lean_object* _init_l_Lake_instMonadStateOfJobStateJobM(void){
_start:
{
lean_object* v___x_87_; lean_object* v_get_88_; lean_object* v_set_89_; lean_object* v_modifyGet_90_; lean_object* v___x_91_; lean_object* v___f_92_; lean_object* v___x_93_; lean_object* v___f_94_; lean_object* v___f_95_; lean_object* v___x_96_; lean_object* v___f_97_; lean_object* v___f_98_; lean_object* v___x_99_; lean_object* v___f_100_; lean_object* v___f_101_; lean_object* v___x_102_; lean_object* v___f_103_; lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_87_ = lean_obj_once(&l_Lake_instMonadStateOfJobStateJobM___closed__1, &l_Lake_instMonadStateOfJobStateJobM___closed__1_once, _init_l_Lake_instMonadStateOfJobStateJobM___closed__1);
v_get_88_ = lean_ctor_get(v___x_87_, 0);
v_set_89_ = lean_ctor_get(v___x_87_, 1);
v_modifyGet_90_ = lean_ctor_get(v___x_87_, 2);
v___x_91_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__2));
v___f_92_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__3));
v___x_93_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__4));
lean_inc(v_set_89_);
v___f_94_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_94_, 0, v_set_89_);
lean_closure_set(v___f_94_, 1, v___f_92_);
lean_inc(v_modifyGet_90_);
v___f_95_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_95_, 0, v_modifyGet_90_);
lean_closure_set(v___f_95_, 1, v___f_92_);
lean_inc(v_get_88_);
v___x_96_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_96_, 0, lean_box(0));
lean_closure_set(v___x_96_, 1, v_get_88_);
v___f_97_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_97_, 0, v___f_94_);
lean_closure_set(v___f_97_, 1, v___x_93_);
v___f_98_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_98_, 0, v___f_95_);
lean_closure_set(v___f_98_, 1, v___x_93_);
v___x_99_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_99_, 0, lean_box(0));
lean_closure_set(v___x_99_, 1, lean_box(0));
lean_closure_set(v___x_99_, 2, lean_box(0));
lean_closure_set(v___x_99_, 3, lean_box(0));
lean_closure_set(v___x_99_, 4, v___x_96_);
v___f_100_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_100_, 0, v___f_97_);
lean_closure_set(v___f_100_, 1, v___f_92_);
v___f_101_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_101_, 0, v___f_98_);
lean_closure_set(v___f_101_, 1, v___f_92_);
v___x_102_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_102_, 0, lean_box(0));
lean_closure_set(v___x_102_, 1, v___x_99_);
v___f_103_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_103_, 0, v___f_100_);
lean_closure_set(v___f_103_, 1, v___f_92_);
v___f_104_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_104_, 0, v___f_101_);
lean_closure_set(v___f_104_, 1, v___f_92_);
v___x_105_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___x_105_, 0, lean_box(0));
lean_closure_set(v___x_105_, 1, v___x_102_);
v___f_106_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_106_, 0, v___f_103_);
lean_closure_set(v___f_106_, 1, v___x_91_);
v___f_107_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_107_, 0, v___f_104_);
lean_closure_set(v___f_107_, 1, v___x_91_);
v___x_108_ = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(v___x_108_, 0, lean_box(0));
lean_closure_set(v___x_108_, 1, lean_box(0));
lean_closure_set(v___x_108_, 2, lean_box(0));
lean_closure_set(v___x_108_, 3, v___x_105_);
v___x_109_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v___f_106_);
lean_ctor_set(v___x_109_, 2, v___f_107_);
return v___x_109_;
}
}
lean_object* l_Lake_instMonadStateOfLogJobM___lam__0(lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_){
_start:
{
lean_object* v_log_117_; lean_object* v___x_118_; 
v_log_117_ = lean_ctor_get(v___y_115_, 0);
lean_inc_ref(v_log_117_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_log_117_);
lean_ctor_set(v___x_118_, 1, v___y_115_);
return v___x_118_;
}
}
LEAN_EXPORT void l_Lake_instMonadStateOfLogJobM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_110_ = stack[0].m_obj;
lean_object* v___y_111_ = stack[1].m_obj;
lean_object* v___y_112_ = stack[2].m_obj;
lean_object* v___y_113_ = stack[3].m_obj;
lean_object* v___y_114_ = stack[4].m_obj;
lean_object* v___y_115_ = stack[5].m_obj;
lean_object* v_res_119_;
v_res_119_ = l_Lake_instMonadStateOfLogJobM___lam__0(v___y_110_, v___y_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
stack->m_obj
 = v_res_119_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0___boxed(lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lake_instMonadStateOfLogJobM___lam__0(v___y_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_);
lean_dec_ref(v___y_124_);
lean_dec(v___y_123_);
lean_dec(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_127_;
}
}
lean_object* l_Lake_instMonadStateOfLogJobM___lam__1(lean_object* v_log_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
uint8_t v_action_136_; uint8_t v_wantsRebuild_137_; uint8_t v_canceled_138_; lean_object* v_trace_139_; lean_object* v_buildTime_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
v_action_136_ = lean_ctor_get_uint8(v___y_134_, sizeof(void*)*3);
v_wantsRebuild_137_ = lean_ctor_get_uint8(v___y_134_, sizeof(void*)*3 + 1);
v_canceled_138_ = lean_ctor_get_uint8(v___y_134_, sizeof(void*)*3 + 2);
v_trace_139_ = lean_ctor_get(v___y_134_, 1);
v_buildTime_140_ = lean_ctor_get(v___y_134_, 2);
v_isSharedCheck_149_ = !lean_is_exclusive(v___y_134_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v___y_134_, 0);
lean_dec(v_unused_150_);
v___x_142_ = v___y_134_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_buildTime_140_);
lean_inc(v_trace_139_);
lean_dec(v___y_134_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_144_ = lean_box(0);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v_log_128_);
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_log_128_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_trace_139_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_buildTime_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_148_, sizeof(void*)*3, v_action_136_);
lean_ctor_set_uint8(v_reuseFailAlloc_148_, sizeof(void*)*3 + 1, v_wantsRebuild_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_148_, sizeof(void*)*3 + 2, v_canceled_138_);
v___x_146_ = v_reuseFailAlloc_148_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
lean_object* v___x_147_; 
v___x_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_144_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
return v___x_147_;
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadStateOfLogJobM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_log_128_ = stack[0].m_obj;
lean_object* v___y_129_ = stack[1].m_obj;
lean_object* v___y_130_ = stack[2].m_obj;
lean_object* v___y_131_ = stack[3].m_obj;
lean_object* v___y_132_ = stack[4].m_obj;
lean_object* v___y_133_ = stack[5].m_obj;
lean_object* v___y_134_ = stack[6].m_obj;
lean_object* v_res_151_;
v_res_151_ = l_Lake_instMonadStateOfLogJobM___lam__1(v_log_128_, v___y_129_, v___y_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
stack->m_obj
 = v_res_151_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1___boxed(lean_object* v_log_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_, lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l_Lake_instMonadStateOfLogJobM___lam__1(v_log_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_, v___y_158_);
lean_dec_ref(v___y_157_);
lean_dec(v___y_156_);
lean_dec(v___y_155_);
lean_dec(v___y_154_);
lean_dec_ref(v___y_153_);
return v_res_160_;
}
}
lean_object* l_Lake_instMonadStateOfLogJobM___lam__2(lean_object* v_00_u03b1_161_, lean_object* v_f_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
lean_object* v_log_170_; uint8_t v_action_171_; uint8_t v_wantsRebuild_172_; uint8_t v_canceled_173_; lean_object* v_trace_174_; lean_object* v_buildTime_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_192_; 
v_log_170_ = lean_ctor_get(v___y_168_, 0);
v_action_171_ = lean_ctor_get_uint8(v___y_168_, sizeof(void*)*3);
v_wantsRebuild_172_ = lean_ctor_get_uint8(v___y_168_, sizeof(void*)*3 + 1);
v_canceled_173_ = lean_ctor_get_uint8(v___y_168_, sizeof(void*)*3 + 2);
v_trace_174_ = lean_ctor_get(v___y_168_, 1);
v_buildTime_175_ = lean_ctor_get(v___y_168_, 2);
v_isSharedCheck_192_ = !lean_is_exclusive(v___y_168_);
if (v_isSharedCheck_192_ == 0)
{
v___x_177_ = v___y_168_;
v_isShared_178_ = v_isSharedCheck_192_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_buildTime_175_);
lean_inc(v_trace_174_);
lean_inc(v_log_170_);
lean_dec(v___y_168_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_192_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v_fst_180_; lean_object* v_snd_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_191_; 
v___x_179_ = lean_apply_1(v_f_162_, v_log_170_);
v_fst_180_ = lean_ctor_get(v___x_179_, 0);
v_snd_181_ = lean_ctor_get(v___x_179_, 1);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_191_ == 0)
{
v___x_183_ = v___x_179_;
v_isShared_184_ = v_isSharedCheck_191_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_snd_181_);
lean_inc(v_fst_180_);
lean_dec(v___x_179_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_191_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v_snd_181_);
v___x_186_ = v___x_177_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_snd_181_);
lean_ctor_set(v_reuseFailAlloc_190_, 1, v_trace_174_);
lean_ctor_set(v_reuseFailAlloc_190_, 2, v_buildTime_175_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, sizeof(void*)*3, v_action_171_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, sizeof(void*)*3 + 1, v_wantsRebuild_172_);
lean_ctor_set_uint8(v_reuseFailAlloc_190_, sizeof(void*)*3 + 2, v_canceled_173_);
v___x_186_ = v_reuseFailAlloc_190_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
lean_object* v___x_188_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set(v___x_183_, 1, v___x_186_);
v___x_188_ = v___x_183_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_fst_180_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadStateOfLogJobM___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_162_ = stack[1].m_obj;
lean_object* v___y_163_ = stack[2].m_obj;
lean_object* v___y_164_ = stack[3].m_obj;
lean_object* v___y_165_ = stack[4].m_obj;
lean_object* v___y_166_ = stack[5].m_obj;
lean_object* v___y_167_ = stack[6].m_obj;
lean_object* v___y_168_ = stack[7].m_obj;
lean_object* v_res_193_;
v_res_193_ = l_Lake_instMonadStateOfLogJobM___lam__2(lean_box(0), v_f_162_, v___y_163_, v___y_164_, v___y_165_, v___y_166_, v___y_167_, v___y_168_);
stack->m_obj
 = v_res_193_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2___boxed(lean_object* v_00_u03b1_194_, lean_object* v_f_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = l_Lake_instMonadStateOfLogJobM___lam__2(v_00_u03b1_194_, v_f_195_, v___y_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_, v___y_201_);
lean_dec_ref(v___y_200_);
lean_dec(v___y_199_);
lean_dec(v___y_198_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_203_;
}
}
lean_object* l_Lake_instMonadErrorJobM___lam__0(lean_object* v_00_u03b1_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_log_224_; uint8_t v_action_225_; uint8_t v_wantsRebuild_226_; uint8_t v_canceled_227_; lean_object* v_trace_228_; lean_object* v_buildTime_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_241_; 
v_log_224_ = lean_ctor_get(v___y_222_, 0);
v_action_225_ = lean_ctor_get_uint8(v___y_222_, sizeof(void*)*3);
v_wantsRebuild_226_ = lean_ctor_get_uint8(v___y_222_, sizeof(void*)*3 + 1);
v_canceled_227_ = lean_ctor_get_uint8(v___y_222_, sizeof(void*)*3 + 2);
v_trace_228_ = lean_ctor_get(v___y_222_, 1);
v_buildTime_229_ = lean_ctor_get(v___y_222_, 2);
v_isSharedCheck_241_ = !lean_is_exclusive(v___y_222_);
if (v_isSharedCheck_241_ == 0)
{
v___x_231_ = v___y_222_;
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_buildTime_229_);
lean_inc(v_trace_228_);
lean_inc(v_log_224_);
lean_dec(v___y_222_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_241_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_233_ = 3;
v___x_234_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_234_, 0, v___y_216_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_233_);
v___x_235_ = lean_array_get_size(v_log_224_);
v___x_236_ = lean_array_push(v_log_224_, v___x_234_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_236_);
v___x_238_ = v___x_231_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v_trace_228_);
lean_ctor_set(v_reuseFailAlloc_240_, 2, v_buildTime_229_);
lean_ctor_set_uint8(v_reuseFailAlloc_240_, sizeof(void*)*3, v_action_225_);
lean_ctor_set_uint8(v_reuseFailAlloc_240_, sizeof(void*)*3 + 1, v_wantsRebuild_226_);
lean_ctor_set_uint8(v_reuseFailAlloc_240_, sizeof(void*)*3 + 2, v_canceled_227_);
v___x_238_ = v_reuseFailAlloc_240_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; 
v___x_239_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_235_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
return v___x_239_;
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadErrorJobM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_216_ = stack[1].m_obj;
lean_object* v___y_217_ = stack[2].m_obj;
lean_object* v___y_218_ = stack[3].m_obj;
lean_object* v___y_219_ = stack[4].m_obj;
lean_object* v___y_220_ = stack[5].m_obj;
lean_object* v___y_221_ = stack[6].m_obj;
lean_object* v___y_222_ = stack[7].m_obj;
lean_object* v_res_242_;
v_res_242_ = l_Lake_instMonadErrorJobM___lam__0(lean_box(0), v___y_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_, v___y_222_);
stack->m_obj
 = v_res_242_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0___boxed(lean_object* v_00_u03b1_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lake_instMonadErrorJobM___lam__0(v_00_u03b1_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
return v_res_252_;
}
}
lean_object* l_Lake_instAlternativeJobM___lam__0(lean_object* v_00_u03b1_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_){
_start:
{
lean_object* v_log_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_log_263_ = lean_ctor_get(v___y_261_, 0);
v___x_264_ = lean_array_get_size(v_log_263_);
v___x_265_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v___y_261_);
return v___x_265_;
}
}
LEAN_EXPORT void l_Lake_instAlternativeJobM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_256_ = stack[1].m_obj;
lean_object* v___y_257_ = stack[2].m_obj;
lean_object* v___y_258_ = stack[3].m_obj;
lean_object* v___y_259_ = stack[4].m_obj;
lean_object* v___y_260_ = stack[5].m_obj;
lean_object* v___y_261_ = stack[6].m_obj;
lean_object* v_res_266_;
v_res_266_ = l_Lake_instAlternativeJobM___lam__0(lean_box(0), v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_);
stack->m_obj
 = v_res_266_;
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0___boxed(lean_object* v_00_u03b1_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Lake_instAlternativeJobM___lam__0(v_00_u03b1_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_);
lean_dec_ref(v___y_272_);
lean_dec(v___y_271_);
lean_dec(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
return v_res_275_;
}
}
lean_object* l_Lake_instAlternativeJobM___lam__1(lean_object* v_00_u03b1_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; 
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc(v___y_281_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
v___x_286_ = lean_apply_7(v___y_277_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, lean_box(0));
if (lean_obj_tag(v___x_286_) == 0)
{
lean_dec_ref(v___y_279_);
lean_dec_ref(v___y_278_);
return v___x_286_;
}
else
{
lean_object* v_a_287_; lean_object* v_a_288_; lean_object* v_log_289_; uint8_t v_action_290_; uint8_t v_wantsRebuild_291_; uint8_t v_canceled_292_; lean_object* v_trace_293_; lean_object* v_buildTime_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_304_; 
v_a_287_ = lean_ctor_get(v___x_286_, 1);
lean_inc(v_a_287_);
v_a_288_ = lean_ctor_get(v___x_286_, 0);
lean_inc(v_a_288_);
lean_dec_ref_known(v___x_286_, 2);
v_log_289_ = lean_ctor_get(v_a_287_, 0);
v_action_290_ = lean_ctor_get_uint8(v_a_287_, sizeof(void*)*3);
v_wantsRebuild_291_ = lean_ctor_get_uint8(v_a_287_, sizeof(void*)*3 + 1);
v_canceled_292_ = lean_ctor_get_uint8(v_a_287_, sizeof(void*)*3 + 2);
v_trace_293_ = lean_ctor_get(v_a_287_, 1);
v_buildTime_294_ = lean_ctor_get(v_a_287_, 2);
v_isSharedCheck_304_ = !lean_is_exclusive(v_a_287_);
if (v_isSharedCheck_304_ == 0)
{
v___x_296_ = v_a_287_;
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_buildTime_294_);
lean_inc(v_trace_293_);
lean_inc(v_log_289_);
lean_dec(v_a_287_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_300_; 
v___x_298_ = l_Array_shrink___redArg(v_log_289_, v_a_288_);
lean_dec(v_a_288_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 0, v___x_298_);
v___x_300_ = v___x_296_;
goto v_reusejp_299_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_298_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_trace_293_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_buildTime_294_);
lean_ctor_set_uint8(v_reuseFailAlloc_303_, sizeof(void*)*3, v_action_290_);
lean_ctor_set_uint8(v_reuseFailAlloc_303_, sizeof(void*)*3 + 1, v_wantsRebuild_291_);
lean_ctor_set_uint8(v_reuseFailAlloc_303_, sizeof(void*)*3 + 2, v_canceled_292_);
v___x_300_ = v_reuseFailAlloc_303_;
goto v_reusejp_299_;
}
v_reusejp_299_:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_box(0);
lean_inc_ref(v___y_283_);
lean_inc(v___y_282_);
lean_inc(v___y_281_);
lean_inc(v___y_280_);
v___x_302_ = lean_apply_8(v___y_278_, v___x_301_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___x_300_, lean_box(0));
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_instAlternativeJobM___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_277_ = stack[1].m_obj;
lean_object* v___y_278_ = stack[2].m_obj;
lean_object* v___y_279_ = stack[3].m_obj;
lean_object* v___y_280_ = stack[4].m_obj;
lean_object* v___y_281_ = stack[5].m_obj;
lean_object* v___y_282_ = stack[6].m_obj;
lean_object* v___y_283_ = stack[7].m_obj;
lean_object* v___y_284_ = stack[8].m_obj;
lean_object* v_res_305_;
v_res_305_ = l_Lake_instAlternativeJobM___lam__1(lean_box(0), v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_);
stack->m_obj
 = v_res_305_;
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1___boxed(lean_object* v_00_u03b1_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lake_instAlternativeJobM___lam__1(v_00_u03b1_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec(v___y_311_);
lean_dec(v___y_310_);
return v_res_316_;
}
}
static lean_object* _init_l_Lake_instAlternativeJobM(void){
_start:
{
lean_object* v___x_319_; lean_object* v_toApplicative_320_; lean_object* v_toBind_321_; lean_object* v_toFunctor_322_; lean_object* v_toPure_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___f_326_; lean_object* v___f_327_; lean_object* v___x_328_; lean_object* v___f_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_toApplicative_337_; lean_object* v___f_338_; lean_object* v___f_339_; lean_object* v___x_340_; 
v___x_319_ = l_instMonadBaseIO;
v_toApplicative_320_ = lean_ctor_get(v___x_319_, 0);
v_toBind_321_ = lean_ctor_get(v___x_319_, 1);
v_toFunctor_322_ = lean_ctor_get(v_toApplicative_320_, 0);
v_toPure_323_ = lean_ctor_get(v_toApplicative_320_, 1);
lean_inc_n(v_toBind_321_, 3);
lean_inc_n(v_toPure_323_, 5);
v___f_324_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_324_, 0, v_toPure_323_);
lean_closure_set(v___f_324_, 1, v_toBind_321_);
v___f_325_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_325_, 0, v_toPure_323_);
lean_closure_set(v___f_325_, 1, v_toBind_321_);
lean_inc_ref(v___f_324_);
v___f_326_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_326_, 0, v_toPure_323_);
lean_closure_set(v___f_326_, 1, v___f_324_);
lean_inc_ref_n(v_toFunctor_322_, 2);
v___f_327_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_327_, 0, v_toFunctor_322_);
lean_closure_set(v___f_327_, 1, v_toPure_323_);
lean_closure_set(v___f_327_, 2, v_toBind_321_);
v___x_328_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_322_);
v___f_329_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_329_, 0, v_toPure_323_);
v___x_330_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___f_329_);
lean_ctor_set(v___x_330_, 2, v___f_327_);
lean_ctor_set(v___x_330_, 3, v___f_326_);
lean_ctor_set(v___x_330_, 4, v___f_325_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___f_324_);
v___x_332_ = l_ReaderT_instMonad___redArg(v___x_331_);
v___x_333_ = l_StateRefT_x27_instMonad___redArg(v___x_332_);
v___x_334_ = l_ReaderT_instMonad___redArg(v___x_333_);
v___x_335_ = l_ReaderT_instMonad___redArg(v___x_334_);
v___x_336_ = l_Lake_EquipT_instMonad___redArg(v___x_335_);
v_toApplicative_337_ = lean_ctor_get(v___x_336_, 0);
lean_inc_ref(v_toApplicative_337_);
lean_dec_ref(v___x_336_);
v___f_338_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__0));
v___f_339_ = ((lean_object*)(l_Lake_instAlternativeJobM___closed__1));
v___x_340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_340_, 0, v_toApplicative_337_);
lean_ctor_set(v___x_340_, 1, v___f_338_);
lean_ctor_set(v___x_340_, 2, v___f_339_);
return v___x_340_;
}
}
lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0(lean_object* v_00_u03b1_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v_log_350_; uint8_t v_action_351_; uint8_t v_wantsRebuild_352_; uint8_t v_canceled_353_; lean_object* v_trace_354_; lean_object* v_buildTime_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_384_; 
v_log_350_ = lean_ctor_get(v___y_348_, 0);
v_action_351_ = lean_ctor_get_uint8(v___y_348_, sizeof(void*)*3);
v_wantsRebuild_352_ = lean_ctor_get_uint8(v___y_348_, sizeof(void*)*3 + 1);
v_canceled_353_ = lean_ctor_get_uint8(v___y_348_, sizeof(void*)*3 + 2);
v_trace_354_ = lean_ctor_get(v___y_348_, 1);
v_buildTime_355_ = lean_ctor_get(v___y_348_, 2);
v_isSharedCheck_384_ = !lean_is_exclusive(v___y_348_);
if (v_isSharedCheck_384_ == 0)
{
v___x_357_ = v___y_348_;
v_isShared_358_ = v_isSharedCheck_384_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_buildTime_355_);
lean_inc(v_trace_354_);
lean_inc(v_log_350_);
lean_dec(v___y_348_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_384_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; 
v___x_359_ = lean_apply_2(v___y_342_, v_log_350_, lean_box(0));
if (lean_obj_tag(v___x_359_) == 0)
{
lean_object* v_a_360_; lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_371_; 
v_a_360_ = lean_ctor_get(v___x_359_, 0);
v_a_361_ = lean_ctor_get(v___x_359_, 1);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_371_ == 0)
{
v___x_363_ = v___x_359_;
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_inc(v_a_360_);
lean_dec(v___x_359_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_371_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v_a_361_);
v___x_366_ = v___x_357_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_361_);
lean_ctor_set(v_reuseFailAlloc_370_, 1, v_trace_354_);
lean_ctor_set(v_reuseFailAlloc_370_, 2, v_buildTime_355_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3, v_action_351_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3 + 1, v_wantsRebuild_352_);
lean_ctor_set_uint8(v_reuseFailAlloc_370_, sizeof(void*)*3 + 2, v_canceled_353_);
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
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 2, 0);
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
else
{
lean_object* v_a_372_; lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_383_; 
v_a_372_ = lean_ctor_get(v___x_359_, 0);
v_a_373_ = lean_ctor_get(v___x_359_, 1);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_359_);
if (v_isSharedCheck_383_ == 0)
{
v___x_375_ = v___x_359_;
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_inc(v_a_372_);
lean_dec(v___x_359_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_383_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v_a_373_);
v___x_378_ = v___x_357_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_373_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_trace_354_);
lean_ctor_set(v_reuseFailAlloc_382_, 2, v_buildTime_355_);
lean_ctor_set_uint8(v_reuseFailAlloc_382_, sizeof(void*)*3, v_action_351_);
lean_ctor_set_uint8(v_reuseFailAlloc_382_, sizeof(void*)*3 + 1, v_wantsRebuild_352_);
lean_ctor_set_uint8(v_reuseFailAlloc_382_, sizeof(void*)*3 + 2, v_canceled_353_);
v___x_378_ = v_reuseFailAlloc_382_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 1, v___x_378_);
v___x_380_ = v___x_375_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_a_372_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_instMonadLiftLogIOJobM___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_342_ = stack[1].m_obj;
lean_object* v___y_343_ = stack[2].m_obj;
lean_object* v___y_344_ = stack[3].m_obj;
lean_object* v___y_345_ = stack[4].m_obj;
lean_object* v___y_346_ = stack[5].m_obj;
lean_object* v___y_347_ = stack[6].m_obj;
lean_object* v___y_348_ = stack[7].m_obj;
lean_object* v_res_385_;
v_res_385_ = l_Lake_instMonadLiftLogIOJobM___lam__0(lean_box(0), v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
stack->m_obj
 = v_res_385_;
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(lean_object* v_00_u03b1_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lake_instMonadLiftLogIOJobM___lam__0(v_00_u03b1_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_);
lean_dec_ref(v___y_392_);
lean_dec(v___y_391_);
lean_dec(v___y_390_);
lean_dec(v___y_389_);
lean_dec_ref(v___y_388_);
return v_res_395_;
}
}
lean_object* l_Lake_updateAction___redArg(uint8_t v_action_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_log_401_; uint8_t v_action_402_; uint8_t v_wantsRebuild_403_; uint8_t v_canceled_404_; lean_object* v_trace_405_; lean_object* v_buildTime_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_416_; 
v_log_401_ = lean_ctor_get(v_a_399_, 0);
v_action_402_ = lean_ctor_get_uint8(v_a_399_, sizeof(void*)*3);
v_wantsRebuild_403_ = lean_ctor_get_uint8(v_a_399_, sizeof(void*)*3 + 1);
v_canceled_404_ = lean_ctor_get_uint8(v_a_399_, sizeof(void*)*3 + 2);
v_trace_405_ = lean_ctor_get(v_a_399_, 1);
v_buildTime_406_ = lean_ctor_get(v_a_399_, 2);
v_isSharedCheck_416_ = !lean_is_exclusive(v_a_399_);
if (v_isSharedCheck_416_ == 0)
{
v___x_408_ = v_a_399_;
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_buildTime_406_);
lean_inc(v_trace_405_);
lean_inc(v_log_401_);
lean_dec(v_a_399_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_416_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
lean_object* v___x_410_; uint8_t v___x_411_; lean_object* v___x_413_; 
v___x_410_ = lean_box(0);
v___x_411_ = l_Lake_JobAction_merge(v_action_402_, v_action_398_);
if (v_isShared_409_ == 0)
{
v___x_413_ = v___x_408_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_log_401_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v_trace_405_);
lean_ctor_set(v_reuseFailAlloc_415_, 2, v_buildTime_406_);
lean_ctor_set_uint8(v_reuseFailAlloc_415_, sizeof(void*)*3 + 1, v_wantsRebuild_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_415_, sizeof(void*)*3 + 2, v_canceled_404_);
v___x_413_ = v_reuseFailAlloc_415_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
lean_object* v___x_414_; 
lean_ctor_set_uint8(v___x_413_, sizeof(void*)*3, v___x_411_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_410_);
lean_ctor_set(v___x_414_, 1, v___x_413_);
return v___x_414_;
}
}
}
}
LEAN_EXPORT void l_Lake_updateAction___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_action_398_ = stack[0].m_num;
lean_object* v_a_399_ = stack[1].m_obj;
lean_object* v_res_417_;
v_res_417_ = l_Lake_updateAction___redArg(v_action_398_, v_a_399_);
stack->m_obj
 = v_res_417_;
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg___boxed(lean_object* v_action_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
uint8_t v_action_boxed_421_; lean_object* v_res_422_; 
v_action_boxed_421_ = lean_unbox(v_action_418_);
v_res_422_ = l_Lake_updateAction___redArg(v_action_boxed_421_, v_a_419_);
return v_res_422_;
}
}
lean_object* l_Lake_updateAction(uint8_t v_action_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_log_431_; uint8_t v_action_432_; uint8_t v_wantsRebuild_433_; uint8_t v_canceled_434_; lean_object* v_trace_435_; lean_object* v_buildTime_436_; lean_object* v___x_438_; uint8_t v_isShared_439_; uint8_t v_isSharedCheck_446_; 
v_log_431_ = lean_ctor_get(v_a_429_, 0);
v_action_432_ = lean_ctor_get_uint8(v_a_429_, sizeof(void*)*3);
v_wantsRebuild_433_ = lean_ctor_get_uint8(v_a_429_, sizeof(void*)*3 + 1);
v_canceled_434_ = lean_ctor_get_uint8(v_a_429_, sizeof(void*)*3 + 2);
v_trace_435_ = lean_ctor_get(v_a_429_, 1);
v_buildTime_436_ = lean_ctor_get(v_a_429_, 2);
v_isSharedCheck_446_ = !lean_is_exclusive(v_a_429_);
if (v_isSharedCheck_446_ == 0)
{
v___x_438_ = v_a_429_;
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
else
{
lean_inc(v_buildTime_436_);
lean_inc(v_trace_435_);
lean_inc(v_log_431_);
lean_dec(v_a_429_);
v___x_438_ = lean_box(0);
v_isShared_439_ = v_isSharedCheck_446_;
goto v_resetjp_437_;
}
v_resetjp_437_:
{
lean_object* v___x_440_; uint8_t v___x_441_; lean_object* v___x_443_; 
v___x_440_ = lean_box(0);
v___x_441_ = l_Lake_JobAction_merge(v_action_432_, v_action_423_);
if (v_isShared_439_ == 0)
{
v___x_443_ = v___x_438_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_log_431_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_trace_435_);
lean_ctor_set(v_reuseFailAlloc_445_, 2, v_buildTime_436_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*3 + 1, v_wantsRebuild_433_);
lean_ctor_set_uint8(v_reuseFailAlloc_445_, sizeof(void*)*3 + 2, v_canceled_434_);
v___x_443_ = v_reuseFailAlloc_445_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_444_; 
lean_ctor_set_uint8(v___x_443_, sizeof(void*)*3, v___x_441_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_440_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
return v___x_444_;
}
}
}
}
LEAN_EXPORT void l_Lake_updateAction_0interp(lean_interpreter_value* stack)
{
uint8_t v_action_423_ = stack[0].m_num;
lean_object* v_a_424_ = stack[1].m_obj;
lean_object* v_a_425_ = stack[2].m_obj;
lean_object* v_a_426_ = stack[3].m_obj;
lean_object* v_a_427_ = stack[4].m_obj;
lean_object* v_a_428_ = stack[5].m_obj;
lean_object* v_a_429_ = stack[6].m_obj;
lean_object* v_res_447_;
v_res_447_ = l_Lake_updateAction(v_action_423_, v_a_424_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
stack->m_obj
 = v_res_447_;
}
LEAN_EXPORT lean_object* l_Lake_updateAction___boxed(lean_object* v_action_448_, lean_object* v_a_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
uint8_t v_action_boxed_456_; lean_object* v_res_457_; 
v_action_boxed_456_ = lean_unbox(v_action_448_);
v_res_457_ = l_Lake_updateAction(v_action_boxed_456_, v_a_449_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_);
lean_dec_ref(v_a_453_);
lean_dec(v_a_452_);
lean_dec(v_a_451_);
lean_dec(v_a_450_);
lean_dec_ref(v_a_449_);
return v_res_457_;
}
}
lean_object* l_Lake_getTrace___redArg(lean_object* v_a_458_){
_start:
{
lean_object* v_trace_460_; lean_object* v___x_461_; 
v_trace_460_ = lean_ctor_get(v_a_458_, 1);
lean_inc_ref(v_trace_460_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_trace_460_);
lean_ctor_set(v___x_461_, 1, v_a_458_);
return v___x_461_;
}
}
LEAN_EXPORT void l_Lake_getTrace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_458_ = stack[0].m_obj;
lean_object* v_res_462_;
v_res_462_ = l_Lake_getTrace___redArg(v_a_458_);
stack->m_obj
 = v_res_462_;
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg___boxed(lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lake_getTrace___redArg(v_a_463_);
return v_res_465_;
}
}
lean_object* l_Lake_getTrace(lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_trace_473_; lean_object* v___x_474_; 
v_trace_473_ = lean_ctor_get(v_a_471_, 1);
lean_inc_ref(v_trace_473_);
v___x_474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_474_, 0, v_trace_473_);
lean_ctor_set(v___x_474_, 1, v_a_471_);
return v___x_474_;
}
}
LEAN_EXPORT void l_Lake_getTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_466_ = stack[0].m_obj;
lean_object* v_a_467_ = stack[1].m_obj;
lean_object* v_a_468_ = stack[2].m_obj;
lean_object* v_a_469_ = stack[3].m_obj;
lean_object* v_a_470_ = stack[4].m_obj;
lean_object* v_a_471_ = stack[5].m_obj;
lean_object* v_res_475_;
v_res_475_ = l_Lake_getTrace(v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_);
stack->m_obj
 = v_res_475_;
}
LEAN_EXPORT lean_object* l_Lake_getTrace___boxed(lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Lake_getTrace(v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
lean_dec_ref(v_a_480_);
lean_dec(v_a_479_);
lean_dec(v_a_478_);
lean_dec(v_a_477_);
lean_dec_ref(v_a_476_);
return v_res_483_;
}
}
lean_object* l_Lake_setTrace___redArg(lean_object* v_trace_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_log_487_; uint8_t v_action_488_; uint8_t v_wantsRebuild_489_; uint8_t v_canceled_490_; lean_object* v_buildTime_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_500_; 
v_log_487_ = lean_ctor_get(v_a_485_, 0);
v_action_488_ = lean_ctor_get_uint8(v_a_485_, sizeof(void*)*3);
v_wantsRebuild_489_ = lean_ctor_get_uint8(v_a_485_, sizeof(void*)*3 + 1);
v_canceled_490_ = lean_ctor_get_uint8(v_a_485_, sizeof(void*)*3 + 2);
v_buildTime_491_ = lean_ctor_get(v_a_485_, 2);
v_isSharedCheck_500_ = !lean_is_exclusive(v_a_485_);
if (v_isSharedCheck_500_ == 0)
{
lean_object* v_unused_501_; 
v_unused_501_ = lean_ctor_get(v_a_485_, 1);
lean_dec(v_unused_501_);
v___x_493_ = v_a_485_;
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_buildTime_491_);
lean_inc(v_log_487_);
lean_dec(v_a_485_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_500_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_497_; 
v___x_495_ = lean_box(0);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 1, v_trace_484_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_log_487_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_trace_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_buildTime_491_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*3, v_action_488_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*3 + 1, v_wantsRebuild_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_499_, sizeof(void*)*3 + 2, v_canceled_490_);
v___x_497_ = v_reuseFailAlloc_499_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; 
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_495_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
return v___x_498_;
}
}
}
}
LEAN_EXPORT void l_Lake_setTrace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_trace_484_ = stack[0].m_obj;
lean_object* v_a_485_ = stack[1].m_obj;
lean_object* v_res_502_;
v_res_502_ = l_Lake_setTrace___redArg(v_trace_484_, v_a_485_);
stack->m_obj
 = v_res_502_;
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg___boxed(lean_object* v_trace_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Lake_setTrace___redArg(v_trace_503_, v_a_504_);
return v_res_506_;
}
}
lean_object* l_Lake_setTrace(lean_object* v_trace_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_){
_start:
{
lean_object* v_log_515_; uint8_t v_action_516_; uint8_t v_wantsRebuild_517_; uint8_t v_canceled_518_; lean_object* v_buildTime_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_528_; 
v_log_515_ = lean_ctor_get(v_a_513_, 0);
v_action_516_ = lean_ctor_get_uint8(v_a_513_, sizeof(void*)*3);
v_wantsRebuild_517_ = lean_ctor_get_uint8(v_a_513_, sizeof(void*)*3 + 1);
v_canceled_518_ = lean_ctor_get_uint8(v_a_513_, sizeof(void*)*3 + 2);
v_buildTime_519_ = lean_ctor_get(v_a_513_, 2);
v_isSharedCheck_528_ = !lean_is_exclusive(v_a_513_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v_a_513_, 1);
lean_dec(v_unused_529_);
v___x_521_ = v_a_513_;
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_buildTime_519_);
lean_inc(v_log_515_);
lean_dec(v_a_513_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_528_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
lean_object* v___x_523_; lean_object* v___x_525_; 
v___x_523_ = lean_box(0);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 1, v_trace_507_);
v___x_525_ = v___x_521_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_log_515_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_trace_507_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_buildTime_519_);
lean_ctor_set_uint8(v_reuseFailAlloc_527_, sizeof(void*)*3, v_action_516_);
lean_ctor_set_uint8(v_reuseFailAlloc_527_, sizeof(void*)*3 + 1, v_wantsRebuild_517_);
lean_ctor_set_uint8(v_reuseFailAlloc_527_, sizeof(void*)*3 + 2, v_canceled_518_);
v___x_525_ = v_reuseFailAlloc_527_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
lean_object* v___x_526_; 
v___x_526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_523_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
return v___x_526_;
}
}
}
}
LEAN_EXPORT void l_Lake_setTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_trace_507_ = stack[0].m_obj;
lean_object* v_a_508_ = stack[1].m_obj;
lean_object* v_a_509_ = stack[2].m_obj;
lean_object* v_a_510_ = stack[3].m_obj;
lean_object* v_a_511_ = stack[4].m_obj;
lean_object* v_a_512_ = stack[5].m_obj;
lean_object* v_a_513_ = stack[6].m_obj;
lean_object* v_res_530_;
v_res_530_ = l_Lake_setTrace(v_trace_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
stack->m_obj
 = v_res_530_;
}
LEAN_EXPORT lean_object* l_Lake_setTrace___boxed(lean_object* v_trace_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l_Lake_setTrace(v_trace_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
return v_res_539_;
}
}
lean_object* l_Lake_newTrace___redArg(lean_object* v_caption_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_log_543_; uint8_t v_action_544_; uint8_t v_wantsRebuild_545_; uint8_t v_canceled_546_; lean_object* v_buildTime_547_; lean_object* v___x_549_; uint8_t v_isShared_550_; uint8_t v_isSharedCheck_557_; 
v_log_543_ = lean_ctor_get(v_a_541_, 0);
v_action_544_ = lean_ctor_get_uint8(v_a_541_, sizeof(void*)*3);
v_wantsRebuild_545_ = lean_ctor_get_uint8(v_a_541_, sizeof(void*)*3 + 1);
v_canceled_546_ = lean_ctor_get_uint8(v_a_541_, sizeof(void*)*3 + 2);
v_buildTime_547_ = lean_ctor_get(v_a_541_, 2);
v_isSharedCheck_557_ = !lean_is_exclusive(v_a_541_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; 
v_unused_558_ = lean_ctor_get(v_a_541_, 1);
lean_dec(v_unused_558_);
v___x_549_ = v_a_541_;
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
else
{
lean_inc(v_buildTime_547_);
lean_inc(v_log_543_);
lean_dec(v_a_541_);
v___x_549_ = lean_box(0);
v_isShared_550_ = v_isSharedCheck_557_;
goto v_resetjp_548_;
}
v_resetjp_548_:
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_551_ = l_Lake_BuildTrace_nil(v_caption_540_);
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
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_log_543_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v___x_551_);
lean_ctor_set(v_reuseFailAlloc_556_, 2, v_buildTime_547_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*3, v_action_544_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*3 + 1, v_wantsRebuild_545_);
lean_ctor_set_uint8(v_reuseFailAlloc_556_, sizeof(void*)*3 + 2, v_canceled_546_);
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
LEAN_EXPORT void l_Lake_newTrace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_caption_540_ = stack[0].m_obj;
lean_object* v_a_541_ = stack[1].m_obj;
lean_object* v_res_559_;
v_res_559_ = l_Lake_newTrace___redArg(v_caption_540_, v_a_541_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg___boxed(lean_object* v_caption_560_, lean_object* v_a_561_, lean_object* v_a_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lake_newTrace___redArg(v_caption_560_, v_a_561_);
return v_res_563_;
}
}
lean_object* l_Lake_newTrace(lean_object* v_caption_564_, lean_object* v_a_565_, lean_object* v_a_566_, lean_object* v_a_567_, lean_object* v_a_568_, lean_object* v_a_569_, lean_object* v_a_570_){
_start:
{
lean_object* v_log_572_; uint8_t v_action_573_; uint8_t v_wantsRebuild_574_; uint8_t v_canceled_575_; lean_object* v_buildTime_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_586_; 
v_log_572_ = lean_ctor_get(v_a_570_, 0);
v_action_573_ = lean_ctor_get_uint8(v_a_570_, sizeof(void*)*3);
v_wantsRebuild_574_ = lean_ctor_get_uint8(v_a_570_, sizeof(void*)*3 + 1);
v_canceled_575_ = lean_ctor_get_uint8(v_a_570_, sizeof(void*)*3 + 2);
v_buildTime_576_ = lean_ctor_get(v_a_570_, 2);
v_isSharedCheck_586_ = !lean_is_exclusive(v_a_570_);
if (v_isSharedCheck_586_ == 0)
{
lean_object* v_unused_587_; 
v_unused_587_ = lean_ctor_get(v_a_570_, 1);
lean_dec(v_unused_587_);
v___x_578_ = v_a_570_;
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_buildTime_576_);
lean_inc(v_log_572_);
lean_dec(v_a_570_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_586_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_583_; 
v___x_580_ = l_Lake_BuildTrace_nil(v_caption_564_);
v___x_581_ = lean_box(0);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v___x_580_);
v___x_583_ = v___x_578_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_log_572_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_585_, 2, v_buildTime_576_);
lean_ctor_set_uint8(v_reuseFailAlloc_585_, sizeof(void*)*3, v_action_573_);
lean_ctor_set_uint8(v_reuseFailAlloc_585_, sizeof(void*)*3 + 1, v_wantsRebuild_574_);
lean_ctor_set_uint8(v_reuseFailAlloc_585_, sizeof(void*)*3 + 2, v_canceled_575_);
v___x_583_ = v_reuseFailAlloc_585_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_584_; 
v___x_584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_584_, 0, v___x_581_);
lean_ctor_set(v___x_584_, 1, v___x_583_);
return v___x_584_;
}
}
}
}
LEAN_EXPORT void l_Lake_newTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_caption_564_ = stack[0].m_obj;
lean_object* v_a_565_ = stack[1].m_obj;
lean_object* v_a_566_ = stack[2].m_obj;
lean_object* v_a_567_ = stack[3].m_obj;
lean_object* v_a_568_ = stack[4].m_obj;
lean_object* v_a_569_ = stack[5].m_obj;
lean_object* v_a_570_ = stack[6].m_obj;
lean_object* v_res_588_;
v_res_588_ = l_Lake_newTrace(v_caption_564_, v_a_565_, v_a_566_, v_a_567_, v_a_568_, v_a_569_, v_a_570_);
stack->m_obj
 = v_res_588_;
}
LEAN_EXPORT lean_object* l_Lake_newTrace___boxed(lean_object* v_caption_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lake_newTrace(v_caption_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_, v_a_595_);
lean_dec_ref(v_a_594_);
lean_dec(v_a_593_);
lean_dec(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_597_;
}
}
lean_object* l_Lake_modifyTrace___redArg(lean_object* v_f_598_, lean_object* v_a_599_){
_start:
{
lean_object* v_log_601_; uint8_t v_action_602_; uint8_t v_wantsRebuild_603_; uint8_t v_canceled_604_; lean_object* v_trace_605_; lean_object* v_buildTime_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_616_; 
v_log_601_ = lean_ctor_get(v_a_599_, 0);
v_action_602_ = lean_ctor_get_uint8(v_a_599_, sizeof(void*)*3);
v_wantsRebuild_603_ = lean_ctor_get_uint8(v_a_599_, sizeof(void*)*3 + 1);
v_canceled_604_ = lean_ctor_get_uint8(v_a_599_, sizeof(void*)*3 + 2);
v_trace_605_ = lean_ctor_get(v_a_599_, 1);
v_buildTime_606_ = lean_ctor_get(v_a_599_, 2);
v_isSharedCheck_616_ = !lean_is_exclusive(v_a_599_);
if (v_isSharedCheck_616_ == 0)
{
v___x_608_ = v_a_599_;
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_buildTime_606_);
lean_inc(v_trace_605_);
lean_inc(v_log_601_);
lean_dec(v_a_599_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_613_; 
v___x_610_ = lean_box(0);
v___x_611_ = lean_apply_1(v_f_598_, v_trace_605_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 1, v___x_611_);
v___x_613_ = v___x_608_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_log_601_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v___x_611_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_buildTime_606_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*3, v_action_602_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*3 + 1, v_wantsRebuild_603_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*3 + 2, v_canceled_604_);
v___x_613_ = v_reuseFailAlloc_615_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
lean_object* v___x_614_; 
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_610_);
lean_ctor_set(v___x_614_, 1, v___x_613_);
return v___x_614_;
}
}
}
}
LEAN_EXPORT void l_Lake_modifyTrace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_598_ = stack[0].m_obj;
lean_object* v_a_599_ = stack[1].m_obj;
lean_object* v_res_617_;
v_res_617_ = l_Lake_modifyTrace___redArg(v_f_598_, v_a_599_);
stack->m_obj
 = v_res_617_;
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg___boxed(lean_object* v_f_618_, lean_object* v_a_619_, lean_object* v_a_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lake_modifyTrace___redArg(v_f_618_, v_a_619_);
return v_res_621_;
}
}
lean_object* l_Lake_modifyTrace(lean_object* v_f_622_, lean_object* v_a_623_, lean_object* v_a_624_, lean_object* v_a_625_, lean_object* v_a_626_, lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_log_630_; uint8_t v_action_631_; uint8_t v_wantsRebuild_632_; uint8_t v_canceled_633_; lean_object* v_trace_634_; lean_object* v_buildTime_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_645_; 
v_log_630_ = lean_ctor_get(v_a_628_, 0);
v_action_631_ = lean_ctor_get_uint8(v_a_628_, sizeof(void*)*3);
v_wantsRebuild_632_ = lean_ctor_get_uint8(v_a_628_, sizeof(void*)*3 + 1);
v_canceled_633_ = lean_ctor_get_uint8(v_a_628_, sizeof(void*)*3 + 2);
v_trace_634_ = lean_ctor_get(v_a_628_, 1);
v_buildTime_635_ = lean_ctor_get(v_a_628_, 2);
v_isSharedCheck_645_ = !lean_is_exclusive(v_a_628_);
if (v_isSharedCheck_645_ == 0)
{
v___x_637_ = v_a_628_;
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_buildTime_635_);
lean_inc(v_trace_634_);
lean_inc(v_log_630_);
lean_dec(v_a_628_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_645_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_639_ = lean_box(0);
v___x_640_ = lean_apply_1(v_f_622_, v_trace_634_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 1, v___x_640_);
v___x_642_ = v___x_637_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_log_630_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v___x_640_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_buildTime_635_);
lean_ctor_set_uint8(v_reuseFailAlloc_644_, sizeof(void*)*3, v_action_631_);
lean_ctor_set_uint8(v_reuseFailAlloc_644_, sizeof(void*)*3 + 1, v_wantsRebuild_632_);
lean_ctor_set_uint8(v_reuseFailAlloc_644_, sizeof(void*)*3 + 2, v_canceled_633_);
v___x_642_ = v_reuseFailAlloc_644_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
lean_object* v___x_643_; 
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_639_);
lean_ctor_set(v___x_643_, 1, v___x_642_);
return v___x_643_;
}
}
}
}
LEAN_EXPORT void l_Lake_modifyTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_622_ = stack[0].m_obj;
lean_object* v_a_623_ = stack[1].m_obj;
lean_object* v_a_624_ = stack[2].m_obj;
lean_object* v_a_625_ = stack[3].m_obj;
lean_object* v_a_626_ = stack[4].m_obj;
lean_object* v_a_627_ = stack[5].m_obj;
lean_object* v_a_628_ = stack[6].m_obj;
lean_object* v_res_646_;
v_res_646_ = l_Lake_modifyTrace(v_f_622_, v_a_623_, v_a_624_, v_a_625_, v_a_626_, v_a_627_, v_a_628_);
stack->m_obj
 = v_res_646_;
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___boxed(lean_object* v_f_647_, lean_object* v_a_648_, lean_object* v_a_649_, lean_object* v_a_650_, lean_object* v_a_651_, lean_object* v_a_652_, lean_object* v_a_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lake_modifyTrace(v_f_647_, v_a_648_, v_a_649_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
lean_dec_ref(v_a_652_);
lean_dec(v_a_651_);
lean_dec(v_a_650_);
lean_dec(v_a_649_);
lean_dec_ref(v_a_648_);
return v_res_655_;
}
}
lean_object* l_Lake_setTraceCaption___redArg(lean_object* v_caption_656_, lean_object* v_a_657_){
_start:
{
lean_object* v_trace_659_; lean_object* v_log_660_; uint8_t v_action_661_; uint8_t v_wantsRebuild_662_; uint8_t v_canceled_663_; lean_object* v_buildTime_664_; lean_object* v___x_666_; uint8_t v_isShared_667_; uint8_t v_isSharedCheck_684_; 
v_trace_659_ = lean_ctor_get(v_a_657_, 1);
v_log_660_ = lean_ctor_get(v_a_657_, 0);
v_action_661_ = lean_ctor_get_uint8(v_a_657_, sizeof(void*)*3);
v_wantsRebuild_662_ = lean_ctor_get_uint8(v_a_657_, sizeof(void*)*3 + 1);
v_canceled_663_ = lean_ctor_get_uint8(v_a_657_, sizeof(void*)*3 + 2);
v_buildTime_664_ = lean_ctor_get(v_a_657_, 2);
v_isSharedCheck_684_ = !lean_is_exclusive(v_a_657_);
if (v_isSharedCheck_684_ == 0)
{
v___x_666_ = v_a_657_;
v_isShared_667_ = v_isSharedCheck_684_;
goto v_resetjp_665_;
}
else
{
lean_inc(v_buildTime_664_);
lean_inc(v_trace_659_);
lean_inc(v_log_660_);
lean_dec(v_a_657_);
v___x_666_ = lean_box(0);
v_isShared_667_ = v_isSharedCheck_684_;
goto v_resetjp_665_;
}
v_resetjp_665_:
{
lean_object* v_inputs_668_; uint64_t v_hash_669_; lean_object* v_mtime_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_682_; 
v_inputs_668_ = lean_ctor_get(v_trace_659_, 1);
v_hash_669_ = lean_ctor_get_uint64(v_trace_659_, sizeof(void*)*3);
v_mtime_670_ = lean_ctor_get(v_trace_659_, 2);
v_isSharedCheck_682_ = !lean_is_exclusive(v_trace_659_);
if (v_isSharedCheck_682_ == 0)
{
lean_object* v_unused_683_; 
v_unused_683_ = lean_ctor_get(v_trace_659_, 0);
lean_dec(v_unused_683_);
v___x_672_ = v_trace_659_;
v_isShared_673_ = v_isSharedCheck_682_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_mtime_670_);
lean_inc(v_inputs_668_);
lean_dec(v_trace_659_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_682_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = lean_box(0);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v_caption_656_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_caption_656_);
lean_ctor_set(v_reuseFailAlloc_681_, 1, v_inputs_668_);
lean_ctor_set(v_reuseFailAlloc_681_, 2, v_mtime_670_);
lean_ctor_set_uint64(v_reuseFailAlloc_681_, sizeof(void*)*3, v_hash_669_);
v___x_676_ = v_reuseFailAlloc_681_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
lean_object* v___x_678_; 
if (v_isShared_667_ == 0)
{
lean_ctor_set(v___x_666_, 1, v___x_676_);
v___x_678_ = v___x_666_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_680_; 
v_reuseFailAlloc_680_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_680_, 0, v_log_660_);
lean_ctor_set(v_reuseFailAlloc_680_, 1, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_680_, 2, v_buildTime_664_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*3, v_action_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*3 + 1, v_wantsRebuild_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_680_, sizeof(void*)*3 + 2, v_canceled_663_);
v___x_678_ = v_reuseFailAlloc_680_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_679_; 
v___x_679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_679_, 0, v___x_674_);
lean_ctor_set(v___x_679_, 1, v___x_678_);
return v___x_679_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_setTraceCaption___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_caption_656_ = stack[0].m_obj;
lean_object* v_a_657_ = stack[1].m_obj;
lean_object* v_res_685_;
v_res_685_ = l_Lake_setTraceCaption___redArg(v_caption_656_, v_a_657_);
stack->m_obj
 = v_res_685_;
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg___boxed(lean_object* v_caption_686_, lean_object* v_a_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Lake_setTraceCaption___redArg(v_caption_686_, v_a_687_);
return v_res_689_;
}
}
lean_object* l_Lake_setTraceCaption(lean_object* v_caption_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_, lean_object* v_a_694_, lean_object* v_a_695_, lean_object* v_a_696_){
_start:
{
lean_object* v_trace_698_; lean_object* v_log_699_; uint8_t v_action_700_; uint8_t v_wantsRebuild_701_; uint8_t v_canceled_702_; lean_object* v_buildTime_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_723_; 
v_trace_698_ = lean_ctor_get(v_a_696_, 1);
v_log_699_ = lean_ctor_get(v_a_696_, 0);
v_action_700_ = lean_ctor_get_uint8(v_a_696_, sizeof(void*)*3);
v_wantsRebuild_701_ = lean_ctor_get_uint8(v_a_696_, sizeof(void*)*3 + 1);
v_canceled_702_ = lean_ctor_get_uint8(v_a_696_, sizeof(void*)*3 + 2);
v_buildTime_703_ = lean_ctor_get(v_a_696_, 2);
v_isSharedCheck_723_ = !lean_is_exclusive(v_a_696_);
if (v_isSharedCheck_723_ == 0)
{
v___x_705_ = v_a_696_;
v_isShared_706_ = v_isSharedCheck_723_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_buildTime_703_);
lean_inc(v_trace_698_);
lean_inc(v_log_699_);
lean_dec(v_a_696_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_723_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v_inputs_707_; uint64_t v_hash_708_; lean_object* v_mtime_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_721_; 
v_inputs_707_ = lean_ctor_get(v_trace_698_, 1);
v_hash_708_ = lean_ctor_get_uint64(v_trace_698_, sizeof(void*)*3);
v_mtime_709_ = lean_ctor_get(v_trace_698_, 2);
v_isSharedCheck_721_ = !lean_is_exclusive(v_trace_698_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v_trace_698_, 0);
lean_dec(v_unused_722_);
v___x_711_ = v_trace_698_;
v_isShared_712_ = v_isSharedCheck_721_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_mtime_709_);
lean_inc(v_inputs_707_);
lean_dec(v_trace_698_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_721_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_713_ = lean_box(0);
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v_caption_690_);
v___x_715_ = v___x_711_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_caption_690_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v_inputs_707_);
lean_ctor_set(v_reuseFailAlloc_720_, 2, v_mtime_709_);
lean_ctor_set_uint64(v_reuseFailAlloc_720_, sizeof(void*)*3, v_hash_708_);
v___x_715_ = v_reuseFailAlloc_720_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 1, v___x_715_);
v___x_717_ = v___x_705_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_log_699_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_buildTime_703_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*3, v_action_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*3 + 1, v_wantsRebuild_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_719_, sizeof(void*)*3 + 2, v_canceled_702_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_718_; 
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___x_713_);
lean_ctor_set(v___x_718_, 1, v___x_717_);
return v___x_718_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_setTraceCaption_0interp(lean_interpreter_value* stack)
{
lean_object* v_caption_690_ = stack[0].m_obj;
lean_object* v_a_691_ = stack[1].m_obj;
lean_object* v_a_692_ = stack[2].m_obj;
lean_object* v_a_693_ = stack[3].m_obj;
lean_object* v_a_694_ = stack[4].m_obj;
lean_object* v_a_695_ = stack[5].m_obj;
lean_object* v_a_696_ = stack[6].m_obj;
lean_object* v_res_724_;
v_res_724_ = l_Lake_setTraceCaption(v_caption_690_, v_a_691_, v_a_692_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
stack->m_obj
 = v_res_724_;
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___boxed(lean_object* v_caption_725_, lean_object* v_a_726_, lean_object* v_a_727_, lean_object* v_a_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
lean_object* v_res_733_; 
v_res_733_ = l_Lake_setTraceCaption(v_caption_725_, v_a_726_, v_a_727_, v_a_728_, v_a_729_, v_a_730_, v_a_731_);
lean_dec_ref(v_a_730_);
lean_dec(v_a_729_);
lean_dec(v_a_728_);
lean_dec(v_a_727_);
lean_dec_ref(v_a_726_);
return v_res_733_;
}
}
static lean_object* _init_l_Lake_takeTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = ((lean_object*)(l_Lake_takeTrace___redArg___closed__0));
v___x_736_ = l_Lake_BuildTrace_nil(v___x_735_);
return v___x_736_;
}
}
lean_object* l_Lake_takeTrace___redArg(lean_object* v_a_737_){
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
LEAN_EXPORT void l_Lake_takeTrace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_737_ = stack[0].m_obj;
lean_object* v_res_754_;
v_res_754_ = l_Lake_takeTrace___redArg(v_a_737_);
stack->m_obj
 = v_res_754_;
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg___boxed(lean_object* v_a_755_, lean_object* v_a_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lake_takeTrace___redArg(v_a_755_);
return v_res_757_;
}
}
lean_object* l_Lake_takeTrace(lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_log_765_; uint8_t v_action_766_; uint8_t v_wantsRebuild_767_; uint8_t v_canceled_768_; lean_object* v_trace_769_; lean_object* v_buildTime_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_779_; 
v_log_765_ = lean_ctor_get(v_a_763_, 0);
v_action_766_ = lean_ctor_get_uint8(v_a_763_, sizeof(void*)*3);
v_wantsRebuild_767_ = lean_ctor_get_uint8(v_a_763_, sizeof(void*)*3 + 1);
v_canceled_768_ = lean_ctor_get_uint8(v_a_763_, sizeof(void*)*3 + 2);
v_trace_769_ = lean_ctor_get(v_a_763_, 1);
v_buildTime_770_ = lean_ctor_get(v_a_763_, 2);
v_isSharedCheck_779_ = !lean_is_exclusive(v_a_763_);
if (v_isSharedCheck_779_ == 0)
{
v___x_772_ = v_a_763_;
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_buildTime_770_);
lean_inc(v_trace_769_);
lean_inc(v_log_765_);
lean_dec(v_a_763_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_779_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
v___x_774_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v___x_774_);
v___x_776_ = v___x_772_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_log_765_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_778_, 2, v_buildTime_770_);
lean_ctor_set_uint8(v_reuseFailAlloc_778_, sizeof(void*)*3, v_action_766_);
lean_ctor_set_uint8(v_reuseFailAlloc_778_, sizeof(void*)*3 + 1, v_wantsRebuild_767_);
lean_ctor_set_uint8(v_reuseFailAlloc_778_, sizeof(void*)*3 + 2, v_canceled_768_);
v___x_776_ = v_reuseFailAlloc_778_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_777_; 
v___x_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_777_, 0, v_trace_769_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
return v___x_777_;
}
}
}
}
LEAN_EXPORT void l_Lake_takeTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_758_ = stack[0].m_obj;
lean_object* v_a_759_ = stack[1].m_obj;
lean_object* v_a_760_ = stack[2].m_obj;
lean_object* v_a_761_ = stack[3].m_obj;
lean_object* v_a_762_ = stack[4].m_obj;
lean_object* v_a_763_ = stack[5].m_obj;
lean_object* v_res_780_;
v_res_780_ = l_Lake_takeTrace(v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
stack->m_obj
 = v_res_780_;
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___boxed(lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v_res_788_; 
v_res_788_ = l_Lake_takeTrace(v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_);
lean_dec_ref(v_a_785_);
lean_dec(v_a_784_);
lean_dec(v_a_783_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
return v_res_788_;
}
}
lean_object* l_Lake_swapTrace___redArg(lean_object* v_trace_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_log_792_; uint8_t v_action_793_; uint8_t v_wantsRebuild_794_; uint8_t v_canceled_795_; lean_object* v_trace_796_; lean_object* v_buildTime_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_805_; 
v_log_792_ = lean_ctor_get(v_a_790_, 0);
v_action_793_ = lean_ctor_get_uint8(v_a_790_, sizeof(void*)*3);
v_wantsRebuild_794_ = lean_ctor_get_uint8(v_a_790_, sizeof(void*)*3 + 1);
v_canceled_795_ = lean_ctor_get_uint8(v_a_790_, sizeof(void*)*3 + 2);
v_trace_796_ = lean_ctor_get(v_a_790_, 1);
v_buildTime_797_ = lean_ctor_get(v_a_790_, 2);
v_isSharedCheck_805_ = !lean_is_exclusive(v_a_790_);
if (v_isSharedCheck_805_ == 0)
{
v___x_799_ = v_a_790_;
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_buildTime_797_);
lean_inc(v_trace_796_);
lean_inc(v_log_792_);
lean_dec(v_a_790_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_805_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
lean_ctor_set(v___x_799_, 1, v_trace_789_);
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_log_792_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_trace_789_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_buildTime_797_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*3, v_action_793_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*3 + 1, v_wantsRebuild_794_);
lean_ctor_set_uint8(v_reuseFailAlloc_804_, sizeof(void*)*3 + 2, v_canceled_795_);
v___x_802_ = v_reuseFailAlloc_804_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; 
v___x_803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_803_, 0, v_trace_796_);
lean_ctor_set(v___x_803_, 1, v___x_802_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT void l_Lake_swapTrace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_trace_789_ = stack[0].m_obj;
lean_object* v_a_790_ = stack[1].m_obj;
lean_object* v_res_806_;
v_res_806_ = l_Lake_swapTrace___redArg(v_trace_789_, v_a_790_);
stack->m_obj
 = v_res_806_;
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg___boxed(lean_object* v_trace_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lake_swapTrace___redArg(v_trace_807_, v_a_808_);
return v_res_810_;
}
}
lean_object* l_Lake_swapTrace(lean_object* v_trace_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_log_819_; uint8_t v_action_820_; uint8_t v_wantsRebuild_821_; uint8_t v_canceled_822_; lean_object* v_trace_823_; lean_object* v_buildTime_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_832_; 
v_log_819_ = lean_ctor_get(v_a_817_, 0);
v_action_820_ = lean_ctor_get_uint8(v_a_817_, sizeof(void*)*3);
v_wantsRebuild_821_ = lean_ctor_get_uint8(v_a_817_, sizeof(void*)*3 + 1);
v_canceled_822_ = lean_ctor_get_uint8(v_a_817_, sizeof(void*)*3 + 2);
v_trace_823_ = lean_ctor_get(v_a_817_, 1);
v_buildTime_824_ = lean_ctor_get(v_a_817_, 2);
v_isSharedCheck_832_ = !lean_is_exclusive(v_a_817_);
if (v_isSharedCheck_832_ == 0)
{
v___x_826_ = v_a_817_;
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_buildTime_824_);
lean_inc(v_trace_823_);
lean_inc(v_log_819_);
lean_dec(v_a_817_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_832_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 1, v_trace_811_);
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v_log_819_);
lean_ctor_set(v_reuseFailAlloc_831_, 1, v_trace_811_);
lean_ctor_set(v_reuseFailAlloc_831_, 2, v_buildTime_824_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*3, v_action_820_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*3 + 1, v_wantsRebuild_821_);
lean_ctor_set_uint8(v_reuseFailAlloc_831_, sizeof(void*)*3 + 2, v_canceled_822_);
v___x_829_ = v_reuseFailAlloc_831_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_830_; 
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_trace_823_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
return v___x_830_;
}
}
}
}
LEAN_EXPORT void l_Lake_swapTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_trace_811_ = stack[0].m_obj;
lean_object* v_a_812_ = stack[1].m_obj;
lean_object* v_a_813_ = stack[2].m_obj;
lean_object* v_a_814_ = stack[3].m_obj;
lean_object* v_a_815_ = stack[4].m_obj;
lean_object* v_a_816_ = stack[5].m_obj;
lean_object* v_a_817_ = stack[6].m_obj;
lean_object* v_res_833_;
v_res_833_ = l_Lake_swapTrace(v_trace_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_);
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___boxed(lean_object* v_trace_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lake_swapTrace(v_trace_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
return v_res_842_;
}
}
lean_object* l_Lake_addTrace___redArg(lean_object* v_trace_843_, lean_object* v_a_844_){
_start:
{
lean_object* v_log_846_; uint8_t v_action_847_; uint8_t v_wantsRebuild_848_; uint8_t v_canceled_849_; lean_object* v_trace_850_; lean_object* v_buildTime_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_861_; 
v_log_846_ = lean_ctor_get(v_a_844_, 0);
v_action_847_ = lean_ctor_get_uint8(v_a_844_, sizeof(void*)*3);
v_wantsRebuild_848_ = lean_ctor_get_uint8(v_a_844_, sizeof(void*)*3 + 1);
v_canceled_849_ = lean_ctor_get_uint8(v_a_844_, sizeof(void*)*3 + 2);
v_trace_850_ = lean_ctor_get(v_a_844_, 1);
v_buildTime_851_ = lean_ctor_get(v_a_844_, 2);
v_isSharedCheck_861_ = !lean_is_exclusive(v_a_844_);
if (v_isSharedCheck_861_ == 0)
{
v___x_853_ = v_a_844_;
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_buildTime_851_);
lean_inc(v_trace_850_);
lean_inc(v_log_846_);
lean_dec(v_a_844_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_861_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_855_ = lean_box(0);
v___x_856_ = l_Lake_BuildTrace_mix(v_trace_850_, v_trace_843_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 1, v___x_856_);
v___x_858_ = v___x_853_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_log_846_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_buildTime_851_);
lean_ctor_set_uint8(v_reuseFailAlloc_860_, sizeof(void*)*3, v_action_847_);
lean_ctor_set_uint8(v_reuseFailAlloc_860_, sizeof(void*)*3 + 1, v_wantsRebuild_848_);
lean_ctor_set_uint8(v_reuseFailAlloc_860_, sizeof(void*)*3 + 2, v_canceled_849_);
v___x_858_ = v_reuseFailAlloc_860_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; 
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_855_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
return v___x_859_;
}
}
}
}
LEAN_EXPORT void l_Lake_addTrace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_trace_843_ = stack[0].m_obj;
lean_object* v_a_844_ = stack[1].m_obj;
lean_object* v_res_862_;
v_res_862_ = l_Lake_addTrace___redArg(v_trace_843_, v_a_844_);
stack->m_obj
 = v_res_862_;
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg___boxed(lean_object* v_trace_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lake_addTrace___redArg(v_trace_863_, v_a_864_);
return v_res_866_;
}
}
lean_object* l_Lake_addTrace(lean_object* v_trace_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_log_875_; uint8_t v_action_876_; uint8_t v_wantsRebuild_877_; uint8_t v_canceled_878_; lean_object* v_trace_879_; lean_object* v_buildTime_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_890_; 
v_log_875_ = lean_ctor_get(v_a_873_, 0);
v_action_876_ = lean_ctor_get_uint8(v_a_873_, sizeof(void*)*3);
v_wantsRebuild_877_ = lean_ctor_get_uint8(v_a_873_, sizeof(void*)*3 + 1);
v_canceled_878_ = lean_ctor_get_uint8(v_a_873_, sizeof(void*)*3 + 2);
v_trace_879_ = lean_ctor_get(v_a_873_, 1);
v_buildTime_880_ = lean_ctor_get(v_a_873_, 2);
v_isSharedCheck_890_ = !lean_is_exclusive(v_a_873_);
if (v_isSharedCheck_890_ == 0)
{
v___x_882_ = v_a_873_;
v_isShared_883_ = v_isSharedCheck_890_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_buildTime_880_);
lean_inc(v_trace_879_);
lean_inc(v_log_875_);
lean_dec(v_a_873_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_890_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_884_ = lean_box(0);
v___x_885_ = l_Lake_BuildTrace_mix(v_trace_879_, v_trace_867_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v___x_885_);
v___x_887_ = v___x_882_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_log_875_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_885_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_buildTime_880_);
lean_ctor_set_uint8(v_reuseFailAlloc_889_, sizeof(void*)*3, v_action_876_);
lean_ctor_set_uint8(v_reuseFailAlloc_889_, sizeof(void*)*3 + 1, v_wantsRebuild_877_);
lean_ctor_set_uint8(v_reuseFailAlloc_889_, sizeof(void*)*3 + 2, v_canceled_878_);
v___x_887_ = v_reuseFailAlloc_889_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
lean_object* v___x_888_; 
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_884_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
return v___x_888_;
}
}
}
}
LEAN_EXPORT void l_Lake_addTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_trace_867_ = stack[0].m_obj;
lean_object* v_a_868_ = stack[1].m_obj;
lean_object* v_a_869_ = stack[2].m_obj;
lean_object* v_a_870_ = stack[3].m_obj;
lean_object* v_a_871_ = stack[4].m_obj;
lean_object* v_a_872_ = stack[5].m_obj;
lean_object* v_a_873_ = stack[6].m_obj;
lean_object* v_res_891_;
v_res_891_ = l_Lake_addTrace(v_trace_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_Lake_addTrace___boxed(lean_object* v_trace_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lake_addTrace(v_trace_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
return v_res_900_;
}
}
lean_object* l_Lake_addSubTrace___redArg(lean_object* v_caption_901_, lean_object* v_x_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_log_910_; uint8_t v_action_911_; uint8_t v_wantsRebuild_912_; uint8_t v_canceled_913_; lean_object* v_trace_914_; lean_object* v_buildTime_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_947_; 
v_log_910_ = lean_ctor_get(v_a_908_, 0);
v_action_911_ = lean_ctor_get_uint8(v_a_908_, sizeof(void*)*3);
v_wantsRebuild_912_ = lean_ctor_get_uint8(v_a_908_, sizeof(void*)*3 + 1);
v_canceled_913_ = lean_ctor_get_uint8(v_a_908_, sizeof(void*)*3 + 2);
v_trace_914_ = lean_ctor_get(v_a_908_, 1);
v_buildTime_915_ = lean_ctor_get(v_a_908_, 2);
v_isSharedCheck_947_ = !lean_is_exclusive(v_a_908_);
if (v_isSharedCheck_947_ == 0)
{
v___x_917_ = v_a_908_;
v_isShared_918_ = v_isSharedCheck_947_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_buildTime_915_);
lean_inc(v_trace_914_);
lean_inc(v_log_910_);
lean_dec(v_a_908_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_947_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_919_; lean_object* v___x_921_; 
v___x_919_ = l_Lake_BuildTrace_nil(v_caption_901_);
if (v_isShared_918_ == 0)
{
lean_ctor_set(v___x_917_, 1, v___x_919_);
v___x_921_ = v___x_917_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v_log_910_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_919_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_buildTime_915_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3, v_action_911_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3 + 1, v_wantsRebuild_912_);
lean_ctor_set_uint8(v_reuseFailAlloc_946_, sizeof(void*)*3 + 2, v_canceled_913_);
v___x_921_ = v_reuseFailAlloc_946_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; 
lean_inc_ref(v_a_907_);
lean_inc(v_a_906_);
lean_inc(v_a_905_);
lean_inc(v_a_904_);
v___x_922_ = lean_apply_7(v_x_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v___x_921_, lean_box(0));
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_945_; 
v_a_923_ = lean_ctor_get(v___x_922_, 1);
v_a_924_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_945_ == 0)
{
v___x_926_ = v___x_922_;
v_isShared_927_ = v_isSharedCheck_945_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_923_);
lean_inc(v_a_924_);
lean_dec(v___x_922_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_945_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v_log_928_; uint8_t v_action_929_; uint8_t v_wantsRebuild_930_; uint8_t v_canceled_931_; lean_object* v_trace_932_; lean_object* v_buildTime_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_944_; 
v_log_928_ = lean_ctor_get(v_a_923_, 0);
v_action_929_ = lean_ctor_get_uint8(v_a_923_, sizeof(void*)*3);
v_wantsRebuild_930_ = lean_ctor_get_uint8(v_a_923_, sizeof(void*)*3 + 1);
v_canceled_931_ = lean_ctor_get_uint8(v_a_923_, sizeof(void*)*3 + 2);
v_trace_932_ = lean_ctor_get(v_a_923_, 1);
v_buildTime_933_ = lean_ctor_get(v_a_923_, 2);
v_isSharedCheck_944_ = !lean_is_exclusive(v_a_923_);
if (v_isSharedCheck_944_ == 0)
{
v___x_935_ = v_a_923_;
v_isShared_936_ = v_isSharedCheck_944_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_buildTime_933_);
lean_inc(v_trace_932_);
lean_inc(v_log_928_);
lean_dec(v_a_923_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_944_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_937_; lean_object* v___x_939_; 
v___x_937_ = l_Lake_BuildTrace_mix(v_trace_914_, v_trace_932_);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 1, v___x_937_);
v___x_939_ = v___x_935_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_log_928_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v___x_937_);
lean_ctor_set(v_reuseFailAlloc_943_, 2, v_buildTime_933_);
lean_ctor_set_uint8(v_reuseFailAlloc_943_, sizeof(void*)*3, v_action_929_);
lean_ctor_set_uint8(v_reuseFailAlloc_943_, sizeof(void*)*3 + 1, v_wantsRebuild_930_);
lean_ctor_set_uint8(v_reuseFailAlloc_943_, sizeof(void*)*3 + 2, v_canceled_931_);
v___x_939_ = v_reuseFailAlloc_943_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
lean_object* v___x_941_; 
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 1, v___x_939_);
v___x_941_ = v___x_926_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_924_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v___x_939_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
}
else
{
lean_dec_ref(v_trace_914_);
return v___x_922_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_addSubTrace___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_caption_901_ = stack[0].m_obj;
lean_object* v_x_902_ = stack[1].m_obj;
lean_object* v_a_903_ = stack[2].m_obj;
lean_object* v_a_904_ = stack[3].m_obj;
lean_object* v_a_905_ = stack[4].m_obj;
lean_object* v_a_906_ = stack[5].m_obj;
lean_object* v_a_907_ = stack[6].m_obj;
lean_object* v_a_908_ = stack[7].m_obj;
lean_object* v_res_948_;
v_res_948_ = l_Lake_addSubTrace___redArg(v_caption_901_, v_x_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
stack->m_obj
 = v_res_948_;
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___redArg___boxed(lean_object* v_caption_949_, lean_object* v_x_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Lake_addSubTrace___redArg(v_caption_949_, v_x_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_);
lean_dec_ref(v_a_955_);
lean_dec(v_a_954_);
lean_dec(v_a_953_);
lean_dec(v_a_952_);
return v_res_958_;
}
}
lean_object* l_Lake_addSubTrace(lean_object* v_00_u03b1_959_, lean_object* v_caption_960_, lean_object* v_x_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_){
_start:
{
lean_object* v_log_969_; uint8_t v_action_970_; uint8_t v_wantsRebuild_971_; uint8_t v_canceled_972_; lean_object* v_trace_973_; lean_object* v_buildTime_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_1006_; 
v_log_969_ = lean_ctor_get(v_a_967_, 0);
v_action_970_ = lean_ctor_get_uint8(v_a_967_, sizeof(void*)*3);
v_wantsRebuild_971_ = lean_ctor_get_uint8(v_a_967_, sizeof(void*)*3 + 1);
v_canceled_972_ = lean_ctor_get_uint8(v_a_967_, sizeof(void*)*3 + 2);
v_trace_973_ = lean_ctor_get(v_a_967_, 1);
v_buildTime_974_ = lean_ctor_get(v_a_967_, 2);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_a_967_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_976_ = v_a_967_;
v_isShared_977_ = v_isSharedCheck_1006_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_buildTime_974_);
lean_inc(v_trace_973_);
lean_inc(v_log_969_);
lean_dec(v_a_967_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_1006_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l_Lake_BuildTrace_nil(v_caption_960_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_log_969_);
lean_ctor_set(v_reuseFailAlloc_1005_, 1, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_1005_, 2, v_buildTime_974_);
lean_ctor_set_uint8(v_reuseFailAlloc_1005_, sizeof(void*)*3, v_action_970_);
lean_ctor_set_uint8(v_reuseFailAlloc_1005_, sizeof(void*)*3 + 1, v_wantsRebuild_971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1005_, sizeof(void*)*3 + 2, v_canceled_972_);
v___x_980_ = v_reuseFailAlloc_1005_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
lean_object* v___x_981_; 
lean_inc_ref(v_a_966_);
lean_inc(v_a_965_);
lean_inc(v_a_964_);
lean_inc(v_a_963_);
v___x_981_ = lean_apply_7(v_x_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v___x_980_, lean_box(0));
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v_a_982_; lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_1004_; 
v_a_982_ = lean_ctor_get(v___x_981_, 1);
v_a_983_ = lean_ctor_get(v___x_981_, 0);
v_isSharedCheck_1004_ = !lean_is_exclusive(v___x_981_);
if (v_isSharedCheck_1004_ == 0)
{
v___x_985_ = v___x_981_;
v_isShared_986_ = v_isSharedCheck_1004_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_982_);
lean_inc(v_a_983_);
lean_dec(v___x_981_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_1004_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v_log_987_; uint8_t v_action_988_; uint8_t v_wantsRebuild_989_; uint8_t v_canceled_990_; lean_object* v_trace_991_; lean_object* v_buildTime_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_1003_; 
v_log_987_ = lean_ctor_get(v_a_982_, 0);
v_action_988_ = lean_ctor_get_uint8(v_a_982_, sizeof(void*)*3);
v_wantsRebuild_989_ = lean_ctor_get_uint8(v_a_982_, sizeof(void*)*3 + 1);
v_canceled_990_ = lean_ctor_get_uint8(v_a_982_, sizeof(void*)*3 + 2);
v_trace_991_ = lean_ctor_get(v_a_982_, 1);
v_buildTime_992_ = lean_ctor_get(v_a_982_, 2);
v_isSharedCheck_1003_ = !lean_is_exclusive(v_a_982_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_994_ = v_a_982_;
v_isShared_995_ = v_isSharedCheck_1003_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_buildTime_992_);
lean_inc(v_trace_991_);
lean_inc(v_log_987_);
lean_dec(v_a_982_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_1003_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_996_; lean_object* v___x_998_; 
v___x_996_ = l_Lake_BuildTrace_mix(v_trace_973_, v_trace_991_);
if (v_isShared_995_ == 0)
{
lean_ctor_set(v___x_994_, 1, v___x_996_);
v___x_998_ = v___x_994_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_log_987_);
lean_ctor_set(v_reuseFailAlloc_1002_, 1, v___x_996_);
lean_ctor_set(v_reuseFailAlloc_1002_, 2, v_buildTime_992_);
lean_ctor_set_uint8(v_reuseFailAlloc_1002_, sizeof(void*)*3, v_action_988_);
lean_ctor_set_uint8(v_reuseFailAlloc_1002_, sizeof(void*)*3 + 1, v_wantsRebuild_989_);
lean_ctor_set_uint8(v_reuseFailAlloc_1002_, sizeof(void*)*3 + 2, v_canceled_990_);
v___x_998_ = v_reuseFailAlloc_1002_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_1000_; 
if (v_isShared_986_ == 0)
{
lean_ctor_set(v___x_985_, 1, v___x_998_);
v___x_1000_ = v___x_985_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_983_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v___x_998_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
else
{
lean_dec_ref(v_trace_973_);
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_addSubTrace_0interp(lean_interpreter_value* stack)
{
lean_object* v_caption_960_ = stack[1].m_obj;
lean_object* v_x_961_ = stack[2].m_obj;
lean_object* v_a_962_ = stack[3].m_obj;
lean_object* v_a_963_ = stack[4].m_obj;
lean_object* v_a_964_ = stack[5].m_obj;
lean_object* v_a_965_ = stack[6].m_obj;
lean_object* v_a_966_ = stack[7].m_obj;
lean_object* v_a_967_ = stack[8].m_obj;
lean_object* v_res_1007_;
v_res_1007_ = l_Lake_addSubTrace(lean_box(0), v_caption_960_, v_x_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
stack->m_obj
 = v_res_1007_;
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___boxed(lean_object* v_00_u03b1_1008_, lean_object* v_caption_1009_, lean_object* v_x_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lake_addSubTrace(v_00_u03b1_1008_, v_caption_1009_, v_x_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
lean_dec_ref(v_a_1015_);
lean_dec(v_a_1014_);
lean_dec(v_a_1013_);
lean_dec(v_a_1012_);
return v_res_1018_;
}
}
lean_object* l_Lake_SpawnM_ofFn___redArg(lean_object* v_f_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v___x_1027_; 
lean_inc_ref(v_a_1025_);
lean_inc_ref(v_a_1024_);
lean_inc(v_a_1023_);
lean_inc(v_a_1022_);
lean_inc(v_a_1021_);
v___x_1027_ = lean_apply_7(v_f_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, lean_box(0));
return v___x_1027_;
}
}
LEAN_EXPORT void l_Lake_SpawnM_ofFn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1019_ = stack[0].m_obj;
lean_object* v_a_1020_ = stack[1].m_obj;
lean_object* v_a_1021_ = stack[2].m_obj;
lean_object* v_a_1022_ = stack[3].m_obj;
lean_object* v_a_1023_ = stack[4].m_obj;
lean_object* v_a_1024_ = stack[5].m_obj;
lean_object* v_a_1025_ = stack[6].m_obj;
lean_object* v_res_1028_;
v_res_1028_ = l_Lake_SpawnM_ofFn___redArg(v_f_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_);
stack->m_obj
 = v_res_1028_;
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg___boxed(lean_object* v_f_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lake_SpawnM_ofFn___redArg(v_f_1029_, v_a_1030_, v_a_1031_, v_a_1032_, v_a_1033_, v_a_1034_, v_a_1035_);
lean_dec_ref(v_a_1035_);
lean_dec_ref(v_a_1034_);
lean_dec(v_a_1033_);
lean_dec(v_a_1032_);
lean_dec(v_a_1031_);
return v_res_1037_;
}
}
lean_object* l_Lake_SpawnM_ofFn(lean_object* v_00_u03b1_1038_, lean_object* v_f_1039_, lean_object* v_a_1040_, lean_object* v_a_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___x_1047_; 
lean_inc_ref(v_a_1045_);
lean_inc_ref(v_a_1044_);
lean_inc(v_a_1043_);
lean_inc(v_a_1042_);
lean_inc(v_a_1041_);
v___x_1047_ = lean_apply_7(v_f_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, lean_box(0));
return v___x_1047_;
}
}
LEAN_EXPORT void l_Lake_SpawnM_ofFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1039_ = stack[1].m_obj;
lean_object* v_a_1040_ = stack[2].m_obj;
lean_object* v_a_1041_ = stack[3].m_obj;
lean_object* v_a_1042_ = stack[4].m_obj;
lean_object* v_a_1043_ = stack[5].m_obj;
lean_object* v_a_1044_ = stack[6].m_obj;
lean_object* v_a_1045_ = stack[7].m_obj;
lean_object* v_res_1048_;
v_res_1048_ = l_Lake_SpawnM_ofFn(lean_box(0), v_f_1039_, v_a_1040_, v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_);
stack->m_obj
 = v_res_1048_;
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___boxed(lean_object* v_00_u03b1_1049_, lean_object* v_f_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lake_SpawnM_ofFn(v_00_u03b1_1049_, v_f_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_);
lean_dec_ref(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec(v_a_1053_);
lean_dec(v_a_1052_);
return v_res_1058_;
}
}
lean_object* l_Lake_SpawnM_toFn___redArg(lean_object* v_self_1059_, lean_object* v_fetch_1060_, lean_object* v_pkg_x3f_1061_, lean_object* v_stack_1062_, lean_object* v_store_1063_, lean_object* v_ctx_1064_, lean_object* v_s_1065_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_apply_7(v_self_1059_, v_fetch_1060_, v_pkg_x3f_1061_, v_stack_1062_, v_store_1063_, v_ctx_1064_, v_s_1065_, lean_box(0));
return v___x_1067_;
}
}
LEAN_EXPORT void l_Lake_SpawnM_toFn___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1059_ = stack[0].m_obj;
lean_object* v_fetch_1060_ = stack[1].m_obj;
lean_object* v_pkg_x3f_1061_ = stack[2].m_obj;
lean_object* v_stack_1062_ = stack[3].m_obj;
lean_object* v_store_1063_ = stack[4].m_obj;
lean_object* v_ctx_1064_ = stack[5].m_obj;
lean_object* v_s_1065_ = stack[6].m_obj;
lean_object* v_res_1068_;
v_res_1068_ = l_Lake_SpawnM_toFn___redArg(v_self_1059_, v_fetch_1060_, v_pkg_x3f_1061_, v_stack_1062_, v_store_1063_, v_ctx_1064_, v_s_1065_);
stack->m_obj
 = v_res_1068_;
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg___boxed(lean_object* v_self_1069_, lean_object* v_fetch_1070_, lean_object* v_pkg_x3f_1071_, lean_object* v_stack_1072_, lean_object* v_store_1073_, lean_object* v_ctx_1074_, lean_object* v_s_1075_, lean_object* v_a_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lake_SpawnM_toFn___redArg(v_self_1069_, v_fetch_1070_, v_pkg_x3f_1071_, v_stack_1072_, v_store_1073_, v_ctx_1074_, v_s_1075_);
return v_res_1077_;
}
}
lean_object* l_Lake_SpawnM_toFn(lean_object* v_00_u03b1_1078_, lean_object* v_self_1079_, lean_object* v_fetch_1080_, lean_object* v_pkg_x3f_1081_, lean_object* v_stack_1082_, lean_object* v_store_1083_, lean_object* v_ctx_1084_, lean_object* v_s_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_apply_7(v_self_1079_, v_fetch_1080_, v_pkg_x3f_1081_, v_stack_1082_, v_store_1083_, v_ctx_1084_, v_s_1085_, lean_box(0));
return v___x_1087_;
}
}
LEAN_EXPORT void l_Lake_SpawnM_toFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1079_ = stack[1].m_obj;
lean_object* v_fetch_1080_ = stack[2].m_obj;
lean_object* v_pkg_x3f_1081_ = stack[3].m_obj;
lean_object* v_stack_1082_ = stack[4].m_obj;
lean_object* v_store_1083_ = stack[5].m_obj;
lean_object* v_ctx_1084_ = stack[6].m_obj;
lean_object* v_s_1085_ = stack[7].m_obj;
lean_object* v_res_1088_;
v_res_1088_ = l_Lake_SpawnM_toFn(lean_box(0), v_self_1079_, v_fetch_1080_, v_pkg_x3f_1081_, v_stack_1082_, v_store_1083_, v_ctx_1084_, v_s_1085_);
stack->m_obj
 = v_res_1088_;
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___boxed(lean_object* v_00_u03b1_1089_, lean_object* v_self_1090_, lean_object* v_fetch_1091_, lean_object* v_pkg_x3f_1092_, lean_object* v_stack_1093_, lean_object* v_store_1094_, lean_object* v_ctx_1095_, lean_object* v_s_1096_, lean_object* v_a_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Lake_SpawnM_toFn(v_00_u03b1_1089_, v_self_1090_, v_fetch_1091_, v_pkg_x3f_1092_, v_stack_1093_, v_store_1094_, v_ctx_1095_, v_s_1096_);
return v_res_1098_;
}
}
lean_object* l_Lake_JobM_runSpawnM___redArg(lean_object* v_x_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v_trace_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_trace_1107_ = lean_ctor_get(v_a_1105_, 1);
lean_inc_ref(v_trace_1107_);
lean_inc_ref(v_a_1104_);
lean_inc(v_a_1103_);
lean_inc(v_a_1102_);
lean_inc(v_a_1101_);
v___x_1108_ = lean_apply_7(v_x_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_trace_1107_, lean_box(0));
v___x_1109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
lean_ctor_set(v___x_1109_, 1, v_a_1105_);
return v___x_1109_;
}
}
LEAN_EXPORT void l_Lake_JobM_runSpawnM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1099_ = stack[0].m_obj;
lean_object* v_a_1100_ = stack[1].m_obj;
lean_object* v_a_1101_ = stack[2].m_obj;
lean_object* v_a_1102_ = stack[3].m_obj;
lean_object* v_a_1103_ = stack[4].m_obj;
lean_object* v_a_1104_ = stack[5].m_obj;
lean_object* v_a_1105_ = stack[6].m_obj;
lean_object* v_res_1110_;
v_res_1110_ = l_Lake_JobM_runSpawnM___redArg(v_x_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
stack->m_obj
 = v_res_1110_;
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg___boxed(lean_object* v_x_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Lake_JobM_runSpawnM___redArg(v_x_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_);
lean_dec_ref(v_a_1116_);
lean_dec(v_a_1115_);
lean_dec(v_a_1114_);
lean_dec(v_a_1113_);
return v_res_1119_;
}
}
lean_object* l_Lake_JobM_runSpawnM(lean_object* v_00_u03b1_1120_, lean_object* v_x_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v_trace_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v_trace_1129_ = lean_ctor_get(v_a_1127_, 1);
lean_inc_ref(v_trace_1129_);
lean_inc_ref(v_a_1126_);
lean_inc(v_a_1125_);
lean_inc(v_a_1124_);
lean_inc(v_a_1123_);
v___x_1130_ = lean_apply_7(v_x_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_trace_1129_, lean_box(0));
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
lean_ctor_set(v___x_1131_, 1, v_a_1127_);
return v___x_1131_;
}
}
LEAN_EXPORT void l_Lake_JobM_runSpawnM_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1121_ = stack[1].m_obj;
lean_object* v_a_1122_ = stack[2].m_obj;
lean_object* v_a_1123_ = stack[3].m_obj;
lean_object* v_a_1124_ = stack[4].m_obj;
lean_object* v_a_1125_ = stack[5].m_obj;
lean_object* v_a_1126_ = stack[6].m_obj;
lean_object* v_a_1127_ = stack[7].m_obj;
lean_object* v_res_1132_;
v_res_1132_ = l_Lake_JobM_runSpawnM(lean_box(0), v_x_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_);
stack->m_obj
 = v_res_1132_;
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___boxed(lean_object* v_00_u03b1_1133_, lean_object* v_x_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lake_JobM_runSpawnM(v_00_u03b1_1133_, v_x_1134_, v_a_1135_, v_a_1136_, v_a_1137_, v_a_1138_, v_a_1139_, v_a_1140_);
lean_dec_ref(v_a_1139_);
lean_dec(v_a_1138_);
lean_dec(v_a_1137_);
lean_dec(v_a_1136_);
return v_res_1142_;
}
}
lean_object* l_Lake_FetchM_runJobM___redArg(lean_object* v_x_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v___x_1153_; uint8_t v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1153_ = 0;
v___x_1154_ = 0;
v___x_1155_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1156_ = lean_unsigned_to_nat(0u);
v___x_1157_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1157_, 0, v_a_1151_);
lean_ctor_set(v___x_1157_, 1, v___x_1155_);
lean_ctor_set(v___x_1157_, 2, v___x_1156_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3, v___x_1153_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3 + 1, v___x_1154_);
lean_ctor_set_uint8(v___x_1157_, sizeof(void*)*3 + 2, v___x_1154_);
lean_inc_ref(v_a_1150_);
lean_inc(v_a_1149_);
lean_inc(v_a_1148_);
lean_inc(v_a_1147_);
v___x_1158_ = lean_apply_7(v_x_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v___x_1157_, lean_box(0));
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1168_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 1);
v_a_1160_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1162_ = v___x_1158_;
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1159_);
lean_inc(v_a_1160_);
lean_dec(v___x_1158_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1168_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v_log_1164_; lean_object* v___x_1166_; 
v_log_1164_ = lean_ctor_get(v_a_1159_, 0);
lean_inc_ref(v_log_1164_);
lean_dec(v_a_1159_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v_log_1164_);
v___x_1166_ = v___x_1162_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1160_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_log_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1178_; 
v_a_1169_ = lean_ctor_get(v___x_1158_, 1);
v_a_1170_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1172_ = v___x_1158_;
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1169_);
lean_inc(v_a_1170_);
lean_dec(v___x_1158_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1178_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v_log_1174_; lean_object* v___x_1176_; 
v_log_1174_ = lean_ctor_get(v_a_1169_, 0);
lean_inc_ref(v_log_1174_);
lean_dec(v_a_1169_);
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 1, v_log_1174_);
v___x_1176_ = v___x_1172_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1170_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_log_1174_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_FetchM_runJobM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1145_ = stack[0].m_obj;
lean_object* v_a_1146_ = stack[1].m_obj;
lean_object* v_a_1147_ = stack[2].m_obj;
lean_object* v_a_1148_ = stack[3].m_obj;
lean_object* v_a_1149_ = stack[4].m_obj;
lean_object* v_a_1150_ = stack[5].m_obj;
lean_object* v_a_1151_ = stack[6].m_obj;
lean_object* v_res_1179_;
v_res_1179_ = l_Lake_FetchM_runJobM___redArg(v_x_1145_, v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_);
stack->m_obj
 = v_res_1179_;
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg___boxed(lean_object* v_x_1180_, lean_object* v_a_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_Lake_FetchM_runJobM___redArg(v_x_1180_, v_a_1181_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec(v_a_1183_);
lean_dec(v_a_1182_);
return v_res_1188_;
}
}
lean_object* l_Lake_FetchM_runJobM(lean_object* v_00_u03b1_1189_, lean_object* v_x_1190_, lean_object* v_a_1191_, lean_object* v_a_1192_, lean_object* v_a_1193_, lean_object* v_a_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_){
_start:
{
uint8_t v___x_1198_; uint8_t v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1198_ = 0;
v___x_1199_ = 0;
v___x_1200_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1201_ = lean_unsigned_to_nat(0u);
v___x_1202_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1202_, 0, v_a_1196_);
lean_ctor_set(v___x_1202_, 1, v___x_1200_);
lean_ctor_set(v___x_1202_, 2, v___x_1201_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*3, v___x_1198_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*3 + 1, v___x_1199_);
lean_ctor_set_uint8(v___x_1202_, sizeof(void*)*3 + 2, v___x_1199_);
lean_inc_ref(v_a_1195_);
lean_inc(v_a_1194_);
lean_inc(v_a_1193_);
lean_inc(v_a_1192_);
v___x_1203_ = lean_apply_7(v_x_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v___x_1202_, lean_box(0));
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1213_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 1);
v_a_1205_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1207_ = v___x_1203_;
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1204_);
lean_inc(v_a_1205_);
lean_dec(v___x_1203_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v_log_1209_; lean_object* v___x_1211_; 
v_log_1209_ = lean_ctor_get(v_a_1204_, 0);
lean_inc_ref(v_log_1209_);
lean_dec(v_a_1204_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v_log_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1205_);
lean_ctor_set(v_reuseFailAlloc_1212_, 1, v_log_1209_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_object* v_a_1214_; lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1223_; 
v_a_1214_ = lean_ctor_get(v___x_1203_, 1);
v_a_1215_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1217_ = v___x_1203_;
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1214_);
lean_inc(v_a_1215_);
lean_dec(v___x_1203_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1223_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v_log_1219_; lean_object* v___x_1221_; 
v_log_1219_ = lean_ctor_get(v_a_1214_, 0);
lean_inc_ref(v_log_1219_);
lean_dec(v_a_1214_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 1, v_log_1219_);
v___x_1221_ = v___x_1217_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_a_1215_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_log_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_FetchM_runJobM_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1190_ = stack[1].m_obj;
lean_object* v_a_1191_ = stack[2].m_obj;
lean_object* v_a_1192_ = stack[3].m_obj;
lean_object* v_a_1193_ = stack[4].m_obj;
lean_object* v_a_1194_ = stack[5].m_obj;
lean_object* v_a_1195_ = stack[6].m_obj;
lean_object* v_a_1196_ = stack[7].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l_Lake_FetchM_runJobM(lean_box(0), v_x_1190_, v_a_1191_, v_a_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_x_1226_, lean_object* v_a_1227_, lean_object* v_a_1228_, lean_object* v_a_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l_Lake_FetchM_runJobM(v_00_u03b1_1225_, v_x_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_, v_a_1231_, v_a_1232_);
lean_dec_ref(v_a_1231_);
lean_dec(v_a_1230_);
lean_dec(v_a_1229_);
lean_dec(v_a_1228_);
return v_res_1234_;
}
}
lean_object* l_Lake_JobM_runFetchM___redArg(lean_object* v_x_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_log_1245_; uint8_t v_action_1246_; uint8_t v_wantsRebuild_1247_; uint8_t v_canceled_1248_; lean_object* v_trace_1249_; lean_object* v_buildTime_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1279_; 
v_log_1245_ = lean_ctor_get(v_a_1243_, 0);
v_action_1246_ = lean_ctor_get_uint8(v_a_1243_, sizeof(void*)*3);
v_wantsRebuild_1247_ = lean_ctor_get_uint8(v_a_1243_, sizeof(void*)*3 + 1);
v_canceled_1248_ = lean_ctor_get_uint8(v_a_1243_, sizeof(void*)*3 + 2);
v_trace_1249_ = lean_ctor_get(v_a_1243_, 1);
v_buildTime_1250_ = lean_ctor_get(v_a_1243_, 2);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_a_1243_);
if (v_isSharedCheck_1279_ == 0)
{
v___x_1252_ = v_a_1243_;
v_isShared_1253_ = v_isSharedCheck_1279_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_buildTime_1250_);
lean_inc(v_trace_1249_);
lean_inc(v_log_1245_);
lean_dec(v_a_1243_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1279_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1254_; 
lean_inc_ref(v_a_1242_);
lean_inc(v_a_1241_);
lean_inc(v_a_1240_);
lean_inc(v_a_1239_);
v___x_1254_ = lean_apply_7(v_x_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_log_1245_, lean_box(0));
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_a_1255_; lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1266_; 
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_a_1256_ = lean_ctor_get(v___x_1254_, 1);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1258_ = v___x_1254_;
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1266_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v_a_1256_);
v___x_1261_ = v___x_1252_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1256_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v_trace_1249_);
lean_ctor_set(v_reuseFailAlloc_1265_, 2, v_buildTime_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*3, v_action_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*3 + 1, v_wantsRebuild_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1265_, sizeof(void*)*3 + 2, v_canceled_1248_);
v___x_1261_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1263_; 
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1261_);
v___x_1263_ = v___x_1258_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_a_1255_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v___x_1261_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
else
{
lean_object* v_a_1267_; lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1278_; 
v_a_1267_ = lean_ctor_get(v___x_1254_, 0);
v_a_1268_ = lean_ctor_get(v___x_1254_, 1);
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1278_ == 0)
{
v___x_1270_ = v___x_1254_;
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_inc(v_a_1267_);
lean_dec(v___x_1254_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1278_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1253_ == 0)
{
lean_ctor_set(v___x_1252_, 0, v_a_1268_);
v___x_1273_ = v___x_1252_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v_a_1268_);
lean_ctor_set(v_reuseFailAlloc_1277_, 1, v_trace_1249_);
lean_ctor_set(v_reuseFailAlloc_1277_, 2, v_buildTime_1250_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*3, v_action_1246_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*3 + 1, v_wantsRebuild_1247_);
lean_ctor_set_uint8(v_reuseFailAlloc_1277_, sizeof(void*)*3 + 2, v_canceled_1248_);
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
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 2, 0);
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
}
}
}
LEAN_EXPORT void l_Lake_JobM_runFetchM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1237_ = stack[0].m_obj;
lean_object* v_a_1238_ = stack[1].m_obj;
lean_object* v_a_1239_ = stack[2].m_obj;
lean_object* v_a_1240_ = stack[3].m_obj;
lean_object* v_a_1241_ = stack[4].m_obj;
lean_object* v_a_1242_ = stack[5].m_obj;
lean_object* v_a_1243_ = stack[6].m_obj;
lean_object* v_res_1280_;
v_res_1280_ = l_Lake_JobM_runFetchM___redArg(v_x_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_, v_a_1243_);
stack->m_obj
 = v_res_1280_;
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg___boxed(lean_object* v_x_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lake_JobM_runFetchM___redArg(v_x_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec(v_a_1284_);
lean_dec(v_a_1283_);
return v_res_1289_;
}
}
lean_object* l_Lake_JobM_runFetchM(lean_object* v_00_u03b1_1290_, lean_object* v_x_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_){
_start:
{
lean_object* v_log_1299_; uint8_t v_action_1300_; uint8_t v_wantsRebuild_1301_; uint8_t v_canceled_1302_; lean_object* v_trace_1303_; lean_object* v_buildTime_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1333_; 
v_log_1299_ = lean_ctor_get(v_a_1297_, 0);
v_action_1300_ = lean_ctor_get_uint8(v_a_1297_, sizeof(void*)*3);
v_wantsRebuild_1301_ = lean_ctor_get_uint8(v_a_1297_, sizeof(void*)*3 + 1);
v_canceled_1302_ = lean_ctor_get_uint8(v_a_1297_, sizeof(void*)*3 + 2);
v_trace_1303_ = lean_ctor_get(v_a_1297_, 1);
v_buildTime_1304_ = lean_ctor_get(v_a_1297_, 2);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_a_1297_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1306_ = v_a_1297_;
v_isShared_1307_ = v_isSharedCheck_1333_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_buildTime_1304_);
lean_inc(v_trace_1303_);
lean_inc(v_log_1299_);
lean_dec(v_a_1297_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1333_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1308_; 
lean_inc_ref(v_a_1296_);
lean_inc(v_a_1295_);
lean_inc(v_a_1294_);
lean_inc(v_a_1293_);
v___x_1308_ = lean_apply_7(v_x_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_log_1299_, lean_box(0));
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1320_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_a_1310_ = lean_ctor_get(v___x_1308_, 1);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1312_ = v___x_1308_;
v_isShared_1313_ = v_isSharedCheck_1320_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1320_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v_a_1310_);
v___x_1315_ = v___x_1306_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1310_);
lean_ctor_set(v_reuseFailAlloc_1319_, 1, v_trace_1303_);
lean_ctor_set(v_reuseFailAlloc_1319_, 2, v_buildTime_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*3, v_action_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*3 + 1, v_wantsRebuild_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1319_, sizeof(void*)*3 + 2, v_canceled_1302_);
v___x_1315_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
lean_object* v___x_1317_; 
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___x_1315_);
v___x_1317_ = v___x_1312_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1309_);
lean_ctor_set(v_reuseFailAlloc_1318_, 1, v___x_1315_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v_a_1321_; lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1332_; 
v_a_1321_ = lean_ctor_get(v___x_1308_, 0);
v_a_1322_ = lean_ctor_get(v___x_1308_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1324_ = v___x_1308_;
v_isShared_1325_ = v_isSharedCheck_1332_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_inc(v_a_1321_);
lean_dec(v___x_1308_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1332_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1307_ == 0)
{
lean_ctor_set(v___x_1306_, 0, v_a_1322_);
v___x_1327_ = v___x_1306_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1322_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_trace_1303_);
lean_ctor_set(v_reuseFailAlloc_1331_, 2, v_buildTime_1304_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*3, v_action_1300_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*3 + 1, v_wantsRebuild_1301_);
lean_ctor_set_uint8(v_reuseFailAlloc_1331_, sizeof(void*)*3 + 2, v_canceled_1302_);
v___x_1327_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1329_; 
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1327_);
v___x_1329_ = v___x_1324_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1321_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v___x_1327_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_JobM_runFetchM_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1291_ = stack[1].m_obj;
lean_object* v_a_1292_ = stack[2].m_obj;
lean_object* v_a_1293_ = stack[3].m_obj;
lean_object* v_a_1294_ = stack[4].m_obj;
lean_object* v_a_1295_ = stack[5].m_obj;
lean_object* v_a_1296_ = stack[6].m_obj;
lean_object* v_a_1297_ = stack[7].m_obj;
lean_object* v_res_1334_;
v_res_1334_ = l_Lake_JobM_runFetchM(lean_box(0), v_x_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
stack->m_obj
 = v_res_1334_;
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___boxed(lean_object* v_00_u03b1_1335_, lean_object* v_x_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lake_JobM_runFetchM(v_00_u03b1_1335_, v_x_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_, v_a_1341_, v_a_1342_);
lean_dec_ref(v_a_1341_);
lean_dec(v_a_1340_);
lean_dec(v_a_1339_);
lean_dec(v_a_1338_);
return v_res_1344_;
}
}
lean_object* l_Lake_Job_bindTask___redArg___lam__0(lean_object* v_inst_1347_, lean_object* v_caption_1348_, uint8_t v_optional_1349_, lean_object* v_toPure_1350_, lean_object* v_____do__lift_1351_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1352_, 0, v_____do__lift_1351_);
lean_ctor_set(v___x_1352_, 1, v_inst_1347_);
lean_ctor_set(v___x_1352_, 2, v_caption_1348_);
lean_ctor_set_uint8(v___x_1352_, sizeof(void*)*3, v_optional_1349_);
v___x_1353_ = lean_apply_2(v_toPure_1350_, lean_box(0), v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT void l_Lake_Job_bindTask___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1347_ = stack[0].m_obj;
lean_object* v_caption_1348_ = stack[1].m_obj;
uint8_t v_optional_1349_ = stack[2].m_num;
lean_object* v_toPure_1350_ = stack[3].m_obj;
lean_object* v_____do__lift_1351_ = stack[4].m_obj;
lean_object* v_res_1354_;
v_res_1354_ = l_Lake_Job_bindTask___redArg___lam__0(v_inst_1347_, v_caption_1348_, v_optional_1349_, v_toPure_1350_, v_____do__lift_1351_);
stack->m_obj
 = v_res_1354_;
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0___boxed(lean_object* v_inst_1355_, lean_object* v_caption_1356_, lean_object* v_optional_1357_, lean_object* v_toPure_1358_, lean_object* v_____do__lift_1359_){
_start:
{
uint8_t v_optional_boxed_1360_; lean_object* v_res_1361_; 
v_optional_boxed_1360_ = lean_unbox(v_optional_1357_);
v_res_1361_ = l_Lake_Job_bindTask___redArg___lam__0(v_inst_1355_, v_caption_1356_, v_optional_boxed_1360_, v_toPure_1358_, v_____do__lift_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg(lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_f_1364_, lean_object* v_self_1365_){
_start:
{
lean_object* v_toApplicative_1366_; lean_object* v_toBind_1367_; lean_object* v_task_1368_; lean_object* v_caption_1369_; uint8_t v_optional_1370_; lean_object* v_toPure_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___f_1374_; lean_object* v___x_1375_; 
v_toApplicative_1366_ = lean_ctor_get(v_inst_1362_, 0);
lean_inc_ref(v_toApplicative_1366_);
v_toBind_1367_ = lean_ctor_get(v_inst_1362_, 1);
lean_inc(v_toBind_1367_);
lean_dec_ref(v_inst_1362_);
v_task_1368_ = lean_ctor_get(v_self_1365_, 0);
lean_inc_ref(v_task_1368_);
v_caption_1369_ = lean_ctor_get(v_self_1365_, 2);
lean_inc_ref(v_caption_1369_);
v_optional_1370_ = lean_ctor_get_uint8(v_self_1365_, sizeof(void*)*3);
lean_dec_ref(v_self_1365_);
v_toPure_1371_ = lean_ctor_get(v_toApplicative_1366_, 1);
lean_inc(v_toPure_1371_);
lean_dec_ref(v_toApplicative_1366_);
v___x_1372_ = lean_apply_1(v_f_1364_, v_task_1368_);
v___x_1373_ = lean_box(v_optional_1370_);
v___f_1374_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1374_, 0, v_inst_1363_);
lean_closure_set(v___f_1374_, 1, v_caption_1369_);
lean_closure_set(v___f_1374_, 2, v___x_1373_);
lean_closure_set(v___f_1374_, 3, v_toPure_1371_);
v___x_1375_ = lean_apply_4(v_toBind_1367_, lean_box(0), lean_box(0), v___x_1372_, v___f_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask(lean_object* v_m_1376_, lean_object* v_00_u03b2_1377_, lean_object* v_00_u03b1_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_f_1381_, lean_object* v_self_1382_){
_start:
{
lean_object* v_toApplicative_1383_; lean_object* v_toBind_1384_; lean_object* v_task_1385_; lean_object* v_caption_1386_; uint8_t v_optional_1387_; lean_object* v_toPure_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___f_1391_; lean_object* v___x_1392_; 
v_toApplicative_1383_ = lean_ctor_get(v_inst_1379_, 0);
lean_inc_ref(v_toApplicative_1383_);
v_toBind_1384_ = lean_ctor_get(v_inst_1379_, 1);
lean_inc(v_toBind_1384_);
lean_dec_ref(v_inst_1379_);
v_task_1385_ = lean_ctor_get(v_self_1382_, 0);
lean_inc_ref(v_task_1385_);
v_caption_1386_ = lean_ctor_get(v_self_1382_, 2);
lean_inc_ref(v_caption_1386_);
v_optional_1387_ = lean_ctor_get_uint8(v_self_1382_, sizeof(void*)*3);
lean_dec_ref(v_self_1382_);
v_toPure_1388_ = lean_ctor_get(v_toApplicative_1383_, 1);
lean_inc(v_toPure_1388_);
lean_dec_ref(v_toApplicative_1383_);
v___x_1389_ = lean_apply_1(v_f_1381_, v_task_1385_);
v___x_1390_ = lean_box(v_optional_1387_);
v___f_1391_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1391_, 0, v_inst_1380_);
lean_closure_set(v___f_1391_, 1, v_caption_1386_);
lean_closure_set(v___f_1391_, 2, v___x_1390_);
lean_closure_set(v___f_1391_, 3, v_toPure_1388_);
v___x_1392_ = lean_apply_4(v_toBind_1384_, lean_box(0), lean_box(0), v___x_1389_, v___f_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Job_sync_spec__0(lean_object* v_msg_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1395_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_1396_ = lean_panic_fn_borrowed(v___x_1395_, v_msg_1394_);
return v___x_1396_;
}
}
lean_object* l_Lake_Job_sync___redArg___lam__0(lean_object* v_val_1397_, lean_object* v_val_1398_, lean_object* v_a_x3f_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1402_ = lean_get_set_stdout(v_val_1397_);
lean_dec_ref(v___x_1402_);
v___x_1403_ = lean_box(0);
v___x_1404_ = lean_get_set_stderr(v_val_1398_);
lean_dec_ref(v___x_1404_);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v___y_1400_);
return v___x_1405_;
}
}
LEAN_EXPORT void l_Lake_Job_sync___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_1397_ = stack[0].m_obj;
lean_object* v_val_1398_ = stack[1].m_obj;
lean_object* v_a_x3f_1399_ = stack[2].m_obj;
lean_object* v___y_1400_ = stack[3].m_obj;
lean_object* v_res_1406_;
v_res_1406_ = l_Lake_Job_sync___redArg___lam__0(v_val_1397_, v_val_1398_, v_a_x3f_1399_, v___y_1400_);
stack->m_obj
 = v_res_1406_;
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0___boxed(lean_object* v_val_1407_, lean_object* v_val_1408_, lean_object* v_a_x3f_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lake_Job_sync___redArg___lam__0(v_val_1407_, v_val_1408_, v_a_x3f_1409_, v___y_1410_);
lean_dec(v_a_x3f_1409_);
return v_res_1412_;
}
}
lean_object* l_Lake_Job_sync___redArg___lam__1(lean_object* v_a_1413_, lean_object* v_____r_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v___x_1422_; 
v___x_1422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1422_, 0, v_a_1413_);
lean_ctor_set(v___x_1422_, 1, v___y_1420_);
return v___x_1422_;
}
}
LEAN_EXPORT void l_Lake_Job_sync___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1413_ = stack[0].m_obj;
lean_object* v_____r_1414_ = stack[1].m_obj;
lean_object* v___y_1415_ = stack[2].m_obj;
lean_object* v___y_1416_ = stack[3].m_obj;
lean_object* v___y_1417_ = stack[4].m_obj;
lean_object* v___y_1418_ = stack[5].m_obj;
lean_object* v___y_1419_ = stack[6].m_obj;
lean_object* v___y_1420_ = stack[7].m_obj;
lean_object* v_res_1423_;
v_res_1423_ = l_Lake_Job_sync___redArg___lam__1(v_a_1413_, v_____r_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
stack->m_obj
 = v_res_1423_;
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1___boxed(lean_object* v_a_1424_, lean_object* v_____r_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Lake_Job_sync___redArg___lam__1(v_a_1424_, v_____r_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1433_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__0(void){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = l_ByteArray_empty;
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v___x_1434_);
return v___x_1436_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__2(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1441_ = 0;
v___x_1442_ = 0;
v___x_1443_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1444_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1444_, 0, v___x_1443_);
lean_ctor_set(v___x_1444_, 1, v___x_1440_);
lean_ctor_set(v___x_1444_, 2, v___x_1439_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3, v___x_1442_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 1, v___x_1441_);
lean_ctor_set_uint8(v___x_1444_, sizeof(void*)*3 + 2, v___x_1441_);
return v___x_1444_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__7(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__6));
v___x_1450_ = lean_unsigned_to_nat(46u);
v___x_1451_ = lean_unsigned_to_nat(193u);
v___x_1452_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__5));
v___x_1453_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__4));
v___x_1454_ = l_mkPanicMessageWithDecl(v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_, v___x_1449_);
return v___x_1454_;
}
}
lean_object* l_Lake_Job_sync___redArg(lean_object* v_inst_1455_, lean_object* v_act_1456_, lean_object* v_caption_1457_, lean_object* v_a_1458_, lean_object* v_a_1459_, lean_object* v_a_1460_, lean_object* v_a_1461_, lean_object* v_a_1462_){
_start:
{
lean_object* v_val_1465_; lean_object* v_a_1470_; lean_object* v_a_1471_; lean_object* v___y_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1475_ = lean_unsigned_to_nat(0u);
v___x_1476_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1477_ = lean_st_mk_ref(v___x_1476_);
lean_inc(v___x_1477_);
v___x_1478_ = l_IO_FS_Stream_ofBuffer(v___x_1477_);
lean_inc_ref(v___x_1478_);
v___x_1479_ = lean_get_set_stdout(v___x_1478_);
v___x_1480_ = lean_get_set_stderr(v___x_1478_);
v___x_1481_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__2, &l_Lake_Job_sync___redArg___closed__2_once, _init_l_Lake_Job_sync___redArg___closed__2);
lean_inc_ref(v_a_1462_);
lean_inc(v_a_1461_);
lean_inc(v_a_1460_);
lean_inc(v_a_1459_);
lean_inc_ref(v_a_1458_);
v___x_1482_ = lean_apply_7(v_act_1456_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v___x_1481_, lean_box(0));
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v_a_1483_; lean_object* v_a_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v_a_1487_; lean_object* v_log_1488_; uint8_t v_action_1489_; uint8_t v_wantsRebuild_1490_; uint8_t v_canceled_1491_; lean_object* v_trace_1492_; lean_object* v_buildTime_1493_; lean_object* v___x_1494_; lean_object* v___y_1496_; lean_object* v_data_1521_; uint8_t v___x_1522_; 
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc_n(v_a_1483_, 2);
v_a_1484_ = lean_ctor_get(v___x_1482_, 1);
lean_inc(v_a_1484_);
lean_dec_ref_known(v___x_1482_, 2);
v___x_1485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1485_, 0, v_a_1483_);
v___x_1486_ = l_Lake_Job_sync___redArg___lam__0(v___x_1479_, v___x_1480_, v___x_1485_, v_a_1484_);
lean_dec_ref_known(v___x_1485_, 1);
v_a_1487_ = lean_ctor_get(v___x_1486_, 1);
lean_inc(v_a_1487_);
lean_dec_ref(v___x_1486_);
v_log_1488_ = lean_ctor_get(v_a_1487_, 0);
v_action_1489_ = lean_ctor_get_uint8(v_a_1487_, sizeof(void*)*3);
v_wantsRebuild_1490_ = lean_ctor_get_uint8(v_a_1487_, sizeof(void*)*3 + 1);
v_canceled_1491_ = lean_ctor_get_uint8(v_a_1487_, sizeof(void*)*3 + 2);
v_trace_1492_ = lean_ctor_get(v_a_1487_, 1);
v_buildTime_1493_ = lean_ctor_get(v_a_1487_, 2);
v___x_1494_ = lean_st_ref_get(v___x_1477_);
lean_dec(v___x_1477_);
v_data_1521_ = lean_ctor_get(v___x_1494_, 0);
lean_inc_ref(v_data_1521_);
lean_dec(v___x_1494_);
v___x_1522_ = lean_string_validate_utf8(v_data_1521_);
if (v___x_1522_ == 0)
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
lean_dec_ref(v_data_1521_);
v___x_1523_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1524_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1523_);
v___y_1496_ = v___x_1524_;
goto v___jp_1495_;
}
else
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_string_from_utf8_unchecked(v_data_1521_);
v___y_1496_ = v___x_1525_;
goto v___jp_1495_;
}
v___jp_1495_:
{
lean_object* v___x_1497_; uint8_t v___x_1498_; 
v___x_1497_ = lean_string_utf8_byte_size(v___y_1496_);
v___x_1498_ = lean_nat_dec_eq(v___x_1497_, v___x_1475_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1515_; 
lean_inc(v_buildTime_1493_);
lean_inc_ref(v_trace_1492_);
lean_inc_ref(v_log_1488_);
v_isSharedCheck_1515_ = !lean_is_exclusive(v_a_1487_);
if (v_isSharedCheck_1515_ == 0)
{
lean_object* v_unused_1516_; lean_object* v_unused_1517_; lean_object* v_unused_1518_; 
v_unused_1516_ = lean_ctor_get(v_a_1487_, 2);
lean_dec(v_unused_1516_);
v_unused_1517_ = lean_ctor_get(v_a_1487_, 1);
lean_dec(v_unused_1517_);
v_unused_1518_ = lean_ctor_get(v_a_1487_, 0);
lean_dec(v_unused_1518_);
v___x_1500_ = v_a_1487_;
v_isShared_1501_ = v_isSharedCheck_1515_;
goto v_resetjp_1499_;
}
else
{
lean_dec(v_a_1487_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1515_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1512_; 
v___x_1502_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1503_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1503_, 0, v___y_1496_);
lean_ctor_set(v___x_1503_, 1, v___x_1475_);
lean_ctor_set(v___x_1503_, 2, v___x_1497_);
v___x_1504_ = l_String_Slice_trimAscii(v___x_1503_);
v___x_1505_ = l_String_Slice_toString(v___x_1504_);
lean_dec_ref(v___x_1504_);
v___x_1506_ = lean_string_append(v___x_1502_, v___x_1505_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = 1;
v___x_1508_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1508_, 0, v___x_1506_);
lean_ctor_set_uint8(v___x_1508_, sizeof(void*)*1, v___x_1507_);
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_array_push(v_log_1488_, v___x_1508_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 0, v___x_1510_);
v___x_1512_ = v___x_1500_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1514_; 
v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1510_);
lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_trace_1492_);
lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_buildTime_1493_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*3, v_action_1489_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*3 + 1, v_wantsRebuild_1490_);
lean_ctor_set_uint8(v_reuseFailAlloc_1514_, sizeof(void*)*3 + 2, v_canceled_1491_);
v___x_1512_ = v_reuseFailAlloc_1514_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lake_Job_sync___redArg___lam__1(v_a_1483_, v___x_1509_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v___x_1512_);
lean_dec_ref(v_a_1458_);
v___y_1474_ = v___x_1513_;
goto v___jp_1473_;
}
}
}
else
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
lean_dec_ref(v___y_1496_);
v___x_1519_ = lean_box(0);
v___x_1520_ = l_Lake_Job_sync___redArg___lam__1(v_a_1483_, v___x_1519_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_, v_a_1487_);
lean_dec_ref(v_a_1458_);
v___y_1474_ = v___x_1520_;
goto v___jp_1473_;
}
}
}
else
{
lean_object* v_a_1526_; lean_object* v_a_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v_a_1530_; 
lean_dec(v___x_1477_);
lean_dec_ref(v_a_1458_);
v_a_1526_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1526_);
v_a_1527_ = lean_ctor_get(v___x_1482_, 1);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1482_, 2);
v___x_1528_ = lean_box(0);
v___x_1529_ = l_Lake_Job_sync___redArg___lam__0(v___x_1479_, v___x_1480_, v___x_1528_, v_a_1527_);
v_a_1530_ = lean_ctor_get(v___x_1529_, 1);
lean_inc(v_a_1530_);
lean_dec_ref(v___x_1529_);
v_a_1470_ = v_a_1526_;
v_a_1471_ = v_a_1530_;
goto v___jp_1469_;
}
v___jp_1464_:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = lean_task_pure(v_val_1465_);
v___x_1467_ = 0;
v___x_1468_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1468_, 0, v___x_1466_);
lean_ctor_set(v___x_1468_, 1, v_inst_1455_);
lean_ctor_set(v___x_1468_, 2, v_caption_1457_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*3, v___x_1467_);
return v___x_1468_;
}
v___jp_1469_:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_a_1470_);
lean_ctor_set(v___x_1472_, 1, v_a_1471_);
v_val_1465_ = v___x_1472_;
goto v___jp_1464_;
}
v___jp_1473_:
{
v_val_1465_ = v___y_1474_;
goto v___jp_1464_;
}
}
}
LEAN_EXPORT void l_Lake_Job_sync___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1455_ = stack[0].m_obj;
lean_object* v_act_1456_ = stack[1].m_obj;
lean_object* v_caption_1457_ = stack[2].m_obj;
lean_object* v_a_1458_ = stack[3].m_obj;
lean_object* v_a_1459_ = stack[4].m_obj;
lean_object* v_a_1460_ = stack[5].m_obj;
lean_object* v_a_1461_ = stack[6].m_obj;
lean_object* v_a_1462_ = stack[7].m_obj;
lean_object* v_res_1531_;
v_res_1531_ = l_Lake_Job_sync___redArg(v_inst_1455_, v_act_1456_, v_caption_1457_, v_a_1458_, v_a_1459_, v_a_1460_, v_a_1461_, v_a_1462_);
stack->m_obj
 = v_res_1531_;
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___boxed(lean_object* v_inst_1532_, lean_object* v_act_1533_, lean_object* v_caption_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lake_Job_sync___redArg(v_inst_1532_, v_act_1533_, v_caption_1534_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec(v_a_1537_);
lean_dec(v_a_1536_);
return v_res_1541_;
}
}
lean_object* l_Lake_Job_sync(lean_object* v_00_u03b1_1542_, lean_object* v_inst_1543_, lean_object* v_act_1544_, lean_object* v_caption_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l_Lake_Job_sync___redArg(v_inst_1543_, v_act_1544_, v_caption_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_);
return v___x_1553_;
}
}
LEAN_EXPORT void l_Lake_Job_sync_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1543_ = stack[1].m_obj;
lean_object* v_act_1544_ = stack[2].m_obj;
lean_object* v_caption_1545_ = stack[3].m_obj;
lean_object* v_a_1546_ = stack[4].m_obj;
lean_object* v_a_1547_ = stack[5].m_obj;
lean_object* v_a_1548_ = stack[6].m_obj;
lean_object* v_a_1549_ = stack[7].m_obj;
lean_object* v_a_1550_ = stack[8].m_obj;
lean_object* v_a_1551_ = stack[9].m_obj;
lean_object* v_res_1554_;
v_res_1554_ = l_Lake_Job_sync(lean_box(0), v_inst_1543_, v_act_1544_, v_caption_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_, v_a_1550_, v_a_1551_);
stack->m_obj
 = v_res_1554_;
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___boxed(lean_object* v_00_u03b1_1555_, lean_object* v_inst_1556_, lean_object* v_act_1557_, lean_object* v_caption_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lake_Job_sync(v_00_u03b1_1555_, v_inst_1556_, v_act_1557_, v_caption_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_);
lean_dec_ref(v_a_1564_);
lean_dec_ref(v_a_1563_);
lean_dec(v_a_1562_);
lean_dec(v_a_1561_);
lean_dec(v_a_1560_);
return v_res_1566_;
}
}
lean_object* l_Lake_Job_async___redArg___lam__1(lean_object* v___x_1567_, lean_object* v___x_1568_, uint8_t v___x_1569_, uint8_t v___x_1570_, lean_object* v___x_1571_, lean_object* v___x_1572_, lean_object* v_act_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_){
_start:
{
lean_object* v_a_1581_; lean_object* v_a_1582_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1584_ = lean_st_mk_ref(v___x_1567_);
lean_inc(v___x_1584_);
v___x_1585_ = l_IO_FS_Stream_ofBuffer(v___x_1584_);
lean_inc_ref(v___x_1585_);
v___x_1586_ = lean_get_set_stdout(v___x_1585_);
v___x_1587_ = lean_get_set_stderr(v___x_1585_);
lean_inc(v___x_1572_);
v___x_1588_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_1588_, 0, v___x_1568_);
lean_ctor_set(v___x_1588_, 1, v___x_1571_);
lean_ctor_set(v___x_1588_, 2, v___x_1572_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*3, v___x_1569_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*3 + 1, v___x_1570_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*3 + 2, v___x_1570_);
lean_inc_ref(v_a_1578_);
lean_inc(v_a_1577_);
lean_inc(v_a_1576_);
lean_inc(v_a_1575_);
v___x_1589_ = lean_apply_7(v_act_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v___x_1588_, lean_box(0));
if (lean_obj_tag(v___x_1589_) == 0)
{
lean_object* v_a_1590_; lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1637_; 
v_a_1590_ = lean_ctor_get(v___x_1589_, 0);
v_a_1591_ = lean_ctor_get(v___x_1589_, 1);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1589_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1593_ = v___x_1589_;
v_isShared_1594_ = v_isSharedCheck_1637_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_inc(v_a_1590_);
lean_dec(v___x_1589_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1637_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___y_1596_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v_a_1602_; lean_object* v_log_1603_; uint8_t v_action_1604_; uint8_t v_wantsRebuild_1605_; uint8_t v_canceled_1606_; lean_object* v_trace_1607_; lean_object* v_buildTime_1608_; lean_object* v___x_1609_; lean_object* v___y_1611_; lean_object* v_data_1632_; uint8_t v___x_1633_; 
lean_inc(v_a_1590_);
v___x_1600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1600_, 0, v_a_1590_);
v___x_1601_ = l_Lake_Job_sync___redArg___lam__0(v___x_1586_, v___x_1587_, v___x_1600_, v_a_1591_);
lean_dec_ref_known(v___x_1600_, 1);
v_a_1602_ = lean_ctor_get(v___x_1601_, 1);
lean_inc(v_a_1602_);
lean_dec_ref(v___x_1601_);
v_log_1603_ = lean_ctor_get(v_a_1602_, 0);
v_action_1604_ = lean_ctor_get_uint8(v_a_1602_, sizeof(void*)*3);
v_wantsRebuild_1605_ = lean_ctor_get_uint8(v_a_1602_, sizeof(void*)*3 + 1);
v_canceled_1606_ = lean_ctor_get_uint8(v_a_1602_, sizeof(void*)*3 + 2);
v_trace_1607_ = lean_ctor_get(v_a_1602_, 1);
v_buildTime_1608_ = lean_ctor_get(v_a_1602_, 2);
v___x_1609_ = lean_st_ref_get(v___x_1584_);
lean_dec(v___x_1584_);
v_data_1632_ = lean_ctor_get(v___x_1609_, 0);
lean_inc_ref(v_data_1632_);
lean_dec(v___x_1609_);
v___x_1633_ = lean_string_validate_utf8(v_data_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; lean_object* v___x_1635_; 
lean_dec_ref(v_data_1632_);
v___x_1634_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1635_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1634_);
v___y_1611_ = v___x_1635_;
goto v___jp_1610_;
}
else
{
lean_object* v___x_1636_; 
v___x_1636_ = lean_string_from_utf8_unchecked(v_data_1632_);
v___y_1611_ = v___x_1636_;
goto v___jp_1610_;
}
v___jp_1595_:
{
lean_object* v___x_1598_; 
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 1, v___y_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1590_);
lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___y_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
v___jp_1610_:
{
lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1612_ = lean_string_utf8_byte_size(v___y_1611_);
v___x_1613_ = lean_nat_dec_eq(v___x_1612_, v___x_1572_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1628_; 
lean_inc(v_buildTime_1608_);
lean_inc_ref(v_trace_1607_);
lean_inc_ref(v_log_1603_);
v_isSharedCheck_1628_ = !lean_is_exclusive(v_a_1602_);
if (v_isSharedCheck_1628_ == 0)
{
lean_object* v_unused_1629_; lean_object* v_unused_1630_; lean_object* v_unused_1631_; 
v_unused_1629_ = lean_ctor_get(v_a_1602_, 2);
lean_dec(v_unused_1629_);
v_unused_1630_ = lean_ctor_get(v_a_1602_, 1);
lean_dec(v_unused_1630_);
v_unused_1631_ = lean_ctor_get(v_a_1602_, 0);
lean_dec(v_unused_1631_);
v___x_1615_ = v_a_1602_;
v_isShared_1616_ = v_isSharedCheck_1628_;
goto v_resetjp_1614_;
}
else
{
lean_dec(v_a_1602_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1628_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1617_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1618_, 0, v___y_1611_);
lean_ctor_set(v___x_1618_, 1, v___x_1572_);
lean_ctor_set(v___x_1618_, 2, v___x_1612_);
v___x_1619_ = l_String_Slice_trimAscii(v___x_1618_);
v___x_1620_ = l_String_Slice_toString(v___x_1619_);
lean_dec_ref(v___x_1619_);
v___x_1621_ = lean_string_append(v___x_1617_, v___x_1620_);
lean_dec_ref(v___x_1620_);
v___x_1622_ = 1;
v___x_1623_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1623_, 0, v___x_1621_);
lean_ctor_set_uint8(v___x_1623_, sizeof(void*)*1, v___x_1622_);
v___x_1624_ = lean_array_push(v_log_1603_, v___x_1623_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1624_);
v___x_1626_ = v___x_1615_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1627_; 
v_reuseFailAlloc_1627_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_trace_1607_);
lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_buildTime_1608_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*3, v_action_1604_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*3 + 1, v_wantsRebuild_1605_);
lean_ctor_set_uint8(v_reuseFailAlloc_1627_, sizeof(void*)*3 + 2, v_canceled_1606_);
v___x_1626_ = v_reuseFailAlloc_1627_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
v___y_1596_ = v___x_1626_;
goto v___jp_1595_;
}
}
}
else
{
lean_dec_ref(v___y_1611_);
lean_dec(v___x_1572_);
v___y_1596_ = v_a_1602_;
goto v___jp_1595_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v_a_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v_a_1642_; 
lean_dec(v___x_1584_);
lean_dec(v___x_1572_);
v_a_1638_ = lean_ctor_get(v___x_1589_, 0);
lean_inc(v_a_1638_);
v_a_1639_ = lean_ctor_get(v___x_1589_, 1);
lean_inc(v_a_1639_);
lean_dec_ref_known(v___x_1589_, 2);
v___x_1640_ = lean_box(0);
v___x_1641_ = l_Lake_Job_sync___redArg___lam__0(v___x_1586_, v___x_1587_, v___x_1640_, v_a_1639_);
v_a_1642_ = lean_ctor_get(v___x_1641_, 1);
lean_inc(v_a_1642_);
lean_dec_ref(v___x_1641_);
v_a_1581_ = v_a_1638_;
v_a_1582_ = v_a_1642_;
goto v___jp_1580_;
}
v___jp_1580_:
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_a_1581_);
lean_ctor_set(v___x_1583_, 1, v_a_1582_);
return v___x_1583_;
}
}
}
LEAN_EXPORT void l_Lake_Job_async___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1567_ = stack[0].m_obj;
lean_object* v___x_1568_ = stack[1].m_obj;
uint8_t v___x_1569_ = stack[2].m_num;
uint8_t v___x_1570_ = stack[3].m_num;
lean_object* v___x_1571_ = stack[4].m_obj;
lean_object* v___x_1572_ = stack[5].m_obj;
lean_object* v_act_1573_ = stack[6].m_obj;
lean_object* v_a_1574_ = stack[7].m_obj;
lean_object* v_a_1575_ = stack[8].m_obj;
lean_object* v_a_1576_ = stack[9].m_obj;
lean_object* v_a_1577_ = stack[10].m_obj;
lean_object* v_a_1578_ = stack[11].m_obj;
lean_object* v_res_1643_;
v_res_1643_ = l_Lake_Job_async___redArg___lam__1(v___x_1567_, v___x_1568_, v___x_1569_, v___x_1570_, v___x_1571_, v___x_1572_, v_act_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_);
stack->m_obj
 = v_res_1643_;
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1___boxed(lean_object* v___x_1644_, lean_object* v___x_1645_, lean_object* v___x_1646_, lean_object* v___x_1647_, lean_object* v___x_1648_, lean_object* v___x_1649_, lean_object* v_act_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v___y_1656_){
_start:
{
uint8_t v___x_23069__boxed_1657_; uint8_t v___x_23070__boxed_1658_; lean_object* v_res_1659_; 
v___x_23069__boxed_1657_ = lean_unbox(v___x_1646_);
v___x_23070__boxed_1658_ = lean_unbox(v___x_1647_);
v_res_1659_ = l_Lake_Job_async___redArg___lam__1(v___x_1644_, v___x_1645_, v___x_23069__boxed_1657_, v___x_23070__boxed_1658_, v___x_1648_, v___x_1649_, v_act_1650_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec(v_a_1652_);
return v_res_1659_;
}
}
lean_object* l_Lake_Job_async___redArg(lean_object* v_inst_1660_, lean_object* v_act_1661_, lean_object* v_prio_1662_, lean_object* v_caption_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; uint8_t v___x_1674_; lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___f_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1670_ = lean_unsigned_to_nat(0u);
v___x_1671_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1672_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1673_ = 0;
v___x_1674_ = 0;
v___x_1675_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1676_ = lean_box(v___x_1673_);
v___x_1677_ = lean_box(v___x_1674_);
lean_inc_ref(v_a_1668_);
lean_inc(v_a_1667_);
lean_inc(v_a_1666_);
lean_inc(v_a_1665_);
v___f_1678_ = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__1___boxed), 13, 12);
lean_closure_set(v___f_1678_, 0, v___x_1671_);
lean_closure_set(v___f_1678_, 1, v___x_1672_);
lean_closure_set(v___f_1678_, 2, v___x_1676_);
lean_closure_set(v___f_1678_, 3, v___x_1677_);
lean_closure_set(v___f_1678_, 4, v___x_1675_);
lean_closure_set(v___f_1678_, 5, v___x_1670_);
lean_closure_set(v___f_1678_, 6, v_act_1661_);
lean_closure_set(v___f_1678_, 7, v_a_1664_);
lean_closure_set(v___f_1678_, 8, v_a_1665_);
lean_closure_set(v___f_1678_, 9, v_a_1666_);
lean_closure_set(v___f_1678_, 10, v_a_1667_);
lean_closure_set(v___f_1678_, 11, v_a_1668_);
v___x_1679_ = lean_io_as_task(v___f_1678_, v_prio_1662_);
v___x_1680_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1680_, 0, v___x_1679_);
lean_ctor_set(v___x_1680_, 1, v_inst_1660_);
lean_ctor_set(v___x_1680_, 2, v_caption_1663_);
lean_ctor_set_uint8(v___x_1680_, sizeof(void*)*3, v___x_1674_);
return v___x_1680_;
}
}
LEAN_EXPORT void l_Lake_Job_async___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1660_ = stack[0].m_obj;
lean_object* v_act_1661_ = stack[1].m_obj;
lean_object* v_prio_1662_ = stack[2].m_obj;
lean_object* v_caption_1663_ = stack[3].m_obj;
lean_object* v_a_1664_ = stack[4].m_obj;
lean_object* v_a_1665_ = stack[5].m_obj;
lean_object* v_a_1666_ = stack[6].m_obj;
lean_object* v_a_1667_ = stack[7].m_obj;
lean_object* v_a_1668_ = stack[8].m_obj;
lean_object* v_res_1681_;
v_res_1681_ = l_Lake_Job_async___redArg(v_inst_1660_, v_act_1661_, v_prio_1662_, v_caption_1663_, v_a_1664_, v_a_1665_, v_a_1666_, v_a_1667_, v_a_1668_);
stack->m_obj
 = v_res_1681_;
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___boxed(lean_object* v_inst_1682_, lean_object* v_act_1683_, lean_object* v_prio_1684_, lean_object* v_caption_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Lake_Job_async___redArg(v_inst_1682_, v_act_1683_, v_prio_1684_, v_caption_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_);
lean_dec_ref(v_a_1690_);
lean_dec(v_a_1689_);
lean_dec(v_a_1688_);
lean_dec(v_a_1687_);
return v_res_1692_;
}
}
lean_object* l_Lake_Job_async(lean_object* v_00_u03b1_1693_, lean_object* v_inst_1694_, lean_object* v_act_1695_, lean_object* v_prio_1696_, lean_object* v_caption_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_, lean_object* v_a_1701_, lean_object* v_a_1702_, lean_object* v_a_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lake_Job_async___redArg(v_inst_1694_, v_act_1695_, v_prio_1696_, v_caption_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_);
return v___x_1705_;
}
}
LEAN_EXPORT void l_Lake_Job_async_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1694_ = stack[1].m_obj;
lean_object* v_act_1695_ = stack[2].m_obj;
lean_object* v_prio_1696_ = stack[3].m_obj;
lean_object* v_caption_1697_ = stack[4].m_obj;
lean_object* v_a_1698_ = stack[5].m_obj;
lean_object* v_a_1699_ = stack[6].m_obj;
lean_object* v_a_1700_ = stack[7].m_obj;
lean_object* v_a_1701_ = stack[8].m_obj;
lean_object* v_a_1702_ = stack[9].m_obj;
lean_object* v_a_1703_ = stack[10].m_obj;
lean_object* v_res_1706_;
v_res_1706_ = l_Lake_Job_async(lean_box(0), v_inst_1694_, v_act_1695_, v_prio_1696_, v_caption_1697_, v_a_1698_, v_a_1699_, v_a_1700_, v_a_1701_, v_a_1702_, v_a_1703_);
stack->m_obj
 = v_res_1706_;
}
LEAN_EXPORT lean_object* l_Lake_Job_async___boxed(lean_object* v_00_u03b1_1707_, lean_object* v_inst_1708_, lean_object* v_act_1709_, lean_object* v_prio_1710_, lean_object* v_caption_1711_, lean_object* v_a_1712_, lean_object* v_a_1713_, lean_object* v_a_1714_, lean_object* v_a_1715_, lean_object* v_a_1716_, lean_object* v_a_1717_, lean_object* v_a_1718_){
_start:
{
lean_object* v_res_1719_; 
v_res_1719_ = l_Lake_Job_async(v_00_u03b1_1707_, v_inst_1708_, v_act_1709_, v_prio_1710_, v_caption_1711_, v_a_1712_, v_a_1713_, v_a_1714_, v_a_1715_, v_a_1716_, v_a_1717_);
lean_dec_ref(v_a_1717_);
lean_dec_ref(v_a_1716_);
lean_dec(v_a_1715_);
lean_dec(v_a_1714_);
lean_dec(v_a_1713_);
return v_res_1719_;
}
}
lean_object* l_Lake_Job_wait___redArg(lean_object* v_self_1720_){
_start:
{
lean_object* v_task_1722_; lean_object* v___x_1723_; 
v_task_1722_ = lean_ctor_get(v_self_1720_, 0);
lean_inc_ref(v_task_1722_);
lean_dec_ref(v_self_1720_);
v___x_1723_ = lean_io_wait(v_task_1722_);
return v___x_1723_;
}
}
LEAN_EXPORT void l_Lake_Job_wait___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1720_ = stack[0].m_obj;
lean_object* v_res_1724_;
v_res_1724_ = l_Lake_Job_wait___redArg(v_self_1720_);
stack->m_obj
 = v_res_1724_;
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg___boxed(lean_object* v_self_1725_, lean_object* v_a_1726_){
_start:
{
lean_object* v_res_1727_; 
v_res_1727_ = l_Lake_Job_wait___redArg(v_self_1725_);
return v_res_1727_;
}
}
lean_object* l_Lake_Job_wait(lean_object* v_00_u03b1_1728_, lean_object* v_self_1729_){
_start:
{
lean_object* v_task_1731_; lean_object* v___x_1732_; 
v_task_1731_ = lean_ctor_get(v_self_1729_, 0);
lean_inc_ref(v_task_1731_);
lean_dec_ref(v_self_1729_);
v___x_1732_ = lean_io_wait(v_task_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT void l_Lake_Job_wait_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1729_ = stack[1].m_obj;
lean_object* v_res_1733_;
v_res_1733_ = l_Lake_Job_wait(lean_box(0), v_self_1729_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_self_1735_, lean_object* v_a_1736_){
_start:
{
lean_object* v_res_1737_; 
v_res_1737_ = l_Lake_Job_wait(v_00_u03b1_1734_, v_self_1735_);
return v_res_1737_;
}
}
lean_object* l_Lake_Job_wait_x3f___redArg(lean_object* v_self_1738_){
_start:
{
lean_object* v_task_1740_; lean_object* v___x_1741_; 
v_task_1740_ = lean_ctor_get(v_self_1738_, 0);
lean_inc_ref(v_task_1740_);
lean_dec_ref(v_self_1738_);
v___x_1741_ = lean_io_wait(v_task_1740_);
if (lean_obj_tag(v___x_1741_) == 0)
{
lean_object* v_a_1742_; lean_object* v___x_1743_; 
v_a_1742_ = lean_ctor_get(v___x_1741_, 0);
lean_inc(v_a_1742_);
lean_dec_ref_known(v___x_1741_, 2);
v___x_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1743_, 0, v_a_1742_);
return v___x_1743_;
}
else
{
lean_object* v___x_1744_; 
lean_dec_ref_known(v___x_1741_, 2);
v___x_1744_ = lean_box(0);
return v___x_1744_;
}
}
}
LEAN_EXPORT void l_Lake_Job_wait_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1738_ = stack[0].m_obj;
lean_object* v_res_1745_;
v_res_1745_ = l_Lake_Job_wait_x3f___redArg(v_self_1738_);
stack->m_obj
 = v_res_1745_;
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg___boxed(lean_object* v_self_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lake_Job_wait_x3f___redArg(v_self_1746_);
return v_res_1748_;
}
}
lean_object* l_Lake_Job_wait_x3f(lean_object* v_00_u03b1_1749_, lean_object* v_self_1750_){
_start:
{
lean_object* v_task_1752_; lean_object* v___x_1753_; 
v_task_1752_ = lean_ctor_get(v_self_1750_, 0);
lean_inc_ref(v_task_1752_);
lean_dec_ref(v_self_1750_);
v___x_1753_ = lean_io_wait(v_task_1752_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v___x_1755_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 2);
v___x_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1755_, 0, v_a_1754_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; 
lean_dec_ref_known(v___x_1753_, 2);
v___x_1756_ = lean_box(0);
return v___x_1756_;
}
}
}
LEAN_EXPORT void l_Lake_Job_wait_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1750_ = stack[1].m_obj;
lean_object* v_res_1757_;
v_res_1757_ = l_Lake_Job_wait_x3f(lean_box(0), v_self_1750_);
stack->m_obj
 = v_res_1757_;
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_self_1759_, lean_object* v_a_1760_){
_start:
{
lean_object* v_res_1761_; 
v_res_1761_ = l_Lake_Job_wait_x3f(v_00_u03b1_1758_, v_self_1759_);
return v_res_1761_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(lean_object* v_as_1762_, size_t v_i_1763_, size_t v_stop_1764_, lean_object* v_b_1765_, lean_object* v___y_1766_){
_start:
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_usize_dec_eq(v_i_1763_, v_stop_1764_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; size_t v___x_1772_; size_t v___x_1773_; 
v___x_1769_ = lean_array_uget_borrowed(v_as_1762_, v_i_1763_);
v___x_1770_ = lean_box(0);
lean_inc(v___x_1769_);
v___x_1771_ = lean_array_push(v___y_1766_, v___x_1769_);
v___x_1772_ = ((size_t)1ULL);
v___x_1773_ = lean_usize_add(v_i_1763_, v___x_1772_);
v_i_1763_ = v___x_1773_;
v_b_1765_ = v___x_1770_;
v___y_1766_ = v___x_1771_;
goto _start;
}
else
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1775_, 0, v_b_1765_);
lean_ctor_set(v___x_1775_, 1, v___y_1766_);
return v___x_1775_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_1762_ = stack[0].m_obj;
size_t v_i_1763_ = stack[1].m_num;
size_t v_stop_1764_ = stack[2].m_num;
lean_object* v_b_1765_ = stack[3].m_obj;
lean_object* v___y_1766_ = stack[4].m_obj;
lean_object* v_res_1776_;
v_res_1776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_as_1762_, v_i_1763_, v_stop_1764_, v_b_1765_, v___y_1766_);
stack->m_obj
 = v_res_1776_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0___boxed(lean_object* v_as_1777_, lean_object* v_i_1778_, lean_object* v_stop_1779_, lean_object* v_b_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_){
_start:
{
size_t v_i_boxed_1783_; size_t v_stop_boxed_1784_; lean_object* v_res_1785_; 
v_i_boxed_1783_ = lean_unbox_usize(v_i_1778_);
lean_dec(v_i_1778_);
v_stop_boxed_1784_ = lean_unbox_usize(v_stop_1779_);
lean_dec(v_stop_1779_);
v_res_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_as_1777_, v_i_boxed_1783_, v_stop_boxed_1784_, v_b_1780_, v___y_1781_);
lean_dec_ref(v_as_1777_);
return v_res_1785_;
}
}
lean_object* l_Lake_Job_await___redArg(lean_object* v_self_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_task_1789_; lean_object* v___x_1790_; 
v_task_1789_ = lean_ctor_get(v_self_1786_, 0);
lean_inc_ref(v_task_1789_);
lean_dec_ref(v_self_1786_);
v___x_1790_ = lean_io_wait(v_task_1789_);
if (lean_obj_tag(v___x_1790_) == 0)
{
lean_object* v_a_1791_; lean_object* v_a_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1819_; 
v_a_1791_ = lean_ctor_get(v___x_1790_, 0);
v_a_1792_ = lean_ctor_get(v___x_1790_, 1);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1794_ = v___x_1790_;
v_isShared_1795_ = v_isSharedCheck_1819_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_a_1792_);
lean_inc(v_a_1791_);
lean_dec(v___x_1790_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1819_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_a_1797_; lean_object* v_log_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_log_1801_ = lean_ctor_get(v_a_1792_, 0);
lean_inc_ref(v_log_1801_);
lean_dec(v_a_1792_);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_array_get_size(v_log_1801_);
v___x_1804_ = lean_nat_dec_lt(v___x_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
lean_dec_ref(v_log_1801_);
v_a_1797_ = v_a_1787_;
goto v___jp_1796_;
}
else
{
lean_object* v___x_1805_; size_t v___x_1806_; size_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1805_ = lean_box(0);
v___x_1806_ = ((size_t)0ULL);
v___x_1807_ = lean_usize_of_nat(v___x_1803_);
v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1801_, v___x_1806_, v___x_1807_, v___x_1805_, v_a_1787_);
lean_dec_ref(v_log_1801_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 1);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 2);
v_a_1797_ = v_a_1809_;
goto v___jp_1796_;
}
else
{
lean_object* v_a_1810_; lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_del_object(v___x_1794_);
lean_dec(v_a_1791_);
v_a_1810_ = lean_ctor_get(v___x_1808_, 0);
v_a_1811_ = lean_ctor_get(v___x_1808_, 1);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1808_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_inc(v_a_1810_);
lean_dec(v___x_1808_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1810_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
v___jp_1796_:
{
lean_object* v___x_1799_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v_a_1797_);
v___x_1799_ = v___x_1794_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1800_; 
v_reuseFailAlloc_1800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1791_);
lean_ctor_set(v_reuseFailAlloc_1800_, 1, v_a_1797_);
v___x_1799_ = v_reuseFailAlloc_1800_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
return v___x_1799_;
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v_a_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1848_; 
v_a_1820_ = lean_ctor_get(v___x_1790_, 0);
v_a_1821_ = lean_ctor_get(v___x_1790_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1823_ = v___x_1790_;
v_isShared_1824_ = v_isSharedCheck_1848_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_a_1821_);
lean_inc(v_a_1820_);
lean_dec(v___x_1790_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1848_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_a_1826_; lean_object* v_log_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_log_1830_ = lean_ctor_get(v_a_1821_, 0);
lean_inc_ref(v_log_1830_);
lean_dec(v_a_1821_);
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = lean_array_get_size(v_log_1830_);
v___x_1833_ = lean_nat_dec_lt(v___x_1831_, v___x_1832_);
if (v___x_1833_ == 0)
{
lean_dec_ref(v_log_1830_);
v_a_1826_ = v_a_1787_;
goto v___jp_1825_;
}
else
{
lean_object* v___x_1834_; size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1834_ = lean_box(0);
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1832_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1830_, v___x_1835_, v___x_1836_, v___x_1834_, v_a_1787_);
lean_dec_ref(v_log_1830_);
if (lean_obj_tag(v___x_1837_) == 0)
{
lean_object* v_a_1838_; 
v_a_1838_ = lean_ctor_get(v___x_1837_, 1);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1837_, 2);
v_a_1826_ = v_a_1838_;
goto v___jp_1825_;
}
else
{
lean_object* v_a_1839_; lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_del_object(v___x_1823_);
lean_dec(v_a_1820_);
v_a_1839_ = lean_ctor_get(v___x_1837_, 0);
v_a_1840_ = lean_ctor_get(v___x_1837_, 1);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1837_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1837_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_inc(v_a_1839_);
lean_dec(v___x_1837_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1839_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_a_1840_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
v___jp_1825_:
{
lean_object* v___x_1828_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v_a_1826_);
v___x_1828_ = v___x_1823_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1820_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_a_1826_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lake_Job_await___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1786_ = stack[0].m_obj;
lean_object* v_a_1787_ = stack[1].m_obj;
lean_object* v_res_1849_;
v_res_1849_ = l_Lake_Job_await___redArg(v_self_1786_, v_a_1787_);
stack->m_obj
 = v_res_1849_;
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___boxed(lean_object* v_self_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lake_Job_await___redArg(v_self_1850_, v_a_1851_);
return v_res_1853_;
}
}
lean_object* l_Lake_Job_await(lean_object* v_00_u03b1_1854_, lean_object* v_self_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Lake_Job_await___redArg(v_self_1855_, v_a_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT void l_Lake_Job_await_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1855_ = stack[1].m_obj;
lean_object* v_a_1856_ = stack[2].m_obj;
lean_object* v_res_1859_;
v_res_1859_ = l_Lake_Job_await(lean_box(0), v_self_1855_, v_a_1856_);
stack->m_obj
 = v_res_1859_;
}
LEAN_EXPORT lean_object* l_Lake_Job_await___boxed(lean_object* v_00_u03b1_1860_, lean_object* v_self_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lake_Job_await(v_00_u03b1_1860_, v_self_1861_, v_a_1862_);
return v_res_1864_;
}
}
lean_object* l_Lake_Job_cancelJob___redArg(lean_object* v_a_1865_){
_start:
{
lean_object* v_log_1867_; uint8_t v_action_1868_; uint8_t v_wantsRebuild_1869_; lean_object* v_trace_1870_; lean_object* v_buildTime_1871_; lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1881_; 
v_log_1867_ = lean_ctor_get(v_a_1865_, 0);
v_action_1868_ = lean_ctor_get_uint8(v_a_1865_, sizeof(void*)*3);
v_wantsRebuild_1869_ = lean_ctor_get_uint8(v_a_1865_, sizeof(void*)*3 + 1);
v_trace_1870_ = lean_ctor_get(v_a_1865_, 1);
v_buildTime_1871_ = lean_ctor_get(v_a_1865_, 2);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_a_1865_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1873_ = v_a_1865_;
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
else
{
lean_inc(v_buildTime_1871_);
lean_inc(v_trace_1870_);
lean_inc(v_log_1867_);
lean_dec(v_a_1865_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1881_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
uint8_t v___x_1875_; lean_object* v___x_1877_; 
v___x_1875_ = 1;
lean_inc_ref(v_log_1867_);
if (v_isShared_1874_ == 0)
{
v___x_1877_ = v___x_1873_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_log_1867_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_trace_1870_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_buildTime_1871_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*3, v_action_1868_);
lean_ctor_set_uint8(v_reuseFailAlloc_1880_, sizeof(void*)*3 + 1, v_wantsRebuild_1869_);
v___x_1877_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
lean_ctor_set_uint8(v___x_1877_, sizeof(void*)*3 + 2, v___x_1875_);
v___x_1878_ = lean_array_get_size(v_log_1867_);
lean_dec_ref(v_log_1867_);
v___x_1879_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1879_, 0, v___x_1878_);
lean_ctor_set(v___x_1879_, 1, v___x_1877_);
return v___x_1879_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_cancelJob___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1865_ = stack[0].m_obj;
lean_object* v_res_1882_;
v_res_1882_ = l_Lake_Job_cancelJob___redArg(v_a_1865_);
stack->m_obj
 = v_res_1882_;
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___redArg___boxed(lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lake_Job_cancelJob___redArg(v_a_1883_);
return v_res_1885_;
}
}
lean_object* l_Lake_Job_cancelJob(lean_object* v_00_u03b1_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lake_Job_cancelJob___redArg(v_a_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT void l_Lake_Job_cancelJob_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1887_ = stack[1].m_obj;
lean_object* v_a_1888_ = stack[2].m_obj;
lean_object* v_a_1889_ = stack[3].m_obj;
lean_object* v_a_1890_ = stack[4].m_obj;
lean_object* v_a_1891_ = stack[5].m_obj;
lean_object* v_a_1892_ = stack[6].m_obj;
lean_object* v_res_1895_;
v_res_1895_ = l_Lake_Job_cancelJob(lean_box(0), v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
stack->m_obj
 = v_res_1895_;
}
LEAN_EXPORT lean_object* l_Lake_Job_cancelJob___boxed(lean_object* v_00_u03b1_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lake_Job_cancelJob(v_00_u03b1_1896_, v_a_1897_, v_a_1898_, v_a_1899_, v_a_1900_, v_a_1901_, v_a_1902_);
lean_dec_ref(v_a_1901_);
lean_dec(v_a_1900_);
lean_dec(v_a_1899_);
lean_dec(v_a_1898_);
lean_dec_ref(v_a_1897_);
return v_res_1904_;
}
}
lean_object* l_Lake_Job_waitUnlessCanceled_x3f___redArg(lean_object* v_self_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_task_1908_; lean_object* v___x_1909_; 
v_task_1908_ = lean_ctor_get(v_self_1905_, 0);
lean_inc_ref(v_task_1908_);
lean_dec_ref(v_self_1905_);
v___x_1909_ = lean_io_wait(v_task_1908_);
if (lean_obj_tag(v___x_1909_) == 0)
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1918_; 
v_a_1910_ = lean_ctor_get(v___x_1909_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1918_ == 0)
{
lean_object* v_unused_1919_; 
v_unused_1919_ = lean_ctor_get(v___x_1909_, 1);
lean_dec(v_unused_1919_);
v___x_1912_ = v___x_1909_;
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1909_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1918_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1914_; lean_object* v___x_1916_; 
v___x_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1914_, 0, v_a_1910_);
if (v_isShared_1913_ == 0)
{
lean_ctor_set(v___x_1912_, 1, v_a_1906_);
lean_ctor_set(v___x_1912_, 0, v___x_1914_);
v___x_1916_ = v___x_1912_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1914_);
lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_a_1906_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1930_; 
v_a_1920_ = lean_ctor_get(v___x_1909_, 1);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1909_);
if (v_isSharedCheck_1930_ == 0)
{
lean_object* v_unused_1931_; 
v_unused_1931_ = lean_ctor_get(v___x_1909_, 0);
lean_dec(v_unused_1931_);
v___x_1922_ = v___x_1909_;
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1909_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1930_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
uint8_t v_canceled_1924_; 
v_canceled_1924_ = lean_ctor_get_uint8(v_a_1920_, sizeof(void*)*3 + 2);
lean_dec(v_a_1920_);
if (v_canceled_1924_ == 0)
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = lean_box(0);
if (v_isShared_1923_ == 0)
{
lean_ctor_set_tag(v___x_1922_, 0);
lean_ctor_set(v___x_1922_, 1, v_a_1906_);
lean_ctor_set(v___x_1922_, 0, v___x_1925_);
v___x_1927_ = v___x_1922_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_a_1906_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
else
{
lean_object* v___x_1929_; 
lean_del_object(v___x_1922_);
v___x_1929_ = l_Lake_Job_cancelJob___redArg(v_a_1906_);
return v___x_1929_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Job_waitUnlessCanceled_x3f___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1905_ = stack[0].m_obj;
lean_object* v_a_1906_ = stack[1].m_obj;
lean_object* v_res_1932_;
v_res_1932_ = l_Lake_Job_waitUnlessCanceled_x3f___redArg(v_self_1905_, v_a_1906_);
stack->m_obj
 = v_res_1932_;
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___redArg___boxed(lean_object* v_self_1933_, lean_object* v_a_1934_, lean_object* v_a_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lake_Job_waitUnlessCanceled_x3f___redArg(v_self_1933_, v_a_1934_);
return v_res_1936_;
}
}
lean_object* l_Lake_Job_waitUnlessCanceled_x3f(lean_object* v_00_u03b1_1937_, lean_object* v_self_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = l_Lake_Job_waitUnlessCanceled_x3f___redArg(v_self_1938_, v_a_1944_);
return v___x_1946_;
}
}
LEAN_EXPORT void l_Lake_Job_waitUnlessCanceled_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_self_1938_ = stack[1].m_obj;
lean_object* v_a_1939_ = stack[2].m_obj;
lean_object* v_a_1940_ = stack[3].m_obj;
lean_object* v_a_1941_ = stack[4].m_obj;
lean_object* v_a_1942_ = stack[5].m_obj;
lean_object* v_a_1943_ = stack[6].m_obj;
lean_object* v_a_1944_ = stack[7].m_obj;
lean_object* v_res_1947_;
v_res_1947_ = l_Lake_Job_waitUnlessCanceled_x3f(lean_box(0), v_self_1938_, v_a_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
stack->m_obj
 = v_res_1947_;
}
LEAN_EXPORT lean_object* l_Lake_Job_waitUnlessCanceled_x3f___boxed(lean_object* v_00_u03b1_1948_, lean_object* v_self_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_, lean_object* v_a_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lake_Job_waitUnlessCanceled_x3f(v_00_u03b1_1948_, v_self_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_);
lean_dec_ref(v_a_1954_);
lean_dec(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec_ref(v_a_1950_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg(lean_object* v_s_1962_){
_start:
{
lean_object* v_log_1963_; uint8_t v_action_1964_; uint8_t v_wantsRebuild_1965_; lean_object* v_trace_1966_; lean_object* v_buildTime_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1979_; 
v_log_1963_ = lean_ctor_get(v_s_1962_, 0);
v_action_1964_ = lean_ctor_get_uint8(v_s_1962_, sizeof(void*)*3);
v_wantsRebuild_1965_ = lean_ctor_get_uint8(v_s_1962_, sizeof(void*)*3 + 1);
v_trace_1966_ = lean_ctor_get(v_s_1962_, 1);
v_buildTime_1967_ = lean_ctor_get(v_s_1962_, 2);
v_isSharedCheck_1979_ = !lean_is_exclusive(v_s_1962_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1969_ = v_s_1962_;
v_isShared_1970_ = v_isSharedCheck_1979_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_buildTime_1967_);
lean_inc(v_trace_1966_);
lean_inc(v_log_1963_);
lean_dec(v_s_1962_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1979_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; uint8_t v___x_1974_; lean_object* v___x_1976_; 
v___x_1971_ = lean_array_get_size(v_log_1963_);
v___x_1972_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_1973_ = lean_array_push(v_log_1963_, v___x_1972_);
v___x_1974_ = 1;
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1973_);
v___x_1976_ = v___x_1969_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1973_);
lean_ctor_set(v_reuseFailAlloc_1978_, 1, v_trace_1966_);
lean_ctor_set(v_reuseFailAlloc_1978_, 2, v_buildTime_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*3, v_action_1964_);
lean_ctor_set_uint8(v_reuseFailAlloc_1978_, sizeof(void*)*3 + 1, v_wantsRebuild_1965_);
v___x_1976_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
lean_object* v___x_1977_; 
lean_ctor_set_uint8(v___x_1976_, sizeof(void*)*3 + 2, v___x_1974_);
v___x_1977_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1971_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
return v___x_1977_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult(lean_object* v_00_u03b1_1980_, lean_object* v_s_1981_){
_start:
{
lean_object* v_log_1982_; uint8_t v_action_1983_; uint8_t v_wantsRebuild_1984_; lean_object* v_trace_1985_; lean_object* v_buildTime_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1998_; 
v_log_1982_ = lean_ctor_get(v_s_1981_, 0);
v_action_1983_ = lean_ctor_get_uint8(v_s_1981_, sizeof(void*)*3);
v_wantsRebuild_1984_ = lean_ctor_get_uint8(v_s_1981_, sizeof(void*)*3 + 1);
v_trace_1985_ = lean_ctor_get(v_s_1981_, 1);
v_buildTime_1986_ = lean_ctor_get(v_s_1981_, 2);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_s_1981_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1988_ = v_s_1981_;
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_buildTime_1986_);
lean_inc(v_trace_1985_);
lean_inc(v_log_1982_);
lean_dec(v_s_1981_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1998_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; lean_object* v___x_1995_; 
v___x_1990_ = lean_array_get_size(v_log_1982_);
v___x_1991_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_1992_ = lean_array_push(v_log_1982_, v___x_1991_);
v___x_1993_ = 1;
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_1992_);
v___x_1995_ = v___x_1988_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v___x_1992_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_trace_1985_);
lean_ctor_set(v_reuseFailAlloc_1997_, 2, v_buildTime_1986_);
lean_ctor_set_uint8(v_reuseFailAlloc_1997_, sizeof(void*)*3, v_action_1983_);
lean_ctor_set_uint8(v_reuseFailAlloc_1997_, sizeof(void*)*3 + 1, v_wantsRebuild_1984_);
v___x_1995_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___x_1996_; 
lean_ctor_set_uint8(v___x_1995_, sizeof(void*)*3 + 2, v___x_1993_);
v___x_1996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1990_);
lean_ctor_set(v___x_1996_, 1, v___x_1995_);
return v___x_1996_;
}
}
}
}
lean_object* l_Lake_Job_mapM___redArg___lam__1(lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_f_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_x_2006_){
_start:
{
lean_object* v_a_2009_; lean_object* v_a_2010_; lean_object* v___y_2013_; lean_object* v___y_2014_; lean_object* v___y_2017_; uint8_t v___y_2018_; lean_object* v___y_2019_; lean_object* v___y_2020_; lean_object* v___y_2021_; lean_object* v___y_2022_; uint8_t v___y_2023_; uint8_t v___y_2024_; lean_object* v___y_2025_; lean_object* v___y_2026_; 
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v_a_2038_; lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2108_; 
v_a_2038_ = lean_ctor_get(v_x_2006_, 0);
v_a_2039_ = lean_ctor_get(v_x_2006_, 1);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_x_2006_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2041_ = v_x_2006_;
v_isShared_2042_ = v_isSharedCheck_2108_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_inc(v_a_2038_);
lean_dec(v_x_2006_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2108_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v_cancelTk_x3f_2087_; 
v_cancelTk_x3f_2087_ = lean_ctor_get(v_a_1999_, 6);
if (lean_obj_tag(v_cancelTk_x3f_2087_) == 1)
{
lean_object* v_val_2088_; uint8_t v___x_2089_; 
v_val_2088_ = lean_ctor_get(v_cancelTk_x3f_2087_, 0);
v___x_2089_ = l_IO_CancelToken_isSet(v_val_2088_);
if (v___x_2089_ == 0)
{
lean_del_object(v___x_2041_);
goto v___jp_2043_;
}
else
{
lean_object* v_log_2090_; uint8_t v_action_2091_; uint8_t v_wantsRebuild_2092_; lean_object* v_trace_2093_; lean_object* v_buildTime_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_a_2038_);
lean_dec_ref(v_a_2002_);
lean_dec_ref(v_f_2001_);
v_log_2090_ = lean_ctor_get(v_a_2039_, 0);
v_action_2091_ = lean_ctor_get_uint8(v_a_2039_, sizeof(void*)*3);
v_wantsRebuild_2092_ = lean_ctor_get_uint8(v_a_2039_, sizeof(void*)*3 + 1);
v_trace_2093_ = lean_ctor_get(v_a_2039_, 1);
v_buildTime_2094_ = lean_ctor_get(v_a_2039_, 2);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_a_2039_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2096_ = v_a_2039_;
v_isShared_2097_ = v_isSharedCheck_2107_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_buildTime_2094_);
lean_inc(v_trace_2093_);
lean_inc(v_log_2090_);
lean_dec(v_a_2039_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2107_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2102_; 
v___x_2098_ = lean_array_get_size(v_log_2090_);
v___x_2099_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_2100_ = lean_array_push(v_log_2090_, v___x_2099_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2100_);
v___x_2102_ = v___x_2096_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2106_, 1, v_trace_2093_);
lean_ctor_set(v_reuseFailAlloc_2106_, 2, v_buildTime_2094_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*3, v_action_2091_);
lean_ctor_set_uint8(v_reuseFailAlloc_2106_, sizeof(void*)*3 + 1, v_wantsRebuild_2092_);
v___x_2102_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
lean_object* v___x_2104_; 
lean_ctor_set_uint8(v___x_2102_, sizeof(void*)*3 + 2, v___x_2089_);
if (v_isShared_2042_ == 0)
{
lean_ctor_set_tag(v___x_2041_, 1);
lean_ctor_set(v___x_2041_, 1, v___x_2102_);
lean_ctor_set(v___x_2041_, 0, v___x_2098_);
v___x_2104_ = v___x_2041_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2102_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
}
else
{
lean_del_object(v___x_2041_);
goto v___jp_2043_;
}
v___jp_2043_:
{
lean_object* v_log_2044_; uint8_t v_action_2045_; uint8_t v_wantsRebuild_2046_; uint8_t v_canceled_2047_; lean_object* v_trace_2048_; lean_object* v_buildTime_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2086_; 
v_log_2044_ = lean_ctor_get(v_a_2039_, 0);
v_action_2045_ = lean_ctor_get_uint8(v_a_2039_, sizeof(void*)*3);
v_wantsRebuild_2046_ = lean_ctor_get_uint8(v_a_2039_, sizeof(void*)*3 + 1);
v_canceled_2047_ = lean_ctor_get_uint8(v_a_2039_, sizeof(void*)*3 + 2);
v_trace_2048_ = lean_ctor_get(v_a_2039_, 1);
v_buildTime_2049_ = lean_ctor_get(v_a_2039_, 2);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_2039_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2051_ = v_a_2039_;
v_isShared_2052_ = v_isSharedCheck_2086_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_buildTime_2049_);
lean_inc(v_trace_2048_);
lean_inc(v_log_2044_);
lean_dec(v_a_2039_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2086_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v_trace_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; 
lean_inc_ref(v_a_2000_);
v_trace_2053_ = l_Lake_BuildTrace_mix(v_a_2000_, v_trace_2048_);
v___x_2054_ = lean_unsigned_to_nat(0u);
v___x_2055_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_2056_ = lean_st_mk_ref(v___x_2055_);
lean_inc(v___x_2056_);
v___x_2057_ = l_IO_FS_Stream_ofBuffer(v___x_2056_);
lean_inc_ref(v___x_2057_);
v___x_2058_ = lean_get_set_stdout(v___x_2057_);
v___x_2059_ = lean_get_set_stderr(v___x_2057_);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 1, v_trace_2053_);
v___x_2061_ = v___x_2051_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_log_2044_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v_trace_2053_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_buildTime_2049_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*3, v_action_2045_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*3 + 1, v_wantsRebuild_2046_);
lean_ctor_set_uint8(v_reuseFailAlloc_2085_, sizeof(void*)*3 + 2, v_canceled_2047_);
v___x_2061_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
lean_object* v___x_2062_; 
lean_inc_ref(v_a_1999_);
lean_inc(v_a_2005_);
lean_inc(v_a_2004_);
lean_inc(v_a_2003_);
v___x_2062_ = lean_apply_8(v_f_2001_, v_a_2038_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_a_1999_, v___x_2061_, lean_box(0));
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v_a_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v_a_2067_; lean_object* v_log_2068_; uint8_t v_action_2069_; uint8_t v_wantsRebuild_2070_; uint8_t v_canceled_2071_; lean_object* v_trace_2072_; lean_object* v_buildTime_2073_; lean_object* v___x_2074_; lean_object* v_data_2075_; uint8_t v___x_2076_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc_n(v_a_2063_, 2);
v_a_2064_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2062_, 2);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_a_2063_);
v___x_2066_ = l_Lake_Job_sync___redArg___lam__0(v___x_2058_, v___x_2059_, v___x_2065_, v_a_2064_);
lean_dec_ref_known(v___x_2065_, 1);
v_a_2067_ = lean_ctor_get(v___x_2066_, 1);
lean_inc(v_a_2067_);
lean_dec_ref(v___x_2066_);
v_log_2068_ = lean_ctor_get(v_a_2067_, 0);
lean_inc_ref(v_log_2068_);
v_action_2069_ = lean_ctor_get_uint8(v_a_2067_, sizeof(void*)*3);
v_wantsRebuild_2070_ = lean_ctor_get_uint8(v_a_2067_, sizeof(void*)*3 + 1);
v_canceled_2071_ = lean_ctor_get_uint8(v_a_2067_, sizeof(void*)*3 + 2);
v_trace_2072_ = lean_ctor_get(v_a_2067_, 1);
lean_inc_ref(v_trace_2072_);
v_buildTime_2073_ = lean_ctor_get(v_a_2067_, 2);
lean_inc(v_buildTime_2073_);
v___x_2074_ = lean_st_ref_get(v___x_2056_);
lean_dec(v___x_2056_);
v_data_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc_ref(v_data_2075_);
lean_dec(v___x_2074_);
v___x_2076_ = lean_string_validate_utf8(v_data_2075_);
if (v___x_2076_ == 0)
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec_ref(v_data_2075_);
v___x_2077_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2078_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2077_);
v___y_2017_ = v_trace_2072_;
v___y_2018_ = v_wantsRebuild_2070_;
v___y_2019_ = v___x_2054_;
v___y_2020_ = v_buildTime_2073_;
v___y_2021_ = v_a_2067_;
v___y_2022_ = v_a_2063_;
v___y_2023_ = v_canceled_2071_;
v___y_2024_ = v_action_2069_;
v___y_2025_ = v_log_2068_;
v___y_2026_ = v___x_2078_;
goto v___jp_2016_;
}
else
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_string_from_utf8_unchecked(v_data_2075_);
v___y_2017_ = v_trace_2072_;
v___y_2018_ = v_wantsRebuild_2070_;
v___y_2019_ = v___x_2054_;
v___y_2020_ = v_buildTime_2073_;
v___y_2021_ = v_a_2067_;
v___y_2022_ = v_a_2063_;
v___y_2023_ = v_canceled_2071_;
v___y_2024_ = v_action_2069_;
v___y_2025_ = v_log_2068_;
v___y_2026_ = v___x_2079_;
goto v___jp_2016_;
}
}
else
{
lean_object* v_a_2080_; lean_object* v_a_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v_a_2084_; 
lean_dec(v___x_2056_);
v_a_2080_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2080_);
v_a_2081_ = lean_ctor_get(v___x_2062_, 1);
lean_inc(v_a_2081_);
lean_dec_ref_known(v___x_2062_, 2);
v___x_2082_ = lean_box(0);
v___x_2083_ = l_Lake_Job_sync___redArg___lam__0(v___x_2058_, v___x_2059_, v___x_2082_, v_a_2081_);
v_a_2084_ = lean_ctor_get(v___x_2083_, 1);
lean_inc(v_a_2084_);
lean_dec_ref(v___x_2083_);
v_a_2009_ = v_a_2080_;
v_a_2010_ = v_a_2084_;
goto v___jp_2008_;
}
}
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v_a_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2117_; 
lean_dec_ref(v_a_2002_);
lean_dec_ref(v_f_2001_);
v_a_2109_ = lean_ctor_get(v_x_2006_, 0);
v_a_2110_ = lean_ctor_get(v_x_2006_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_x_2006_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2112_ = v_x_2006_;
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_a_2110_);
lean_inc(v_a_2109_);
lean_dec(v_x_2006_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2117_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2115_; 
if (v_isShared_2113_ == 0)
{
v___x_2115_ = v___x_2112_;
goto v_reusejp_2114_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_a_2109_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v_a_2110_);
v___x_2115_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2114_;
}
v_reusejp_2114_:
{
return v___x_2115_;
}
}
}
v___jp_2008_:
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2011_, 0, v_a_2009_);
lean_ctor_set(v___x_2011_, 1, v_a_2010_);
return v___x_2011_;
}
v___jp_2012_:
{
lean_object* v___x_2015_; 
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___y_2013_);
lean_ctor_set(v___x_2015_, 1, v___y_2014_);
return v___x_2015_;
}
v___jp_2016_:
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = lean_string_utf8_byte_size(v___y_2026_);
v___x_2028_ = lean_nat_dec_eq(v___x_2027_, v___y_2019_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
lean_dec_ref(v___y_2021_);
v___x_2029_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_2030_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2030_, 0, v___y_2026_);
lean_ctor_set(v___x_2030_, 1, v___y_2019_);
lean_ctor_set(v___x_2030_, 2, v___x_2027_);
v___x_2031_ = l_String_Slice_trimAscii(v___x_2030_);
v___x_2032_ = l_String_Slice_toString(v___x_2031_);
lean_dec_ref(v___x_2031_);
v___x_2033_ = lean_string_append(v___x_2029_, v___x_2032_);
lean_dec_ref(v___x_2032_);
v___x_2034_ = 1;
v___x_2035_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2035_, 0, v___x_2033_);
lean_ctor_set_uint8(v___x_2035_, sizeof(void*)*1, v___x_2034_);
v___x_2036_ = lean_array_push(v___y_2025_, v___x_2035_);
v___x_2037_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
lean_ctor_set(v___x_2037_, 1, v___y_2017_);
lean_ctor_set(v___x_2037_, 2, v___y_2020_);
lean_ctor_set_uint8(v___x_2037_, sizeof(void*)*3, v___y_2024_);
lean_ctor_set_uint8(v___x_2037_, sizeof(void*)*3 + 1, v___y_2018_);
lean_ctor_set_uint8(v___x_2037_, sizeof(void*)*3 + 2, v___y_2023_);
v___y_2013_ = v___y_2022_;
v___y_2014_ = v___x_2037_;
goto v___jp_2012_;
}
else
{
lean_dec_ref(v___y_2026_);
lean_dec_ref(v___y_2025_);
lean_dec(v___y_2020_);
lean_dec(v___y_2019_);
lean_dec_ref(v___y_2017_);
v___y_2013_ = v___y_2022_;
v___y_2014_ = v___y_2021_;
goto v___jp_2012_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_mapM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1999_ = stack[0].m_obj;
lean_object* v_a_2000_ = stack[1].m_obj;
lean_object* v_f_2001_ = stack[2].m_obj;
lean_object* v_a_2002_ = stack[3].m_obj;
lean_object* v_a_2003_ = stack[4].m_obj;
lean_object* v_a_2004_ = stack[5].m_obj;
lean_object* v_a_2005_ = stack[6].m_obj;
lean_object* v_x_2006_ = stack[7].m_obj;
lean_object* v_res_2118_;
v_res_2118_ = l_Lake_Job_mapM___redArg___lam__1(v_a_1999_, v_a_2000_, v_f_2001_, v_a_2002_, v_a_2003_, v_a_2004_, v_a_2005_, v_x_2006_);
stack->m_obj
 = v_res_2118_;
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1___boxed(lean_object* v_a_2119_, lean_object* v_a_2120_, lean_object* v_f_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_x_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lake_Job_mapM___redArg___lam__1(v_a_2119_, v_a_2120_, v_f_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_x_2126_);
lean_dec(v_a_2125_);
lean_dec(v_a_2124_);
lean_dec(v_a_2123_);
lean_dec_ref(v_a_2120_);
lean_dec_ref(v_a_2119_);
return v_res_2128_;
}
}
lean_object* l_Lake_Job_mapM___redArg(lean_object* v_kind_2129_, lean_object* v_self_2130_, lean_object* v_f_2131_, lean_object* v_prio_2132_, uint8_t v_sync_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_task_2141_; lean_object* v_caption_2142_; uint8_t v_optional_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2152_; 
v_task_2141_ = lean_ctor_get(v_self_2130_, 0);
v_caption_2142_ = lean_ctor_get(v_self_2130_, 2);
v_optional_2143_ = lean_ctor_get_uint8(v_self_2130_, sizeof(void*)*3);
v_isSharedCheck_2152_ = !lean_is_exclusive(v_self_2130_);
if (v_isSharedCheck_2152_ == 0)
{
lean_object* v_unused_2153_; 
v_unused_2153_ = lean_ctor_get(v_self_2130_, 1);
lean_dec(v_unused_2153_);
v___x_2145_ = v_self_2130_;
v_isShared_2146_ = v_isSharedCheck_2152_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_caption_2142_);
lean_inc(v_task_2141_);
lean_dec(v_self_2130_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2152_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___f_2147_; lean_object* v___x_2148_; lean_object* v___x_2150_; 
lean_inc(v_a_2137_);
lean_inc(v_a_2136_);
lean_inc(v_a_2135_);
lean_inc_ref(v_a_2139_);
lean_inc_ref(v_a_2138_);
v___f_2147_ = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__1___boxed), 9, 7);
lean_closure_set(v___f_2147_, 0, v_a_2138_);
lean_closure_set(v___f_2147_, 1, v_a_2139_);
lean_closure_set(v___f_2147_, 2, v_f_2131_);
lean_closure_set(v___f_2147_, 3, v_a_2134_);
lean_closure_set(v___f_2147_, 4, v_a_2135_);
lean_closure_set(v___f_2147_, 5, v_a_2136_);
lean_closure_set(v___f_2147_, 6, v_a_2137_);
v___x_2148_ = lean_io_map_task(v___f_2147_, v_task_2141_, v_prio_2132_, v_sync_2133_);
if (v_isShared_2146_ == 0)
{
lean_ctor_set(v___x_2145_, 1, v_kind_2129_);
lean_ctor_set(v___x_2145_, 0, v___x_2148_);
v___x_2150_ = v___x_2145_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v___x_2148_);
lean_ctor_set(v_reuseFailAlloc_2151_, 1, v_kind_2129_);
lean_ctor_set(v_reuseFailAlloc_2151_, 2, v_caption_2142_);
lean_ctor_set_uint8(v_reuseFailAlloc_2151_, sizeof(void*)*3, v_optional_2143_);
v___x_2150_ = v_reuseFailAlloc_2151_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
return v___x_2150_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_mapM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_2129_ = stack[0].m_obj;
lean_object* v_self_2130_ = stack[1].m_obj;
lean_object* v_f_2131_ = stack[2].m_obj;
lean_object* v_prio_2132_ = stack[3].m_obj;
uint8_t v_sync_2133_ = stack[4].m_num;
lean_object* v_a_2134_ = stack[5].m_obj;
lean_object* v_a_2135_ = stack[6].m_obj;
lean_object* v_a_2136_ = stack[7].m_obj;
lean_object* v_a_2137_ = stack[8].m_obj;
lean_object* v_a_2138_ = stack[9].m_obj;
lean_object* v_a_2139_ = stack[10].m_obj;
lean_object* v_res_2154_;
v_res_2154_ = l_Lake_Job_mapM___redArg(v_kind_2129_, v_self_2130_, v_f_2131_, v_prio_2132_, v_sync_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
stack->m_obj
 = v_res_2154_;
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object* v_kind_2155_, lean_object* v_self_2156_, lean_object* v_f_2157_, lean_object* v_prio_2158_, lean_object* v_sync_2159_, lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
uint8_t v_sync_boxed_2167_; lean_object* v_res_2168_; 
v_sync_boxed_2167_ = lean_unbox(v_sync_2159_);
v_res_2168_ = l_Lake_Job_mapM___redArg(v_kind_2155_, v_self_2156_, v_f_2157_, v_prio_2158_, v_sync_boxed_2167_, v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec_ref(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec(v_a_2162_);
lean_dec(v_a_2161_);
return v_res_2168_;
}
}
lean_object* l_Lake_Job_mapM(lean_object* v_00_u03b2_2169_, lean_object* v_00_u03b1_2170_, lean_object* v_kind_2171_, lean_object* v_self_2172_, lean_object* v_f_2173_, lean_object* v_prio_2174_, uint8_t v_sync_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l_Lake_Job_mapM___redArg(v_kind_2171_, v_self_2172_, v_f_2173_, v_prio_2174_, v_sync_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
return v___x_2183_;
}
}
LEAN_EXPORT void l_Lake_Job_mapM_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_2171_ = stack[2].m_obj;
lean_object* v_self_2172_ = stack[3].m_obj;
lean_object* v_f_2173_ = stack[4].m_obj;
lean_object* v_prio_2174_ = stack[5].m_obj;
uint8_t v_sync_2175_ = stack[6].m_num;
lean_object* v_a_2176_ = stack[7].m_obj;
lean_object* v_a_2177_ = stack[8].m_obj;
lean_object* v_a_2178_ = stack[9].m_obj;
lean_object* v_a_2179_ = stack[10].m_obj;
lean_object* v_a_2180_ = stack[11].m_obj;
lean_object* v_a_2181_ = stack[12].m_obj;
lean_object* v_res_2184_;
v_res_2184_ = l_Lake_Job_mapM(lean_box(0), lean_box(0), v_kind_2171_, v_self_2172_, v_f_2173_, v_prio_2174_, v_sync_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_, v_a_2181_);
stack->m_obj
 = v_res_2184_;
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object* v_00_u03b2_2185_, lean_object* v_00_u03b1_2186_, lean_object* v_kind_2187_, lean_object* v_self_2188_, lean_object* v_f_2189_, lean_object* v_prio_2190_, lean_object* v_sync_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_){
_start:
{
uint8_t v_sync_boxed_2199_; lean_object* v_res_2200_; 
v_sync_boxed_2199_ = lean_unbox(v_sync_2191_);
v_res_2200_ = l_Lake_Job_mapM(v_00_u03b2_2185_, v_00_u03b1_2186_, v_kind_2187_, v_self_2188_, v_f_2189_, v_prio_2190_, v_sync_boxed_2199_, v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_, v_a_2196_, v_a_2197_);
lean_dec_ref(v_a_2197_);
lean_dec_ref(v_a_2196_);
lean_dec(v_a_2195_);
lean_dec(v_a_2194_);
lean_dec(v_a_2193_);
return v_res_2200_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object* v_a_2201_, lean_object* v_x_2202_){
_start:
{
if (lean_obj_tag(v_x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v_a_2204_; lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2227_; 
v_a_2203_ = lean_ctor_get(v_x_2202_, 0);
v_a_2204_ = lean_ctor_get(v_x_2202_, 1);
v_isSharedCheck_2227_ = !lean_is_exclusive(v_x_2202_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2206_ = v_x_2202_;
v_isShared_2207_ = v_isSharedCheck_2227_;
goto v_resetjp_2205_;
}
else
{
lean_inc(v_a_2204_);
lean_inc(v_a_2203_);
lean_dec(v_x_2202_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2227_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v_log_2209_; uint8_t v_action_2210_; uint8_t v_wantsRebuild_2211_; uint8_t v_canceled_2212_; lean_object* v_buildTime_2213_; lean_object* v_trace_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2224_; 
lean_inc(v_a_2204_);
v___x_2208_ = l_Lake_JobState_merge(v_a_2201_, v_a_2204_);
v_log_2209_ = lean_ctor_get(v___x_2208_, 0);
lean_inc_ref(v_log_2209_);
v_action_2210_ = lean_ctor_get_uint8(v___x_2208_, sizeof(void*)*3);
v_wantsRebuild_2211_ = lean_ctor_get_uint8(v___x_2208_, sizeof(void*)*3 + 1);
v_canceled_2212_ = lean_ctor_get_uint8(v___x_2208_, sizeof(void*)*3 + 2);
v_buildTime_2213_ = lean_ctor_get(v___x_2208_, 2);
lean_inc(v_buildTime_2213_);
lean_dec_ref(v___x_2208_);
v_trace_2214_ = lean_ctor_get(v_a_2204_, 1);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_a_2204_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; 
v_unused_2225_ = lean_ctor_get(v_a_2204_, 2);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_a_2204_, 0);
lean_dec(v_unused_2226_);
v___x_2216_ = v_a_2204_;
v_isShared_2217_ = v_isSharedCheck_2224_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_trace_2214_);
lean_dec(v_a_2204_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2224_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 2, v_buildTime_2213_);
lean_ctor_set(v___x_2216_, 0, v_log_2209_);
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_log_2209_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v_trace_2214_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_buildTime_2213_);
v___x_2219_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2221_; 
lean_ctor_set_uint8(v___x_2219_, sizeof(void*)*3, v_action_2210_);
lean_ctor_set_uint8(v___x_2219_, sizeof(void*)*3 + 1, v_wantsRebuild_2211_);
lean_ctor_set_uint8(v___x_2219_, sizeof(void*)*3 + 2, v_canceled_2212_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 1, v___x_2219_);
v___x_2221_ = v___x_2206_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2203_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v___x_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
else
{
lean_object* v_a_2228_; lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2255_; 
v_a_2228_ = lean_ctor_get(v_x_2202_, 0);
v_a_2229_ = lean_ctor_get(v_x_2202_, 1);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_x_2202_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2231_ = v_x_2202_;
v_isShared_2232_ = v_isSharedCheck_2255_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_inc(v_a_2228_);
lean_dec(v_x_2202_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2255_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v_log_2233_; lean_object* v___x_2234_; lean_object* v_log_2235_; uint8_t v_action_2236_; uint8_t v_wantsRebuild_2237_; uint8_t v_canceled_2238_; lean_object* v_buildTime_2239_; lean_object* v_trace_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2252_; 
v_log_2233_ = lean_ctor_get(v_a_2201_, 0);
lean_inc_ref(v_log_2233_);
lean_inc(v_a_2229_);
v___x_2234_ = l_Lake_JobState_merge(v_a_2201_, v_a_2229_);
v_log_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc_ref(v_log_2235_);
v_action_2236_ = lean_ctor_get_uint8(v___x_2234_, sizeof(void*)*3);
v_wantsRebuild_2237_ = lean_ctor_get_uint8(v___x_2234_, sizeof(void*)*3 + 1);
v_canceled_2238_ = lean_ctor_get_uint8(v___x_2234_, sizeof(void*)*3 + 2);
v_buildTime_2239_ = lean_ctor_get(v___x_2234_, 2);
lean_inc(v_buildTime_2239_);
lean_dec_ref(v___x_2234_);
v_trace_2240_ = lean_ctor_get(v_a_2229_, 1);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_a_2229_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; lean_object* v_unused_2254_; 
v_unused_2253_ = lean_ctor_get(v_a_2229_, 2);
lean_dec(v_unused_2253_);
v_unused_2254_ = lean_ctor_get(v_a_2229_, 0);
lean_dec(v_unused_2254_);
v___x_2242_ = v_a_2229_;
v_isShared_2243_ = v_isSharedCheck_2252_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_trace_2240_);
lean_dec(v_a_2229_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2252_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2247_; 
v___x_2244_ = lean_array_get_size(v_log_2233_);
lean_dec_ref(v_log_2233_);
v___x_2245_ = lean_nat_add(v___x_2244_, v_a_2228_);
lean_dec(v_a_2228_);
if (v_isShared_2243_ == 0)
{
lean_ctor_set(v___x_2242_, 2, v_buildTime_2239_);
lean_ctor_set(v___x_2242_, 0, v_log_2235_);
v___x_2247_ = v___x_2242_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2251_; 
v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_log_2235_);
lean_ctor_set(v_reuseFailAlloc_2251_, 1, v_trace_2240_);
lean_ctor_set(v_reuseFailAlloc_2251_, 2, v_buildTime_2239_);
v___x_2247_ = v_reuseFailAlloc_2251_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
lean_object* v___x_2249_; 
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3, v_action_2236_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3 + 1, v_wantsRebuild_2237_);
lean_ctor_set_uint8(v___x_2247_, sizeof(void*)*3 + 2, v_canceled_2238_);
if (v_isShared_2232_ == 0)
{
lean_ctor_set(v___x_2231_, 1, v___x_2247_);
lean_ctor_set(v___x_2231_, 0, v___x_2245_);
v___x_2249_ = v___x_2231_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2250_; 
v_reuseFailAlloc_2250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2250_, 0, v___x_2245_);
lean_ctor_set(v_reuseFailAlloc_2250_, 1, v___x_2247_);
v___x_2249_ = v_reuseFailAlloc_2250_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
return v___x_2249_;
}
}
}
}
}
}
}
lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object* v_val_2256_, lean_object* v_val_2257_, lean_object* v_a_x3f_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2261_ = lean_get_set_stdout(v_val_2256_);
lean_dec_ref(v___x_2261_);
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_get_set_stderr(v_val_2257_);
lean_dec_ref(v___x_2263_);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2262_);
lean_ctor_set(v___x_2264_, 1, v___y_2259_);
return v___x_2264_;
}
}
LEAN_EXPORT void l_Lake_Job_bindM___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2256_ = stack[0].m_obj;
lean_object* v_val_2257_ = stack[1].m_obj;
lean_object* v_a_x3f_2258_ = stack[2].m_obj;
lean_object* v___y_2259_ = stack[3].m_obj;
lean_object* v_res_2265_;
v_res_2265_ = l_Lake_Job_bindM___redArg___lam__1(v_val_2256_, v_val_2257_, v_a_x3f_2258_, v___y_2259_);
stack->m_obj
 = v_res_2265_;
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1___boxed(lean_object* v_val_2266_, lean_object* v_val_2267_, lean_object* v_a_x3f_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_Lake_Job_bindM___redArg___lam__1(v_val_2266_, v_val_2267_, v_a_x3f_2268_, v___y_2269_);
lean_dec(v_a_x3f_2268_);
return v_res_2271_;
}
}
lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object* v_a_2272_, lean_object* v_____r_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___x_2281_; 
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v_a_2272_);
lean_ctor_set(v___x_2281_, 1, v___y_2279_);
return v___x_2281_;
}
}
LEAN_EXPORT void l_Lake_Job_bindM___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2272_ = stack[0].m_obj;
lean_object* v_____r_2273_ = stack[1].m_obj;
lean_object* v___y_2274_ = stack[2].m_obj;
lean_object* v___y_2275_ = stack[3].m_obj;
lean_object* v___y_2276_ = stack[4].m_obj;
lean_object* v___y_2277_ = stack[5].m_obj;
lean_object* v___y_2278_ = stack[6].m_obj;
lean_object* v___y_2279_ = stack[7].m_obj;
lean_object* v_res_2282_;
v_res_2282_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2272_, v_____r_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
stack->m_obj
 = v_res_2282_;
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2___boxed(lean_object* v_a_2283_, lean_object* v_____r_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2283_, v_____r_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec(v___y_2286_);
lean_dec_ref(v___y_2285_);
return v_res_2292_;
}
}
lean_object* l_Lake_Job_bindM___redArg___lam__3(lean_object* v_a_2293_, lean_object* v_prio_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_, lean_object* v_a_2298_, lean_object* v_a_2299_, lean_object* v_f_2300_, lean_object* v_x_2301_){
_start:
{
lean_object* v_a_2304_; lean_object* v_a_2305_; lean_object* v___y_2309_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; uint8_t v___y_2323_; lean_object* v___y_2324_; lean_object* v___y_2325_; uint8_t v___y_2326_; uint8_t v___y_2327_; lean_object* v___y_2328_; 
if (lean_obj_tag(v_x_2301_) == 0)
{
lean_object* v_a_2344_; lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2416_; 
v_a_2344_ = lean_ctor_get(v_x_2301_, 0);
v_a_2345_ = lean_ctor_get(v_x_2301_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_x_2301_);
if (v_isSharedCheck_2416_ == 0)
{
v___x_2347_ = v_x_2301_;
v_isShared_2348_ = v_isSharedCheck_2416_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_inc(v_a_2344_);
lean_dec(v_x_2301_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2416_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v_cancelTk_x3f_2394_; 
v_cancelTk_x3f_2394_ = lean_ctor_get(v_a_2293_, 6);
if (lean_obj_tag(v_cancelTk_x3f_2394_) == 1)
{
lean_object* v_val_2395_; uint8_t v___x_2396_; 
v_val_2395_ = lean_ctor_get(v_cancelTk_x3f_2394_, 0);
v___x_2396_ = l_IO_CancelToken_isSet(v_val_2395_);
if (v___x_2396_ == 0)
{
lean_del_object(v___x_2347_);
goto v___jp_2349_;
}
else
{
lean_object* v_log_2397_; uint8_t v_action_2398_; uint8_t v_wantsRebuild_2399_; lean_object* v_trace_2400_; lean_object* v_buildTime_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2415_; 
lean_dec(v_a_2344_);
lean_dec_ref(v_f_2300_);
lean_dec_ref(v_a_2295_);
lean_dec(v_prio_2294_);
v_log_2397_ = lean_ctor_get(v_a_2345_, 0);
v_action_2398_ = lean_ctor_get_uint8(v_a_2345_, sizeof(void*)*3);
v_wantsRebuild_2399_ = lean_ctor_get_uint8(v_a_2345_, sizeof(void*)*3 + 1);
v_trace_2400_ = lean_ctor_get(v_a_2345_, 1);
v_buildTime_2401_ = lean_ctor_get(v_a_2345_, 2);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_a_2345_);
if (v_isSharedCheck_2415_ == 0)
{
v___x_2403_ = v_a_2345_;
v_isShared_2404_ = v_isSharedCheck_2415_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_buildTime_2401_);
lean_inc(v_trace_2400_);
lean_inc(v_log_2397_);
lean_dec(v_a_2345_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2415_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2409_; 
v___x_2405_ = lean_array_get_size(v_log_2397_);
v___x_2406_ = ((lean_object*)(l___private_Lake_Build_Job_Monad_0__Lake_Job_canceledResult___redArg___closed__1));
v___x_2407_ = lean_array_push(v_log_2397_, v___x_2406_);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2407_);
v___x_2409_ = v___x_2403_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2407_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_trace_2400_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v_buildTime_2401_);
lean_ctor_set_uint8(v_reuseFailAlloc_2414_, sizeof(void*)*3, v_action_2398_);
lean_ctor_set_uint8(v_reuseFailAlloc_2414_, sizeof(void*)*3 + 1, v_wantsRebuild_2399_);
v___x_2409_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2411_; 
lean_ctor_set_uint8(v___x_2409_, sizeof(void*)*3 + 2, v___x_2396_);
if (v_isShared_2348_ == 0)
{
lean_ctor_set_tag(v___x_2347_, 1);
lean_ctor_set(v___x_2347_, 1, v___x_2409_);
lean_ctor_set(v___x_2347_, 0, v___x_2405_);
v___x_2411_ = v___x_2347_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v___x_2405_);
lean_ctor_set(v_reuseFailAlloc_2413_, 1, v___x_2409_);
v___x_2411_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
lean_object* v___x_2412_; 
v___x_2412_ = lean_task_pure(v___x_2411_);
return v___x_2412_;
}
}
}
}
}
else
{
lean_del_object(v___x_2347_);
goto v___jp_2349_;
}
v___jp_2349_:
{
lean_object* v_log_2350_; uint8_t v_action_2351_; uint8_t v_wantsRebuild_2352_; uint8_t v_canceled_2353_; lean_object* v_trace_2354_; lean_object* v_buildTime_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2393_; 
v_log_2350_ = lean_ctor_get(v_a_2345_, 0);
v_action_2351_ = lean_ctor_get_uint8(v_a_2345_, sizeof(void*)*3);
v_wantsRebuild_2352_ = lean_ctor_get_uint8(v_a_2345_, sizeof(void*)*3 + 1);
v_canceled_2353_ = lean_ctor_get_uint8(v_a_2345_, sizeof(void*)*3 + 2);
v_trace_2354_ = lean_ctor_get(v_a_2345_, 1);
v_buildTime_2355_ = lean_ctor_get(v_a_2345_, 2);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_a_2345_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2357_ = v_a_2345_;
v_isShared_2358_ = v_isSharedCheck_2393_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_buildTime_2355_);
lean_inc(v_trace_2354_);
lean_inc(v_log_2350_);
lean_dec(v_a_2345_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2393_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v_trace_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2367_; 
lean_inc_ref(v_a_2299_);
v_trace_2359_ = l_Lake_BuildTrace_mix(v_a_2299_, v_trace_2354_);
v___x_2360_ = lean_unsigned_to_nat(0u);
v___x_2361_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_2362_ = lean_st_mk_ref(v___x_2361_);
lean_inc(v___x_2362_);
v___x_2363_ = l_IO_FS_Stream_ofBuffer(v___x_2362_);
lean_inc_ref(v___x_2363_);
v___x_2364_ = lean_get_set_stdout(v___x_2363_);
v___x_2365_ = lean_get_set_stderr(v___x_2363_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 1, v_trace_2359_);
v___x_2367_ = v___x_2357_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2392_; 
v_reuseFailAlloc_2392_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2392_, 0, v_log_2350_);
lean_ctor_set(v_reuseFailAlloc_2392_, 1, v_trace_2359_);
lean_ctor_set(v_reuseFailAlloc_2392_, 2, v_buildTime_2355_);
lean_ctor_set_uint8(v_reuseFailAlloc_2392_, sizeof(void*)*3, v_action_2351_);
lean_ctor_set_uint8(v_reuseFailAlloc_2392_, sizeof(void*)*3 + 1, v_wantsRebuild_2352_);
lean_ctor_set_uint8(v_reuseFailAlloc_2392_, sizeof(void*)*3 + 2, v_canceled_2353_);
v___x_2367_ = v_reuseFailAlloc_2392_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
lean_object* v___x_2368_; 
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc(v_a_2296_);
lean_inc_ref(v_a_2295_);
v___x_2368_ = lean_apply_8(v_f_2300_, v_a_2344_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2293_, v___x_2367_, lean_box(0));
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v_a_2370_; lean_object* v___f_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v_a_2374_; lean_object* v_log_2375_; uint8_t v_action_2376_; uint8_t v_wantsRebuild_2377_; uint8_t v_canceled_2378_; lean_object* v_trace_2379_; lean_object* v_buildTime_2380_; lean_object* v___x_2381_; lean_object* v_data_2382_; uint8_t v___x_2383_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc_n(v_a_2369_, 2);
v_a_2370_ = lean_ctor_get(v___x_2368_, 1);
lean_inc(v_a_2370_);
lean_dec_ref_known(v___x_2368_, 2);
v___f_2371_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__2___boxed), 9, 1);
lean_closure_set(v___f_2371_, 0, v_a_2369_);
v___x_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2372_, 0, v_a_2369_);
v___x_2373_ = l_Lake_Job_bindM___redArg___lam__1(v___x_2364_, v___x_2365_, v___x_2372_, v_a_2370_);
lean_dec_ref_known(v___x_2372_, 1);
v_a_2374_ = lean_ctor_get(v___x_2373_, 1);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2373_);
v_log_2375_ = lean_ctor_get(v_a_2374_, 0);
lean_inc_ref(v_log_2375_);
v_action_2376_ = lean_ctor_get_uint8(v_a_2374_, sizeof(void*)*3);
v_wantsRebuild_2377_ = lean_ctor_get_uint8(v_a_2374_, sizeof(void*)*3 + 1);
v_canceled_2378_ = lean_ctor_get_uint8(v_a_2374_, sizeof(void*)*3 + 2);
v_trace_2379_ = lean_ctor_get(v_a_2374_, 1);
lean_inc_ref(v_trace_2379_);
v_buildTime_2380_ = lean_ctor_get(v_a_2374_, 2);
lean_inc(v_buildTime_2380_);
v___x_2381_ = lean_st_ref_get(v___x_2362_);
lean_dec(v___x_2362_);
v_data_2382_ = lean_ctor_get(v___x_2381_, 0);
lean_inc_ref(v_data_2382_);
lean_dec(v___x_2381_);
v___x_2383_ = lean_string_validate_utf8(v_data_2382_);
if (v___x_2383_ == 0)
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_dec_ref(v_data_2382_);
v___x_2384_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2385_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2384_);
v___y_2319_ = v_buildTime_2380_;
v___y_2320_ = v___x_2360_;
v___y_2321_ = v___f_2371_;
v___y_2322_ = v_trace_2379_;
v___y_2323_ = v_wantsRebuild_2377_;
v___y_2324_ = v_log_2375_;
v___y_2325_ = v_a_2374_;
v___y_2326_ = v_canceled_2378_;
v___y_2327_ = v_action_2376_;
v___y_2328_ = v___x_2385_;
goto v___jp_2318_;
}
else
{
lean_object* v___x_2386_; 
v___x_2386_ = lean_string_from_utf8_unchecked(v_data_2382_);
v___y_2319_ = v_buildTime_2380_;
v___y_2320_ = v___x_2360_;
v___y_2321_ = v___f_2371_;
v___y_2322_ = v_trace_2379_;
v___y_2323_ = v_wantsRebuild_2377_;
v___y_2324_ = v_log_2375_;
v___y_2325_ = v_a_2374_;
v___y_2326_ = v_canceled_2378_;
v___y_2327_ = v_action_2376_;
v___y_2328_ = v___x_2386_;
goto v___jp_2318_;
}
}
else
{
lean_object* v_a_2387_; lean_object* v_a_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v_a_2391_; 
lean_dec(v___x_2362_);
lean_dec_ref(v_a_2295_);
lean_dec(v_prio_2294_);
v_a_2387_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2387_);
v_a_2388_ = lean_ctor_get(v___x_2368_, 1);
lean_inc(v_a_2388_);
lean_dec_ref_known(v___x_2368_, 2);
v___x_2389_ = lean_box(0);
v___x_2390_ = l_Lake_Job_bindM___redArg___lam__1(v___x_2364_, v___x_2365_, v___x_2389_, v_a_2388_);
v_a_2391_ = lean_ctor_get(v___x_2390_, 1);
lean_inc(v_a_2391_);
lean_dec_ref(v___x_2390_);
v_a_2304_ = v_a_2387_;
v_a_2305_ = v_a_2391_;
goto v___jp_2303_;
}
}
}
}
}
}
else
{
lean_object* v_a_2417_; lean_object* v_a_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2426_; 
lean_dec_ref(v_f_2300_);
lean_dec_ref(v_a_2295_);
lean_dec(v_prio_2294_);
v_a_2417_ = lean_ctor_get(v_x_2301_, 0);
v_a_2418_ = lean_ctor_get(v_x_2301_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_x_2301_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2420_ = v_x_2301_;
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_a_2418_);
lean_inc(v_a_2417_);
lean_dec(v_x_2301_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2423_; 
if (v_isShared_2421_ == 0)
{
v___x_2423_ = v___x_2420_;
goto v_reusejp_2422_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2417_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_a_2418_);
v___x_2423_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2422_;
}
v_reusejp_2422_:
{
lean_object* v___x_2424_; 
v___x_2424_ = lean_task_pure(v___x_2423_);
return v___x_2424_;
}
}
}
v___jp_2303_:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2306_, 0, v_a_2304_);
lean_ctor_set(v___x_2306_, 1, v_a_2305_);
v___x_2307_ = lean_task_pure(v___x_2306_);
return v___x_2307_;
}
v___jp_2308_:
{
if (lean_obj_tag(v___y_2309_) == 0)
{
lean_object* v_a_2310_; lean_object* v_a_2311_; lean_object* v_task_2312_; lean_object* v___f_2313_; uint8_t v___x_2314_; lean_object* v___x_2315_; 
v_a_2310_ = lean_ctor_get(v___y_2309_, 0);
lean_inc(v_a_2310_);
v_a_2311_ = lean_ctor_get(v___y_2309_, 1);
lean_inc(v_a_2311_);
lean_dec_ref_known(v___y_2309_, 2);
v_task_2312_ = lean_ctor_get(v_a_2310_, 0);
lean_inc_ref(v_task_2312_);
lean_dec(v_a_2310_);
v___f_2313_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2313_, 0, v_a_2311_);
v___x_2314_ = 1;
v___x_2315_ = lean_task_map(v___f_2313_, v_task_2312_, v_prio_2294_, v___x_2314_);
return v___x_2315_;
}
else
{
lean_object* v_a_2316_; lean_object* v_a_2317_; 
lean_dec(v_prio_2294_);
v_a_2316_ = lean_ctor_get(v___y_2309_, 0);
lean_inc(v_a_2316_);
v_a_2317_ = lean_ctor_get(v___y_2309_, 1);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___y_2309_, 2);
v_a_2304_ = v_a_2316_;
v_a_2305_ = v_a_2317_;
goto v___jp_2303_;
}
}
v___jp_2318_:
{
lean_object* v___x_2329_; uint8_t v___x_2330_; 
v___x_2329_ = lean_string_utf8_byte_size(v___y_2328_);
v___x_2330_ = lean_nat_dec_eq(v___x_2329_, v___y_2320_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
lean_dec_ref(v___y_2325_);
v___x_2331_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_2332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2332_, 0, v___y_2328_);
lean_ctor_set(v___x_2332_, 1, v___y_2320_);
lean_ctor_set(v___x_2332_, 2, v___x_2329_);
v___x_2333_ = l_String_Slice_trimAscii(v___x_2332_);
v___x_2334_ = l_String_Slice_toString(v___x_2333_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = lean_string_append(v___x_2331_, v___x_2334_);
lean_dec_ref(v___x_2334_);
v___x_2336_ = 1;
v___x_2337_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2337_, 0, v___x_2335_);
lean_ctor_set_uint8(v___x_2337_, sizeof(void*)*1, v___x_2336_);
v___x_2338_ = lean_box(0);
v___x_2339_ = lean_array_push(v___y_2324_, v___x_2337_);
v___x_2340_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
lean_ctor_set(v___x_2340_, 1, v___y_2322_);
lean_ctor_set(v___x_2340_, 2, v___y_2319_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*3, v___y_2327_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*3 + 1, v___y_2323_);
lean_ctor_set_uint8(v___x_2340_, sizeof(void*)*3 + 2, v___y_2326_);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc(v_a_2296_);
v___x_2341_ = lean_apply_8(v___y_2321_, v___x_2338_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2293_, v___x_2340_, lean_box(0));
v___y_2309_ = v___x_2341_;
goto v___jp_2308_;
}
else
{
lean_object* v___x_2342_; lean_object* v___x_2343_; 
lean_dec_ref(v___y_2328_);
lean_dec_ref(v___y_2324_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2320_);
lean_dec(v___y_2319_);
v___x_2342_ = lean_box(0);
lean_inc_ref(v_a_2293_);
lean_inc(v_a_2298_);
lean_inc(v_a_2297_);
lean_inc(v_a_2296_);
v___x_2343_ = lean_apply_8(v___y_2321_, v___x_2342_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2293_, v___y_2325_, lean_box(0));
v___y_2309_ = v___x_2343_;
goto v___jp_2308_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_bindM___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2293_ = stack[0].m_obj;
lean_object* v_prio_2294_ = stack[1].m_obj;
lean_object* v_a_2295_ = stack[2].m_obj;
lean_object* v_a_2296_ = stack[3].m_obj;
lean_object* v_a_2297_ = stack[4].m_obj;
lean_object* v_a_2298_ = stack[5].m_obj;
lean_object* v_a_2299_ = stack[6].m_obj;
lean_object* v_f_2300_ = stack[7].m_obj;
lean_object* v_x_2301_ = stack[8].m_obj;
lean_object* v_res_2427_;
v_res_2427_ = l_Lake_Job_bindM___redArg___lam__3(v_a_2293_, v_prio_2294_, v_a_2295_, v_a_2296_, v_a_2297_, v_a_2298_, v_a_2299_, v_f_2300_, v_x_2301_);
stack->m_obj
 = v_res_2427_;
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3___boxed(lean_object* v_a_2428_, lean_object* v_prio_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_f_2435_, lean_object* v_x_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lake_Job_bindM___redArg___lam__3(v_a_2428_, v_prio_2429_, v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_, v_f_2435_, v_x_2436_);
lean_dec_ref(v_a_2434_);
lean_dec(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2428_);
return v_res_2438_;
}
}
lean_object* l_Lake_Job_bindM___redArg(lean_object* v_kind_2439_, lean_object* v_self_2440_, lean_object* v_f_2441_, lean_object* v_prio_2442_, uint8_t v_sync_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_task_2451_; lean_object* v_caption_2452_; uint8_t v_optional_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2462_; 
v_task_2451_ = lean_ctor_get(v_self_2440_, 0);
v_caption_2452_ = lean_ctor_get(v_self_2440_, 2);
v_optional_2453_ = lean_ctor_get_uint8(v_self_2440_, sizeof(void*)*3);
v_isSharedCheck_2462_ = !lean_is_exclusive(v_self_2440_);
if (v_isSharedCheck_2462_ == 0)
{
lean_object* v_unused_2463_; 
v_unused_2463_ = lean_ctor_get(v_self_2440_, 1);
lean_dec(v_unused_2463_);
v___x_2455_ = v_self_2440_;
v_isShared_2456_ = v_isSharedCheck_2462_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_caption_2452_);
lean_inc(v_task_2451_);
lean_dec(v_self_2440_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2462_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___f_2457_; lean_object* v___x_2458_; lean_object* v___x_2460_; 
lean_inc_ref(v_a_2449_);
lean_inc(v_a_2447_);
lean_inc(v_a_2446_);
lean_inc(v_a_2445_);
lean_inc(v_prio_2442_);
lean_inc_ref(v_a_2448_);
v___f_2457_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__3___boxed), 10, 8);
lean_closure_set(v___f_2457_, 0, v_a_2448_);
lean_closure_set(v___f_2457_, 1, v_prio_2442_);
lean_closure_set(v___f_2457_, 2, v_a_2444_);
lean_closure_set(v___f_2457_, 3, v_a_2445_);
lean_closure_set(v___f_2457_, 4, v_a_2446_);
lean_closure_set(v___f_2457_, 5, v_a_2447_);
lean_closure_set(v___f_2457_, 6, v_a_2449_);
lean_closure_set(v___f_2457_, 7, v_f_2441_);
v___x_2458_ = lean_io_bind_task(v_task_2451_, v___f_2457_, v_prio_2442_, v_sync_2443_);
if (v_isShared_2456_ == 0)
{
lean_ctor_set(v___x_2455_, 1, v_kind_2439_);
lean_ctor_set(v___x_2455_, 0, v___x_2458_);
v___x_2460_ = v___x_2455_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2461_, 1, v_kind_2439_);
lean_ctor_set(v_reuseFailAlloc_2461_, 2, v_caption_2452_);
lean_ctor_set_uint8(v_reuseFailAlloc_2461_, sizeof(void*)*3, v_optional_2453_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_bindM___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_2439_ = stack[0].m_obj;
lean_object* v_self_2440_ = stack[1].m_obj;
lean_object* v_f_2441_ = stack[2].m_obj;
lean_object* v_prio_2442_ = stack[3].m_obj;
uint8_t v_sync_2443_ = stack[4].m_num;
lean_object* v_a_2444_ = stack[5].m_obj;
lean_object* v_a_2445_ = stack[6].m_obj;
lean_object* v_a_2446_ = stack[7].m_obj;
lean_object* v_a_2447_ = stack[8].m_obj;
lean_object* v_a_2448_ = stack[9].m_obj;
lean_object* v_a_2449_ = stack[10].m_obj;
lean_object* v_res_2464_;
v_res_2464_ = l_Lake_Job_bindM___redArg(v_kind_2439_, v_self_2440_, v_f_2441_, v_prio_2442_, v_sync_2443_, v_a_2444_, v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
stack->m_obj
 = v_res_2464_;
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object* v_kind_2465_, lean_object* v_self_2466_, lean_object* v_f_2467_, lean_object* v_prio_2468_, lean_object* v_sync_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_){
_start:
{
uint8_t v_sync_boxed_2477_; lean_object* v_res_2478_; 
v_sync_boxed_2477_ = lean_unbox(v_sync_2469_);
v_res_2478_ = l_Lake_Job_bindM___redArg(v_kind_2465_, v_self_2466_, v_f_2467_, v_prio_2468_, v_sync_boxed_2477_, v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_, v_a_2474_, v_a_2475_);
lean_dec_ref(v_a_2475_);
lean_dec_ref(v_a_2474_);
lean_dec(v_a_2473_);
lean_dec(v_a_2472_);
lean_dec(v_a_2471_);
return v_res_2478_;
}
}
lean_object* l_Lake_Job_bindM(lean_object* v_00_u03b2_2479_, lean_object* v_00_u03b1_2480_, lean_object* v_kind_2481_, lean_object* v_self_2482_, lean_object* v_f_2483_, lean_object* v_prio_2484_, uint8_t v_sync_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_){
_start:
{
lean_object* v___x_2493_; 
v___x_2493_ = l_Lake_Job_bindM___redArg(v_kind_2481_, v_self_2482_, v_f_2483_, v_prio_2484_, v_sync_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
return v___x_2493_;
}
}
LEAN_EXPORT void l_Lake_Job_bindM_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_2481_ = stack[2].m_obj;
lean_object* v_self_2482_ = stack[3].m_obj;
lean_object* v_f_2483_ = stack[4].m_obj;
lean_object* v_prio_2484_ = stack[5].m_obj;
uint8_t v_sync_2485_ = stack[6].m_num;
lean_object* v_a_2486_ = stack[7].m_obj;
lean_object* v_a_2487_ = stack[8].m_obj;
lean_object* v_a_2488_ = stack[9].m_obj;
lean_object* v_a_2489_ = stack[10].m_obj;
lean_object* v_a_2490_ = stack[11].m_obj;
lean_object* v_a_2491_ = stack[12].m_obj;
lean_object* v_res_2494_;
v_res_2494_ = l_Lake_Job_bindM(lean_box(0), lean_box(0), v_kind_2481_, v_self_2482_, v_f_2483_, v_prio_2484_, v_sync_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_, v_a_2490_, v_a_2491_);
stack->m_obj
 = v_res_2494_;
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object* v_00_u03b2_2495_, lean_object* v_00_u03b1_2496_, lean_object* v_kind_2497_, lean_object* v_self_2498_, lean_object* v_f_2499_, lean_object* v_prio_2500_, lean_object* v_sync_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_){
_start:
{
uint8_t v_sync_boxed_2509_; lean_object* v_res_2510_; 
v_sync_boxed_2509_ = lean_unbox(v_sync_2501_);
v_res_2510_ = l_Lake_Job_bindM(v_00_u03b2_2495_, v_00_u03b1_2496_, v_kind_2497_, v_self_2498_, v_f_2499_, v_prio_2500_, v_sync_boxed_2509_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_, v_a_2507_);
lean_dec_ref(v_a_2507_);
lean_dec_ref(v_a_2506_);
lean_dec(v_a_2505_);
lean_dec(v_a_2504_);
lean_dec(v_a_2503_);
return v_res_2510_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object* v_f_2511_, lean_object* v_rx_2512_, lean_object* v_ry_2513_){
_start:
{
lean_object* v___x_2514_; 
v___x_2514_ = lean_apply_2(v_f_2511_, v_rx_2512_, v_ry_2513_);
return v___x_2514_;
}
}
lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object* v_other_2515_, lean_object* v_f_2516_, lean_object* v_prio_2517_, uint8_t v_sync_2518_, lean_object* v_rx_2519_){
_start:
{
lean_object* v_task_2520_; lean_object* v___f_2521_; lean_object* v___x_2522_; 
v_task_2520_ = lean_ctor_get(v_other_2515_, 0);
lean_inc_ref(v_task_2520_);
lean_dec_ref(v_other_2515_);
v___f_2521_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2521_, 0, v_f_2516_);
lean_closure_set(v___f_2521_, 1, v_rx_2519_);
v___x_2522_ = lean_task_map(v___f_2521_, v_task_2520_, v_prio_2517_, v_sync_2518_);
return v___x_2522_;
}
}
LEAN_EXPORT void l_Lake_Job_zipResultWith___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_other_2515_ = stack[0].m_obj;
lean_object* v_f_2516_ = stack[1].m_obj;
lean_object* v_prio_2517_ = stack[2].m_obj;
uint8_t v_sync_2518_ = stack[3].m_num;
lean_object* v_rx_2519_ = stack[4].m_obj;
lean_object* v_res_2523_;
v_res_2523_ = l_Lake_Job_zipResultWith___redArg___lam__1(v_other_2515_, v_f_2516_, v_prio_2517_, v_sync_2518_, v_rx_2519_);
stack->m_obj
 = v_res_2523_;
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object* v_other_2524_, lean_object* v_f_2525_, lean_object* v_prio_2526_, lean_object* v_sync_2527_, lean_object* v_rx_2528_){
_start:
{
uint8_t v_sync_boxed_2529_; lean_object* v_res_2530_; 
v_sync_boxed_2529_ = lean_unbox(v_sync_2527_);
v_res_2530_ = l_Lake_Job_zipResultWith___redArg___lam__1(v_other_2524_, v_f_2525_, v_prio_2526_, v_sync_boxed_2529_, v_rx_2528_);
return v_res_2530_;
}
}
lean_object* l_Lake_Job_zipResultWith___redArg(lean_object* v_inst_2531_, lean_object* v_f_2532_, lean_object* v_self_2533_, lean_object* v_other_2534_, lean_object* v_prio_2535_, uint8_t v_sync_2536_){
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
v___f_2542_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
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
LEAN_EXPORT void l_Lake_Job_zipResultWith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2531_ = stack[0].m_obj;
lean_object* v_f_2532_ = stack[1].m_obj;
lean_object* v_self_2533_ = stack[2].m_obj;
lean_object* v_other_2534_ = stack[3].m_obj;
lean_object* v_prio_2535_ = stack[4].m_obj;
uint8_t v_sync_2536_ = stack[5].m_num;
lean_object* v_res_2553_;
v_res_2553_ = l_Lake_Job_zipResultWith___redArg(v_inst_2531_, v_f_2532_, v_self_2533_, v_other_2534_, v_prio_2535_, v_sync_2536_);
stack->m_obj
 = v_res_2553_;
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object* v_inst_2554_, lean_object* v_f_2555_, lean_object* v_self_2556_, lean_object* v_other_2557_, lean_object* v_prio_2558_, lean_object* v_sync_2559_){
_start:
{
uint8_t v_sync_boxed_2560_; lean_object* v_res_2561_; 
v_sync_boxed_2560_ = lean_unbox(v_sync_2559_);
v_res_2561_ = l_Lake_Job_zipResultWith___redArg(v_inst_2554_, v_f_2555_, v_self_2556_, v_other_2557_, v_prio_2558_, v_sync_boxed_2560_);
return v_res_2561_;
}
}
lean_object* l_Lake_Job_zipResultWith(lean_object* v_00_u03b3_2562_, lean_object* v_00_u03b1_2563_, lean_object* v_00_u03b2_2564_, lean_object* v_inst_2565_, lean_object* v_f_2566_, lean_object* v_self_2567_, lean_object* v_other_2568_, lean_object* v_prio_2569_, uint8_t v_sync_2570_){
_start:
{
lean_object* v_task_2571_; lean_object* v___x_2573_; uint8_t v_isShared_2574_; uint8_t v_isSharedCheck_2584_; 
v_task_2571_ = lean_ctor_get(v_self_2567_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_self_2567_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; lean_object* v_unused_2586_; 
v_unused_2585_ = lean_ctor_get(v_self_2567_, 2);
lean_dec(v_unused_2585_);
v_unused_2586_ = lean_ctor_get(v_self_2567_, 1);
lean_dec(v_unused_2586_);
v___x_2573_ = v_self_2567_;
v_isShared_2574_ = v_isSharedCheck_2584_;
goto v_resetjp_2572_;
}
else
{
lean_inc(v_task_2571_);
lean_dec(v_self_2567_);
v___x_2573_ = lean_box(0);
v_isShared_2574_ = v_isSharedCheck_2584_;
goto v_resetjp_2572_;
}
v_resetjp_2572_:
{
lean_object* v___x_2575_; lean_object* v___f_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; lean_object* v___x_2582_; 
v___x_2575_ = lean_box(v_sync_2570_);
lean_inc(v_prio_2569_);
v___f_2576_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2576_, 0, v_other_2568_);
lean_closure_set(v___f_2576_, 1, v_f_2566_);
lean_closure_set(v___f_2576_, 2, v_prio_2569_);
lean_closure_set(v___f_2576_, 3, v___x_2575_);
v___x_2577_ = 1;
v___x_2578_ = lean_task_bind(v_task_2571_, v___f_2576_, v_prio_2569_, v___x_2577_);
v___x_2579_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2580_ = 0;
if (v_isShared_2574_ == 0)
{
lean_ctor_set(v___x_2573_, 2, v___x_2579_);
lean_ctor_set(v___x_2573_, 1, v_inst_2565_);
lean_ctor_set(v___x_2573_, 0, v___x_2578_);
v___x_2582_ = v___x_2573_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2578_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_inst_2565_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v___x_2579_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
lean_ctor_set_uint8(v___x_2582_, sizeof(void*)*3, v___x_2580_);
return v___x_2582_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_zipResultWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2565_ = stack[3].m_obj;
lean_object* v_f_2566_ = stack[4].m_obj;
lean_object* v_self_2567_ = stack[5].m_obj;
lean_object* v_other_2568_ = stack[6].m_obj;
lean_object* v_prio_2569_ = stack[7].m_obj;
uint8_t v_sync_2570_ = stack[8].m_num;
lean_object* v_res_2587_;
v_res_2587_ = l_Lake_Job_zipResultWith(lean_box(0), lean_box(0), lean_box(0), v_inst_2565_, v_f_2566_, v_self_2567_, v_other_2568_, v_prio_2569_, v_sync_2570_);
stack->m_obj
 = v_res_2587_;
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object* v_00_u03b3_2588_, lean_object* v_00_u03b1_2589_, lean_object* v_00_u03b2_2590_, lean_object* v_inst_2591_, lean_object* v_f_2592_, lean_object* v_self_2593_, lean_object* v_other_2594_, lean_object* v_prio_2595_, lean_object* v_sync_2596_){
_start:
{
uint8_t v_sync_boxed_2597_; lean_object* v_res_2598_; 
v_sync_boxed_2597_ = lean_unbox(v_sync_2596_);
v_res_2598_ = l_Lake_Job_zipResultWith(v_00_u03b3_2588_, v_00_u03b1_2589_, v_00_u03b2_2590_, v_inst_2591_, v_f_2592_, v_self_2593_, v_other_2594_, v_prio_2595_, v_sync_boxed_2597_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object* v_rx_2599_, lean_object* v_f_2600_, lean_object* v_ry_2601_){
_start:
{
lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2609_; lean_object* v___y_2610_; lean_object* v___y_2611_; lean_object* v_a_2614_; 
if (lean_obj_tag(v_rx_2599_) == 0)
{
if (lean_obj_tag(v_ry_2601_) == 0)
{
lean_object* v_a_2616_; lean_object* v_a_2617_; lean_object* v_a_2618_; lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2628_; 
v_a_2616_ = lean_ctor_get(v_rx_2599_, 0);
lean_inc(v_a_2616_);
v_a_2617_ = lean_ctor_get(v_rx_2599_, 1);
lean_inc(v_a_2617_);
lean_dec_ref_known(v_rx_2599_, 2);
v_a_2618_ = lean_ctor_get(v_ry_2601_, 0);
v_a_2619_ = lean_ctor_get(v_ry_2601_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_ry_2601_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2621_ = v_ry_2601_;
v_isShared_2622_ = v_isSharedCheck_2628_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_inc(v_a_2618_);
lean_dec(v_ry_2601_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2628_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2623_ = lean_apply_2(v_f_2600_, v_a_2616_, v_a_2618_);
v___x_2624_ = l_Lake_JobState_merge(v_a_2617_, v_a_2619_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 1, v___x_2624_);
lean_ctor_set(v___x_2621_, 0, v___x_2623_);
v___x_2626_ = v___x_2621_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
else
{
lean_object* v_a_2629_; 
lean_dec(v_f_2600_);
v_a_2629_ = lean_ctor_get(v_rx_2599_, 1);
lean_inc(v_a_2629_);
lean_dec_ref_known(v_rx_2599_, 2);
v_a_2614_ = v_a_2629_;
goto v___jp_2613_;
}
}
else
{
lean_dec(v_f_2600_);
if (lean_obj_tag(v_rx_2599_) == 0)
{
lean_object* v_a_2630_; 
v_a_2630_ = lean_ctor_get(v_rx_2599_, 1);
lean_inc(v_a_2630_);
lean_dec_ref_known(v_rx_2599_, 2);
v_a_2614_ = v_a_2630_;
goto v___jp_2613_;
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2632_; 
v_a_2631_ = lean_ctor_get(v_rx_2599_, 1);
lean_inc(v_a_2631_);
lean_dec_ref_known(v_rx_2599_, 2);
v___x_2632_ = lean_unsigned_to_nat(0u);
v___y_2609_ = v_ry_2601_;
v___y_2610_ = v___x_2632_;
v___y_2611_ = v_a_2631_;
goto v___jp_2608_;
}
}
v___jp_2602_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2606_ = l_Lake_JobState_merge(v___y_2604_, v___y_2605_);
v___x_2607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___y_2603_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
return v___x_2607_;
}
v___jp_2608_:
{
lean_object* v_a_2612_; 
v_a_2612_ = lean_ctor_get(v___y_2609_, 1);
lean_inc(v_a_2612_);
lean_dec_ref(v___y_2609_);
v___y_2603_ = v___y_2610_;
v___y_2604_ = v___y_2611_;
v___y_2605_ = v_a_2612_;
goto v___jp_2602_;
}
v___jp_2613_:
{
lean_object* v___x_2615_; 
v___x_2615_ = lean_unsigned_to_nat(0u);
v___y_2609_ = v_ry_2601_;
v___y_2610_ = v___x_2615_;
v___y_2611_ = v_a_2614_;
goto v___jp_2608_;
}
}
}
lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object* v_other_2633_, lean_object* v_f_2634_, lean_object* v_prio_2635_, uint8_t v_sync_2636_, lean_object* v_rx_2637_){
_start:
{
lean_object* v_task_2638_; lean_object* v___f_2639_; lean_object* v___x_2640_; 
v_task_2638_ = lean_ctor_get(v_other_2633_, 0);
lean_inc_ref(v_task_2638_);
lean_dec_ref(v_other_2633_);
v___f_2639_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2639_, 0, v_rx_2637_);
lean_closure_set(v___f_2639_, 1, v_f_2634_);
v___x_2640_ = lean_task_map(v___f_2639_, v_task_2638_, v_prio_2635_, v_sync_2636_);
return v___x_2640_;
}
}
LEAN_EXPORT void l_Lake_Job_zipWith___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_other_2633_ = stack[0].m_obj;
lean_object* v_f_2634_ = stack[1].m_obj;
lean_object* v_prio_2635_ = stack[2].m_obj;
uint8_t v_sync_2636_ = stack[3].m_num;
lean_object* v_rx_2637_ = stack[4].m_obj;
lean_object* v_res_2641_;
v_res_2641_ = l_Lake_Job_zipWith___redArg___lam__1(v_other_2633_, v_f_2634_, v_prio_2635_, v_sync_2636_, v_rx_2637_);
stack->m_obj
 = v_res_2641_;
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object* v_other_2642_, lean_object* v_f_2643_, lean_object* v_prio_2644_, lean_object* v_sync_2645_, lean_object* v_rx_2646_){
_start:
{
uint8_t v_sync_boxed_2647_; lean_object* v_res_2648_; 
v_sync_boxed_2647_ = lean_unbox(v_sync_2645_);
v_res_2648_ = l_Lake_Job_zipWith___redArg___lam__1(v_other_2642_, v_f_2643_, v_prio_2644_, v_sync_boxed_2647_, v_rx_2646_);
return v_res_2648_;
}
}
lean_object* l_Lake_Job_zipWith___redArg(lean_object* v_inst_2649_, lean_object* v_f_2650_, lean_object* v_self_2651_, lean_object* v_other_2652_, lean_object* v_prio_2653_, uint8_t v_sync_2654_){
_start:
{
lean_object* v_task_2655_; lean_object* v___x_2657_; uint8_t v_isShared_2658_; uint8_t v_isSharedCheck_2668_; 
v_task_2655_ = lean_ctor_get(v_self_2651_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v_self_2651_);
if (v_isSharedCheck_2668_ == 0)
{
lean_object* v_unused_2669_; lean_object* v_unused_2670_; 
v_unused_2669_ = lean_ctor_get(v_self_2651_, 2);
lean_dec(v_unused_2669_);
v_unused_2670_ = lean_ctor_get(v_self_2651_, 1);
lean_dec(v_unused_2670_);
v___x_2657_ = v_self_2651_;
v_isShared_2658_ = v_isSharedCheck_2668_;
goto v_resetjp_2656_;
}
else
{
lean_inc(v_task_2655_);
lean_dec(v_self_2651_);
v___x_2657_ = lean_box(0);
v_isShared_2658_ = v_isSharedCheck_2668_;
goto v_resetjp_2656_;
}
v_resetjp_2656_:
{
lean_object* v___x_2659_; lean_object* v___f_2660_; uint8_t v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; lean_object* v___x_2666_; 
v___x_2659_ = lean_box(v_sync_2654_);
lean_inc(v_prio_2653_);
v___f_2660_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2660_, 0, v_other_2652_);
lean_closure_set(v___f_2660_, 1, v_f_2650_);
lean_closure_set(v___f_2660_, 2, v_prio_2653_);
lean_closure_set(v___f_2660_, 3, v___x_2659_);
v___x_2661_ = 1;
v___x_2662_ = lean_task_bind(v_task_2655_, v___f_2660_, v_prio_2653_, v___x_2661_);
v___x_2663_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2664_ = 0;
if (v_isShared_2658_ == 0)
{
lean_ctor_set(v___x_2657_, 2, v___x_2663_);
lean_ctor_set(v___x_2657_, 1, v_inst_2649_);
lean_ctor_set(v___x_2657_, 0, v___x_2662_);
v___x_2666_ = v___x_2657_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2662_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_inst_2649_);
lean_ctor_set(v_reuseFailAlloc_2667_, 2, v___x_2663_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
lean_ctor_set_uint8(v___x_2666_, sizeof(void*)*3, v___x_2664_);
return v___x_2666_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_zipWith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2649_ = stack[0].m_obj;
lean_object* v_f_2650_ = stack[1].m_obj;
lean_object* v_self_2651_ = stack[2].m_obj;
lean_object* v_other_2652_ = stack[3].m_obj;
lean_object* v_prio_2653_ = stack[4].m_obj;
uint8_t v_sync_2654_ = stack[5].m_num;
lean_object* v_res_2671_;
v_res_2671_ = l_Lake_Job_zipWith___redArg(v_inst_2649_, v_f_2650_, v_self_2651_, v_other_2652_, v_prio_2653_, v_sync_2654_);
stack->m_obj
 = v_res_2671_;
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object* v_inst_2672_, lean_object* v_f_2673_, lean_object* v_self_2674_, lean_object* v_other_2675_, lean_object* v_prio_2676_, lean_object* v_sync_2677_){
_start:
{
uint8_t v_sync_boxed_2678_; lean_object* v_res_2679_; 
v_sync_boxed_2678_ = lean_unbox(v_sync_2677_);
v_res_2679_ = l_Lake_Job_zipWith___redArg(v_inst_2672_, v_f_2673_, v_self_2674_, v_other_2675_, v_prio_2676_, v_sync_boxed_2678_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__0(lean_object* v_rx_2680_, lean_object* v_f_2681_, lean_object* v_ry_2682_){
_start:
{
lean_object* v___y_2684_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v___y_2690_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v_a_2695_; lean_object* v_rb_2696_; 
if (lean_obj_tag(v_rx_2680_) == 0)
{
if (lean_obj_tag(v_ry_2682_) == 0)
{
lean_object* v_a_2698_; lean_object* v_a_2699_; lean_object* v_a_2700_; lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2710_; 
v_a_2698_ = lean_ctor_get(v_rx_2680_, 0);
lean_inc(v_a_2698_);
v_a_2699_ = lean_ctor_get(v_rx_2680_, 1);
lean_inc(v_a_2699_);
lean_dec_ref_known(v_rx_2680_, 2);
v_a_2700_ = lean_ctor_get(v_ry_2682_, 0);
v_a_2701_ = lean_ctor_get(v_ry_2682_, 1);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_ry_2682_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2703_ = v_ry_2682_;
v_isShared_2704_ = v_isSharedCheck_2710_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_inc(v_a_2700_);
lean_dec(v_ry_2682_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2710_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2708_; 
v___x_2705_ = lean_apply_2(v_f_2681_, v_a_2698_, v_a_2700_);
v___x_2706_ = l_Lake_JobState_merge(v_a_2699_, v_a_2701_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 1, v___x_2706_);
lean_ctor_set(v___x_2703_, 0, v___x_2705_);
v___x_2708_ = v___x_2703_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2705_);
lean_ctor_set(v_reuseFailAlloc_2709_, 1, v___x_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
else
{
lean_object* v_a_2711_; 
lean_dec(v_f_2681_);
v_a_2711_ = lean_ctor_get(v_rx_2680_, 1);
lean_inc(v_a_2711_);
lean_dec_ref_known(v_rx_2680_, 2);
v_a_2695_ = v_a_2711_;
v_rb_2696_ = v_ry_2682_;
goto v___jp_2694_;
}
}
else
{
lean_dec(v_f_2681_);
if (lean_obj_tag(v_rx_2680_) == 0)
{
lean_object* v_a_2712_; 
v_a_2712_ = lean_ctor_get(v_rx_2680_, 1);
lean_inc(v_a_2712_);
lean_dec_ref_known(v_rx_2680_, 2);
v_a_2695_ = v_a_2712_;
v_rb_2696_ = v_ry_2682_;
goto v___jp_2694_;
}
else
{
lean_object* v_a_2713_; lean_object* v___x_2714_; 
v_a_2713_ = lean_ctor_get(v_rx_2680_, 1);
lean_inc(v_a_2713_);
lean_dec_ref_known(v_rx_2680_, 2);
v___x_2714_ = lean_unsigned_to_nat(0u);
v___y_2690_ = v_ry_2682_;
v___y_2691_ = v___x_2714_;
v___y_2692_ = v_a_2713_;
goto v___jp_2689_;
}
}
v___jp_2683_:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; 
v___x_2687_ = l_Lake_JobState_merge(v___y_2685_, v___y_2686_);
v___x_2688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2688_, 0, v___y_2684_);
lean_ctor_set(v___x_2688_, 1, v___x_2687_);
return v___x_2688_;
}
v___jp_2689_:
{
lean_object* v_a_2693_; 
v_a_2693_ = lean_ctor_get(v___y_2690_, 1);
lean_inc(v_a_2693_);
lean_dec_ref(v___y_2690_);
v___y_2684_ = v___y_2691_;
v___y_2685_ = v___y_2692_;
v___y_2686_ = v_a_2693_;
goto v___jp_2683_;
}
v___jp_2694_:
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_unsigned_to_nat(0u);
v___y_2690_ = v_rb_2696_;
v___y_2691_ = v___x_2697_;
v___y_2692_ = v_a_2695_;
goto v___jp_2689_;
}
}
}
lean_object* l_Lake_Job_zipWith___lam__1(lean_object* v_other_2715_, lean_object* v_f_2716_, lean_object* v_prio_2717_, uint8_t v_sync_2718_, lean_object* v_rx_2719_){
_start:
{
lean_object* v_task_2720_; lean_object* v___f_2721_; lean_object* v___x_2722_; 
v_task_2720_ = lean_ctor_get(v_other_2715_, 0);
lean_inc_ref(v_task_2720_);
lean_dec_ref(v_other_2715_);
v___f_2721_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__0), 3, 2);
lean_closure_set(v___f_2721_, 0, v_rx_2719_);
lean_closure_set(v___f_2721_, 1, v_f_2716_);
v___x_2722_ = lean_task_map(v___f_2721_, v_task_2720_, v_prio_2717_, v_sync_2718_);
return v___x_2722_;
}
}
LEAN_EXPORT void l_Lake_Job_zipWith___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_other_2715_ = stack[0].m_obj;
lean_object* v_f_2716_ = stack[1].m_obj;
lean_object* v_prio_2717_ = stack[2].m_obj;
uint8_t v_sync_2718_ = stack[3].m_num;
lean_object* v_rx_2719_ = stack[4].m_obj;
lean_object* v_res_2723_;
v_res_2723_ = l_Lake_Job_zipWith___lam__1(v_other_2715_, v_f_2716_, v_prio_2717_, v_sync_2718_, v_rx_2719_);
stack->m_obj
 = v_res_2723_;
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1___boxed(lean_object* v_other_2724_, lean_object* v_f_2725_, lean_object* v_prio_2726_, lean_object* v_sync_2727_, lean_object* v_rx_2728_){
_start:
{
uint8_t v_sync_boxed_2729_; lean_object* v_res_2730_; 
v_sync_boxed_2729_ = lean_unbox(v_sync_2727_);
v_res_2730_ = l_Lake_Job_zipWith___lam__1(v_other_2724_, v_f_2725_, v_prio_2726_, v_sync_boxed_2729_, v_rx_2728_);
return v_res_2730_;
}
}
lean_object* l_Lake_Job_zipWith(lean_object* v_00_u03b3_2731_, lean_object* v_00_u03b1_2732_, lean_object* v_00_u03b2_2733_, lean_object* v_inst_2734_, lean_object* v_f_2735_, lean_object* v_self_2736_, lean_object* v_other_2737_, lean_object* v_prio_2738_, uint8_t v_sync_2739_){
_start:
{
lean_object* v_task_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2753_; 
v_task_2740_ = lean_ctor_get(v_self_2736_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_self_2736_);
if (v_isSharedCheck_2753_ == 0)
{
lean_object* v_unused_2754_; lean_object* v_unused_2755_; 
v_unused_2754_ = lean_ctor_get(v_self_2736_, 2);
lean_dec(v_unused_2754_);
v_unused_2755_ = lean_ctor_get(v_self_2736_, 1);
lean_dec(v_unused_2755_);
v___x_2742_ = v_self_2736_;
v_isShared_2743_ = v_isSharedCheck_2753_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_task_2740_);
lean_dec(v_self_2736_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2753_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2744_; lean_object* v___f_2745_; uint8_t v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; uint8_t v___x_2749_; lean_object* v___x_2751_; 
v___x_2744_ = lean_box(v_sync_2739_);
lean_inc(v_prio_2738_);
v___f_2745_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2745_, 0, v_other_2737_);
lean_closure_set(v___f_2745_, 1, v_f_2735_);
lean_closure_set(v___f_2745_, 2, v_prio_2738_);
lean_closure_set(v___f_2745_, 3, v___x_2744_);
v___x_2746_ = 1;
v___x_2747_ = lean_task_bind(v_task_2740_, v___f_2745_, v_prio_2738_, v___x_2746_);
v___x_2748_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2749_ = 0;
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 2, v___x_2748_);
lean_ctor_set(v___x_2742_, 1, v_inst_2734_);
lean_ctor_set(v___x_2742_, 0, v___x_2747_);
v___x_2751_ = v___x_2742_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2747_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_inst_2734_);
lean_ctor_set(v_reuseFailAlloc_2752_, 2, v___x_2748_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
lean_ctor_set_uint8(v___x_2751_, sizeof(void*)*3, v___x_2749_);
return v___x_2751_;
}
}
}
}
LEAN_EXPORT void l_Lake_Job_zipWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_2734_ = stack[3].m_obj;
lean_object* v_f_2735_ = stack[4].m_obj;
lean_object* v_self_2736_ = stack[5].m_obj;
lean_object* v_other_2737_ = stack[6].m_obj;
lean_object* v_prio_2738_ = stack[7].m_obj;
uint8_t v_sync_2739_ = stack[8].m_num;
lean_object* v_res_2756_;
v_res_2756_ = l_Lake_Job_zipWith(lean_box(0), lean_box(0), lean_box(0), v_inst_2734_, v_f_2735_, v_self_2736_, v_other_2737_, v_prio_2738_, v_sync_2739_);
stack->m_obj
 = v_res_2756_;
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object* v_00_u03b3_2757_, lean_object* v_00_u03b1_2758_, lean_object* v_00_u03b2_2759_, lean_object* v_inst_2760_, lean_object* v_f_2761_, lean_object* v_self_2762_, lean_object* v_other_2763_, lean_object* v_prio_2764_, lean_object* v_sync_2765_){
_start:
{
uint8_t v_sync_boxed_2766_; lean_object* v_res_2767_; 
v_sync_boxed_2766_ = lean_unbox(v_sync_2765_);
v_res_2767_ = l_Lake_Job_zipWith(v_00_u03b3_2757_, v_00_u03b1_2758_, v_00_u03b2_2759_, v_inst_2760_, v_f_2761_, v_self_2762_, v_other_2763_, v_prio_2764_, v_sync_boxed_2766_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object* v___x_2768_, lean_object* v_rx_2769_, lean_object* v_ry_2770_){
_start:
{
lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2792_; lean_object* v___y_2793_; 
if (lean_obj_tag(v_rx_2769_) == 0)
{
if (lean_obj_tag(v_ry_2770_) == 0)
{
lean_object* v_a_2795_; lean_object* v_a_2796_; lean_object* v_a_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2820_; 
lean_dec(v___x_2768_);
v_a_2795_ = lean_ctor_get(v_rx_2769_, 0);
lean_inc(v_a_2795_);
v_a_2796_ = lean_ctor_get(v_rx_2769_, 1);
lean_inc(v_a_2796_);
lean_dec_ref_known(v_rx_2769_, 2);
v_a_2797_ = lean_ctor_get(v_ry_2770_, 1);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_ry_2770_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; 
v_unused_2821_ = lean_ctor_get(v_ry_2770_, 0);
lean_dec(v_unused_2821_);
v___x_2799_ = v_ry_2770_;
v_isShared_2800_ = v_isSharedCheck_2820_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_a_2797_);
lean_dec(v_ry_2770_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2820_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v_log_2802_; uint8_t v_action_2803_; uint8_t v_wantsRebuild_2804_; uint8_t v_canceled_2805_; lean_object* v_buildTime_2806_; lean_object* v_trace_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2817_; 
lean_inc(v_a_2796_);
v___x_2801_ = l_Lake_JobState_merge(v_a_2796_, v_a_2797_);
v_log_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc_ref(v_log_2802_);
v_action_2803_ = lean_ctor_get_uint8(v___x_2801_, sizeof(void*)*3);
v_wantsRebuild_2804_ = lean_ctor_get_uint8(v___x_2801_, sizeof(void*)*3 + 1);
v_canceled_2805_ = lean_ctor_get_uint8(v___x_2801_, sizeof(void*)*3 + 2);
v_buildTime_2806_ = lean_ctor_get(v___x_2801_, 2);
lean_inc(v_buildTime_2806_);
lean_dec_ref(v___x_2801_);
v_trace_2807_ = lean_ctor_get(v_a_2796_, 1);
v_isSharedCheck_2817_ = !lean_is_exclusive(v_a_2796_);
if (v_isSharedCheck_2817_ == 0)
{
lean_object* v_unused_2818_; lean_object* v_unused_2819_; 
v_unused_2818_ = lean_ctor_get(v_a_2796_, 2);
lean_dec(v_unused_2818_);
v_unused_2819_ = lean_ctor_get(v_a_2796_, 0);
lean_dec(v_unused_2819_);
v___x_2809_ = v_a_2796_;
v_isShared_2810_ = v_isSharedCheck_2817_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_trace_2807_);
lean_dec(v_a_2796_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2817_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2812_; 
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 2, v_buildTime_2806_);
lean_ctor_set(v___x_2809_, 0, v_log_2802_);
v___x_2812_ = v___x_2809_;
goto v_reusejp_2811_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_log_2802_);
lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_trace_2807_);
lean_ctor_set(v_reuseFailAlloc_2816_, 2, v_buildTime_2806_);
v___x_2812_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2811_;
}
v_reusejp_2811_:
{
lean_object* v___x_2814_; 
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*3, v_action_2803_);
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*3 + 1, v_wantsRebuild_2804_);
lean_ctor_set_uint8(v___x_2812_, sizeof(void*)*3 + 2, v_canceled_2805_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 1, v___x_2812_);
lean_ctor_set(v___x_2799_, 0, v_a_2795_);
v___x_2814_ = v___x_2799_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2795_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v___x_2812_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
else
{
lean_object* v_a_2822_; 
v_a_2822_ = lean_ctor_get(v_rx_2769_, 1);
lean_inc(v_a_2822_);
lean_dec_ref_known(v_rx_2769_, 2);
v___y_2792_ = v_ry_2770_;
v___y_2793_ = v_a_2822_;
goto v___jp_2791_;
}
}
else
{
lean_object* v_a_2823_; 
v_a_2823_ = lean_ctor_get(v_rx_2769_, 1);
lean_inc(v_a_2823_);
lean_dec_ref(v_rx_2769_);
v___y_2792_ = v_ry_2770_;
v___y_2793_ = v_a_2823_;
goto v___jp_2791_;
}
v___jp_2771_:
{
lean_object* v___x_2774_; lean_object* v_log_2775_; uint8_t v_action_2776_; uint8_t v_wantsRebuild_2777_; uint8_t v_canceled_2778_; lean_object* v_buildTime_2779_; lean_object* v_trace_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2788_; 
lean_inc_ref(v___y_2772_);
v___x_2774_ = l_Lake_JobState_merge(v___y_2772_, v___y_2773_);
v_log_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc_ref(v_log_2775_);
v_action_2776_ = lean_ctor_get_uint8(v___x_2774_, sizeof(void*)*3);
v_wantsRebuild_2777_ = lean_ctor_get_uint8(v___x_2774_, sizeof(void*)*3 + 1);
v_canceled_2778_ = lean_ctor_get_uint8(v___x_2774_, sizeof(void*)*3 + 2);
v_buildTime_2779_ = lean_ctor_get(v___x_2774_, 2);
lean_inc(v_buildTime_2779_);
lean_dec_ref(v___x_2774_);
v_trace_2780_ = lean_ctor_get(v___y_2772_, 1);
v_isSharedCheck_2788_ = !lean_is_exclusive(v___y_2772_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; lean_object* v_unused_2790_; 
v_unused_2789_ = lean_ctor_get(v___y_2772_, 2);
lean_dec(v_unused_2789_);
v_unused_2790_ = lean_ctor_get(v___y_2772_, 0);
lean_dec(v_unused_2790_);
v___x_2782_ = v___y_2772_;
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_trace_2780_);
lean_dec(v___y_2772_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2788_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
lean_ctor_set(v___x_2782_, 2, v_buildTime_2779_);
lean_ctor_set(v___x_2782_, 0, v_log_2775_);
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_log_2775_);
lean_ctor_set(v_reuseFailAlloc_2787_, 1, v_trace_2780_);
lean_ctor_set(v_reuseFailAlloc_2787_, 2, v_buildTime_2779_);
v___x_2785_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
lean_object* v___x_2786_; 
lean_ctor_set_uint8(v___x_2785_, sizeof(void*)*3, v_action_2776_);
lean_ctor_set_uint8(v___x_2785_, sizeof(void*)*3 + 1, v_wantsRebuild_2777_);
lean_ctor_set_uint8(v___x_2785_, sizeof(void*)*3 + 2, v_canceled_2778_);
v___x_2786_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2768_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
return v___x_2786_;
}
}
}
v___jp_2791_:
{
lean_object* v_a_2794_; 
v_a_2794_ = lean_ctor_get(v___y_2792_, 1);
lean_inc(v_a_2794_);
lean_dec_ref(v___y_2792_);
v___y_2772_ = v___y_2793_;
v___y_2773_ = v_a_2794_;
goto v___jp_2771_;
}
}
}
lean_object* l_Lake_Job_add___redArg___lam__1(lean_object* v_other_2824_, lean_object* v___x_2825_, uint8_t v___x_2826_, lean_object* v_rx_2827_){
_start:
{
lean_object* v_task_2828_; lean_object* v___f_2829_; lean_object* v___x_2830_; 
v_task_2828_ = lean_ctor_get(v_other_2824_, 0);
lean_inc_ref(v_task_2828_);
lean_dec_ref(v_other_2824_);
lean_inc(v___x_2825_);
v___f_2829_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2829_, 0, v___x_2825_);
lean_closure_set(v___f_2829_, 1, v_rx_2827_);
v___x_2830_ = lean_task_map(v___f_2829_, v_task_2828_, v___x_2825_, v___x_2826_);
return v___x_2830_;
}
}
LEAN_EXPORT void l_Lake_Job_add___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_other_2824_ = stack[0].m_obj;
lean_object* v___x_2825_ = stack[1].m_obj;
uint8_t v___x_2826_ = stack[2].m_num;
lean_object* v_rx_2827_ = stack[3].m_obj;
lean_object* v_res_2831_;
v_res_2831_ = l_Lake_Job_add___redArg___lam__1(v_other_2824_, v___x_2825_, v___x_2826_, v_rx_2827_);
stack->m_obj
 = v_res_2831_;
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object* v_other_2832_, lean_object* v___x_2833_, lean_object* v___x_2834_, lean_object* v_rx_2835_){
_start:
{
uint8_t v___x_300__boxed_2836_; lean_object* v_res_2837_; 
v___x_300__boxed_2836_ = lean_unbox(v___x_2834_);
v_res_2837_ = l_Lake_Job_add___redArg___lam__1(v_other_2832_, v___x_2833_, v___x_300__boxed_2836_, v_rx_2835_);
return v_res_2837_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object* v_self_2838_, lean_object* v_other_2839_){
_start:
{
lean_object* v_task_2840_; lean_object* v_kind_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2855_; 
v_task_2840_ = lean_ctor_get(v_self_2838_, 0);
v_kind_2841_ = lean_ctor_get(v_self_2838_, 1);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_self_2838_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v_self_2838_, 2);
lean_dec(v_unused_2856_);
v___x_2843_ = v_self_2838_;
v_isShared_2844_ = v_isSharedCheck_2855_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_kind_2841_);
lean_inc(v_task_2840_);
lean_dec(v_self_2838_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2855_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; uint8_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___f_2848_; uint8_t v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
v___x_2845_ = lean_unsigned_to_nat(0u);
v___x_2846_ = 0;
v___x_2847_ = lean_box(v___x_2846_);
v___f_2848_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2848_, 0, v_other_2839_);
lean_closure_set(v___f_2848_, 1, v___x_2845_);
lean_closure_set(v___f_2848_, 2, v___x_2847_);
v___x_2849_ = 1;
v___x_2850_ = lean_task_bind(v_task_2840_, v___f_2848_, v___x_2845_, v___x_2849_);
v___x_2851_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 2, v___x_2851_);
lean_ctor_set(v___x_2843_, 0, v___x_2850_);
v___x_2853_ = v___x_2843_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2850_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_kind_2841_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v___x_2851_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_ctor_set_uint8(v___x_2853_, sizeof(void*)*3, v___x_2846_);
return v___x_2853_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object* v_00_u03b1_2857_, lean_object* v_00_u03b2_2858_, lean_object* v_self_2859_, lean_object* v_other_2860_){
_start:
{
lean_object* v___x_2861_; 
v___x_2861_ = l_Lake_Job_add___redArg(v_self_2859_, v_other_2860_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object* v___x_2862_, lean_object* v_rx_2863_, lean_object* v_ry_2864_){
_start:
{
lean_object* v___y_2866_; lean_object* v___y_2867_; lean_object* v___y_2871_; lean_object* v___y_2872_; 
if (lean_obj_tag(v_rx_2863_) == 0)
{
if (lean_obj_tag(v_ry_2864_) == 0)
{
lean_object* v_a_2874_; lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2884_; 
lean_dec(v___x_2862_);
v_a_2874_ = lean_ctor_get(v_rx_2863_, 1);
lean_inc(v_a_2874_);
lean_dec_ref_known(v_rx_2863_, 2);
v_a_2875_ = lean_ctor_get(v_ry_2864_, 1);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_ry_2864_);
if (v_isSharedCheck_2884_ == 0)
{
lean_object* v_unused_2885_; 
v_unused_2885_ = lean_ctor_get(v_ry_2864_, 0);
lean_dec(v_unused_2885_);
v___x_2877_ = v_ry_2864_;
v_isShared_2878_ = v_isSharedCheck_2884_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v_ry_2864_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2884_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2882_; 
v___x_2879_ = lean_box(0);
v___x_2880_ = l_Lake_JobState_merge(v_a_2874_, v_a_2875_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 1, v___x_2880_);
lean_ctor_set(v___x_2877_, 0, v___x_2879_);
v___x_2882_ = v___x_2877_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2879_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
else
{
lean_object* v_a_2886_; 
v_a_2886_ = lean_ctor_get(v_rx_2863_, 1);
lean_inc(v_a_2886_);
lean_dec_ref_known(v_rx_2863_, 2);
v___y_2871_ = v_ry_2864_;
v___y_2872_ = v_a_2886_;
goto v___jp_2870_;
}
}
else
{
lean_object* v_a_2887_; 
v_a_2887_ = lean_ctor_get(v_rx_2863_, 1);
lean_inc(v_a_2887_);
lean_dec_ref(v_rx_2863_);
v___y_2871_ = v_ry_2864_;
v___y_2872_ = v_a_2887_;
goto v___jp_2870_;
}
v___jp_2865_:
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2868_ = l_Lake_JobState_merge(v___y_2866_, v___y_2867_);
v___x_2869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2862_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
return v___x_2869_;
}
v___jp_2870_:
{
lean_object* v_a_2873_; 
v_a_2873_ = lean_ctor_get(v___y_2871_, 1);
lean_inc(v_a_2873_);
lean_dec_ref(v___y_2871_);
v___y_2866_ = v___y_2872_;
v___y_2867_ = v_a_2873_;
goto v___jp_2865_;
}
}
}
lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object* v_other_2888_, lean_object* v___x_2889_, uint8_t v___x_2890_, lean_object* v_rx_2891_){
_start:
{
lean_object* v_task_2892_; lean_object* v___f_2893_; lean_object* v___x_2894_; 
v_task_2892_ = lean_ctor_get(v_other_2888_, 0);
lean_inc_ref(v_task_2892_);
lean_dec_ref(v_other_2888_);
lean_inc(v___x_2889_);
v___f_2893_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2893_, 0, v___x_2889_);
lean_closure_set(v___f_2893_, 1, v_rx_2891_);
v___x_2894_ = lean_task_map(v___f_2893_, v_task_2892_, v___x_2889_, v___x_2890_);
return v___x_2894_;
}
}
LEAN_EXPORT void l_Lake_Job_mix___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_other_2888_ = stack[0].m_obj;
lean_object* v___x_2889_ = stack[1].m_obj;
uint8_t v___x_2890_ = stack[2].m_num;
lean_object* v_rx_2891_ = stack[3].m_obj;
lean_object* v_res_2895_;
v_res_2895_ = l_Lake_Job_mix___redArg___lam__1(v_other_2888_, v___x_2889_, v___x_2890_, v_rx_2891_);
stack->m_obj
 = v_res_2895_;
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object* v_other_2896_, lean_object* v___x_2897_, lean_object* v___x_2898_, lean_object* v_rx_2899_){
_start:
{
uint8_t v___x_166__boxed_2900_; lean_object* v_res_2901_; 
v___x_166__boxed_2900_ = lean_unbox(v___x_2898_);
v_res_2901_ = l_Lake_Job_mix___redArg___lam__1(v_other_2896_, v___x_2897_, v___x_166__boxed_2900_, v_rx_2899_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object* v_self_2902_, lean_object* v_other_2903_){
_start:
{
lean_object* v_task_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2919_; 
v_task_2904_ = lean_ctor_get(v_self_2902_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_self_2902_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; lean_object* v_unused_2921_; 
v_unused_2920_ = lean_ctor_get(v_self_2902_, 2);
lean_dec(v_unused_2920_);
v_unused_2921_ = lean_ctor_get(v_self_2902_, 1);
lean_dec(v_unused_2921_);
v___x_2906_ = v_self_2902_;
v_isShared_2907_ = v_isSharedCheck_2919_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_task_2904_);
lean_dec(v_self_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2919_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; lean_object* v___x_2911_; lean_object* v___f_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; uint8_t v___x_2915_; lean_object* v___x_2917_; 
v___x_2908_ = l_Lake_instDataKindUnit;
v___x_2909_ = lean_unsigned_to_nat(0u);
v___x_2910_ = 1;
v___x_2911_ = lean_box(v___x_2910_);
v___f_2912_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2912_, 0, v_other_2903_);
lean_closure_set(v___f_2912_, 1, v___x_2909_);
lean_closure_set(v___f_2912_, 2, v___x_2911_);
v___x_2913_ = lean_task_bind(v_task_2904_, v___f_2912_, v___x_2909_, v___x_2910_);
v___x_2914_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2915_ = 0;
if (v_isShared_2907_ == 0)
{
lean_ctor_set(v___x_2906_, 2, v___x_2914_);
lean_ctor_set(v___x_2906_, 1, v___x_2908_);
lean_ctor_set(v___x_2906_, 0, v___x_2913_);
v___x_2917_ = v___x_2906_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2913_);
lean_ctor_set(v_reuseFailAlloc_2918_, 1, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2918_, 2, v___x_2914_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
lean_ctor_set_uint8(v___x_2917_, sizeof(void*)*3, v___x_2915_);
return v___x_2917_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object* v_00_u03b1_2922_, lean_object* v_00_u03b2_2923_, lean_object* v_self_2924_, lean_object* v_other_2925_){
_start:
{
lean_object* v___x_2926_; 
v___x_2926_ = l_Lake_Job_mix___redArg(v_self_2924_, v_other_2925_);
return v___x_2926_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(lean_object* v_as_2927_, size_t v_i_2928_, size_t v_stop_2929_, lean_object* v_b_2930_){
_start:
{
uint8_t v___x_2931_; 
v___x_2931_ = lean_usize_dec_eq(v_i_2928_, v_stop_2929_);
if (v___x_2931_ == 0)
{
size_t v___x_2932_; size_t v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2932_ = ((size_t)1ULL);
v___x_2933_ = lean_usize_sub(v_i_2928_, v___x_2932_);
v___x_2934_ = lean_array_uget_borrowed(v_as_2927_, v___x_2933_);
lean_inc(v___x_2934_);
v___x_2935_ = l_Lake_Job_mix___redArg(v___x_2934_, v_b_2930_);
v_i_2928_ = v___x_2933_;
v_b_2930_ = v___x_2935_;
goto _start;
}
else
{
return v_b_2930_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2927_ = stack[0].m_obj;
size_t v_i_2928_ = stack[1].m_num;
size_t v_stop_2929_ = stack[2].m_num;
lean_object* v_b_2930_ = stack[3].m_obj;
lean_object* v_res_2937_;
v_res_2937_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2927_, v_i_2928_, v_stop_2929_, v_b_2930_);
stack->m_obj
 = v_res_2937_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2938_, lean_object* v_i_2939_, lean_object* v_stop_2940_, lean_object* v_b_2941_){
_start:
{
size_t v_i_boxed_2942_; size_t v_stop_boxed_2943_; lean_object* v_res_2944_; 
v_i_boxed_2942_ = lean_unbox_usize(v_i_2939_);
lean_dec(v_i_2939_);
v_stop_boxed_2943_ = lean_unbox_usize(v_stop_2940_);
lean_dec(v_stop_2940_);
v_res_2944_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2938_, v_i_boxed_2942_, v_stop_boxed_2943_, v_b_2941_);
lean_dec_ref(v_as_2938_);
return v_res_2944_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(lean_object* v_init_2945_, lean_object* v_l_2946_){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v___x_2947_ = lean_array_mk(v_l_2946_);
v___x_2948_ = lean_array_get_size(v___x_2947_);
v___x_2949_ = lean_unsigned_to_nat(0u);
v___x_2950_ = lean_nat_dec_lt(v___x_2949_, v___x_2948_);
if (v___x_2950_ == 0)
{
lean_dec_ref(v___x_2947_);
return v_init_2945_;
}
else
{
size_t v___x_2951_; size_t v___x_2952_; lean_object* v___x_2953_; 
v___x_2951_ = lean_usize_of_nat(v___x_2948_);
v___x_2952_ = ((size_t)0ULL);
v___x_2953_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v___x_2947_, v___x_2951_, v___x_2952_, v_init_2945_);
lean_dec_ref(v___x_2947_);
return v___x_2953_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object* v_jobs_2954_, lean_object* v_traceCaption_2955_){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; uint8_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2956_ = lean_box(0);
v___x_2957_ = lean_box(0);
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2960_ = 0;
v___x_2961_ = 0;
v___x_2962_ = l_Lake_BuildTrace_nil(v_traceCaption_2955_);
v___x_2963_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_2963_, 0, v___x_2959_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
lean_ctor_set(v___x_2963_, 2, v___x_2958_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*3, v___x_2960_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*3 + 1, v___x_2961_);
lean_ctor_set_uint8(v___x_2963_, sizeof(void*)*3 + 2, v___x_2961_);
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2956_);
lean_ctor_set(v___x_2964_, 1, v___x_2963_);
v___x_2965_ = lean_task_pure(v___x_2964_);
v___x_2966_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2967_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2967_, 0, v___x_2965_);
lean_ctor_set(v___x_2967_, 1, v___x_2957_);
lean_ctor_set(v___x_2967_, 2, v___x_2966_);
lean_ctor_set_uint8(v___x_2967_, sizeof(void*)*3, v___x_2961_);
v___x_2968_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v___x_2967_, v_jobs_2954_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object* v_00_u03b1_2969_, lean_object* v_jobs_2970_, lean_object* v_traceCaption_2971_){
_start:
{
lean_object* v___x_2972_; 
v___x_2972_ = l_Lake_Job_mixList___redArg(v_jobs_2970_, v_traceCaption_2971_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0(lean_object* v_00_u03b1_2973_, lean_object* v_init_2974_, lean_object* v_l_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v_init_2974_, v_l_2975_);
return v___x_2976_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(lean_object* v_00_u03b1_2977_, lean_object* v_as_2978_, size_t v_i_2979_, size_t v_stop_2980_, lean_object* v_b_2981_){
_start:
{
lean_object* v___x_2982_; 
v___x_2982_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2978_, v_i_2979_, v_stop_2980_, v_b_2981_);
return v___x_2982_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2978_ = stack[1].m_obj;
size_t v_i_2979_ = stack[2].m_num;
size_t v_stop_2980_ = stack[3].m_num;
lean_object* v_b_2981_ = stack[4].m_obj;
lean_object* v_res_2983_;
v_res_2983_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(lean_box(0), v_as_2978_, v_i_2979_, v_stop_2980_, v_b_2981_);
stack->m_obj
 = v_res_2983_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2984_, lean_object* v_as_2985_, lean_object* v_i_2986_, lean_object* v_stop_2987_, lean_object* v_b_2988_){
_start:
{
size_t v_i_boxed_2989_; size_t v_stop_boxed_2990_; lean_object* v_res_2991_; 
v_i_boxed_2989_ = lean_unbox_usize(v_i_2986_);
lean_dec(v_i_2986_);
v_stop_boxed_2990_ = lean_unbox_usize(v_stop_2987_);
lean_dec(v_stop_2987_);
v_res_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(v_00_u03b1_2984_, v_as_2985_, v_i_boxed_2989_, v_stop_boxed_2990_, v_b_2988_);
lean_dec_ref(v_as_2985_);
return v_res_2991_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(lean_object* v_as_2992_, size_t v_i_2993_, size_t v_stop_2994_, lean_object* v_b_2995_){
_start:
{
uint8_t v___x_2996_; 
v___x_2996_ = lean_usize_dec_eq(v_i_2993_, v_stop_2994_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; size_t v___x_2999_; size_t v___x_3000_; 
v___x_2997_ = lean_array_uget_borrowed(v_as_2992_, v_i_2993_);
lean_inc(v___x_2997_);
v___x_2998_ = l_Lake_Job_mix___redArg(v_b_2995_, v___x_2997_);
v___x_2999_ = ((size_t)1ULL);
v___x_3000_ = lean_usize_add(v_i_2993_, v___x_2999_);
v_i_2993_ = v___x_3000_;
v_b_2995_ = v___x_2998_;
goto _start;
}
else
{
return v_b_2995_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2992_ = stack[0].m_obj;
size_t v_i_2993_ = stack[1].m_num;
size_t v_stop_2994_ = stack[2].m_num;
lean_object* v_b_2995_ = stack[3].m_obj;
lean_object* v_res_3002_;
v_res_3002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2992_, v_i_2993_, v_stop_2994_, v_b_2995_);
stack->m_obj
 = v_res_3002_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg___boxed(lean_object* v_as_3003_, lean_object* v_i_3004_, lean_object* v_stop_3005_, lean_object* v_b_3006_){
_start:
{
size_t v_i_boxed_3007_; size_t v_stop_boxed_3008_; lean_object* v_res_3009_; 
v_i_boxed_3007_ = lean_unbox_usize(v_i_3004_);
lean_dec(v_i_3004_);
v_stop_boxed_3008_ = lean_unbox_usize(v_stop_3005_);
lean_dec(v_stop_3005_);
v_res_3009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_3003_, v_i_boxed_3007_, v_stop_boxed_3008_, v_b_3006_);
lean_dec_ref(v_as_3003_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object* v_jobs_3010_, lean_object* v_traceCaption_3011_){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v___x_3012_ = lean_box(0);
v___x_3013_ = lean_box(0);
v___x_3014_ = lean_unsigned_to_nat(0u);
v___x_3015_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3016_ = 0;
v___x_3017_ = 0;
v___x_3018_ = l_Lake_BuildTrace_nil(v_traceCaption_3011_);
v___x_3019_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3019_, 0, v___x_3015_);
lean_ctor_set(v___x_3019_, 1, v___x_3018_);
lean_ctor_set(v___x_3019_, 2, v___x_3014_);
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*3, v___x_3016_);
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*3 + 1, v___x_3017_);
lean_ctor_set_uint8(v___x_3019_, sizeof(void*)*3 + 2, v___x_3017_);
v___x_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3020_, 0, v___x_3012_);
lean_ctor_set(v___x_3020_, 1, v___x_3019_);
v___x_3021_ = lean_task_pure(v___x_3020_);
v___x_3022_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3023_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3023_, 0, v___x_3021_);
lean_ctor_set(v___x_3023_, 1, v___x_3013_);
lean_ctor_set(v___x_3023_, 2, v___x_3022_);
lean_ctor_set_uint8(v___x_3023_, sizeof(void*)*3, v___x_3017_);
v___x_3024_ = lean_array_get_size(v_jobs_3010_);
v___x_3025_ = lean_nat_dec_lt(v___x_3014_, v___x_3024_);
if (v___x_3025_ == 0)
{
return v___x_3023_;
}
else
{
uint8_t v___x_3026_; 
v___x_3026_ = lean_nat_dec_le(v___x_3024_, v___x_3024_);
if (v___x_3026_ == 0)
{
if (v___x_3025_ == 0)
{
return v___x_3023_;
}
else
{
size_t v___x_3027_; size_t v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = ((size_t)0ULL);
v___x_3028_ = lean_usize_of_nat(v___x_3024_);
v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_3010_, v___x_3027_, v___x_3028_, v___x_3023_);
return v___x_3029_;
}
}
else
{
size_t v___x_3030_; size_t v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = ((size_t)0ULL);
v___x_3031_ = lean_usize_of_nat(v___x_3024_);
v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_3010_, v___x_3030_, v___x_3031_, v___x_3023_);
return v___x_3032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object* v_jobs_3033_, lean_object* v_traceCaption_3034_){
_start:
{
lean_object* v_res_3035_; 
v_res_3035_ = l_Lake_Job_mixArray___redArg(v_jobs_3033_, v_traceCaption_3034_);
lean_dec_ref(v_jobs_3033_);
return v_res_3035_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object* v_00_u03b1_3036_, lean_object* v_jobs_3037_, lean_object* v_traceCaption_3038_){
_start:
{
lean_object* v___x_3039_; 
v___x_3039_ = l_Lake_Job_mixArray___redArg(v_jobs_3037_, v_traceCaption_3038_);
return v___x_3039_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object* v_00_u03b1_3040_, lean_object* v_jobs_3041_, lean_object* v_traceCaption_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l_Lake_Job_mixArray(v_00_u03b1_3040_, v_jobs_3041_, v_traceCaption_3042_);
lean_dec_ref(v_jobs_3041_);
return v_res_3043_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_object* v_00_u03b1_3044_, lean_object* v_as_3045_, size_t v_i_3046_, size_t v_stop_3047_, lean_object* v_b_3048_){
_start:
{
lean_object* v___x_3049_; 
v___x_3049_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_3045_, v_i_3046_, v_stop_3047_, v_b_3048_);
return v___x_3049_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3045_ = stack[1].m_obj;
size_t v_i_3046_ = stack[2].m_num;
size_t v_stop_3047_ = stack[3].m_num;
lean_object* v_b_3048_ = stack[4].m_obj;
lean_object* v_res_3050_;
v_res_3050_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_box(0), v_as_3045_, v_i_3046_, v_stop_3047_, v_b_3048_);
stack->m_obj
 = v_res_3050_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(lean_object* v_00_u03b1_3051_, lean_object* v_as_3052_, lean_object* v_i_3053_, lean_object* v_stop_3054_, lean_object* v_b_3055_){
_start:
{
size_t v_i_boxed_3056_; size_t v_stop_boxed_3057_; lean_object* v_res_3058_; 
v_i_boxed_3056_ = lean_unbox_usize(v_i_3053_);
lean_dec(v_i_3053_);
v_stop_boxed_3057_ = lean_unbox_usize(v_stop_3054_);
lean_dec(v_stop_3054_);
v_res_3058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(v_00_u03b1_3051_, v_as_3052_, v_i_boxed_3056_, v_stop_boxed_3057_, v_b_3055_);
lean_dec_ref(v_as_3052_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object* v___x_3059_, lean_object* v_rx_3060_, lean_object* v_ry_3061_){
_start:
{
lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3068_; lean_object* v___y_3069_; 
if (lean_obj_tag(v_rx_3060_) == 0)
{
if (lean_obj_tag(v_ry_3061_) == 0)
{
lean_object* v_a_3071_; lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3089_; 
lean_dec(v___x_3059_);
v_a_3071_ = lean_ctor_get(v_rx_3060_, 0);
v_a_3072_ = lean_ctor_get(v_rx_3060_, 1);
v_isSharedCheck_3089_ = !lean_is_exclusive(v_rx_3060_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3074_ = v_rx_3060_;
v_isShared_3075_ = v_isSharedCheck_3089_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_inc(v_a_3071_);
lean_dec(v_rx_3060_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3089_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v_a_3076_; lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3088_; 
v_a_3076_ = lean_ctor_get(v_ry_3061_, 0);
v_a_3077_ = lean_ctor_get(v_ry_3061_, 1);
v_isSharedCheck_3088_ = !lean_is_exclusive(v_ry_3061_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3079_ = v_ry_3061_;
v_isShared_3080_ = v_isSharedCheck_3088_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_inc(v_a_3076_);
lean_dec(v_ry_3061_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3088_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3075_ == 0)
{
lean_ctor_set_tag(v___x_3074_, 1);
lean_ctor_set(v___x_3074_, 1, v_a_3076_);
v___x_3082_ = v___x_3074_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3071_);
lean_ctor_set(v_reuseFailAlloc_3087_, 1, v_a_3076_);
v___x_3082_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
lean_object* v___x_3083_; lean_object* v___x_3085_; 
v___x_3083_ = l_Lake_JobState_merge(v_a_3072_, v_a_3077_);
if (v_isShared_3080_ == 0)
{
lean_ctor_set(v___x_3079_, 1, v___x_3083_);
lean_ctor_set(v___x_3079_, 0, v___x_3082_);
v___x_3085_ = v___x_3079_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v___x_3082_);
lean_ctor_set(v_reuseFailAlloc_3086_, 1, v___x_3083_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
}
}
else
{
lean_object* v_a_3090_; 
v_a_3090_ = lean_ctor_get(v_rx_3060_, 1);
lean_inc(v_a_3090_);
lean_dec_ref_known(v_rx_3060_, 2);
v___y_3068_ = v_ry_3061_;
v___y_3069_ = v_a_3090_;
goto v___jp_3067_;
}
}
else
{
lean_object* v_a_3091_; 
v_a_3091_ = lean_ctor_get(v_rx_3060_, 1);
lean_inc(v_a_3091_);
lean_dec_ref(v_rx_3060_);
v___y_3068_ = v_ry_3061_;
v___y_3069_ = v_a_3091_;
goto v___jp_3067_;
}
v___jp_3062_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; 
v___x_3065_ = l_Lake_JobState_merge(v___y_3063_, v___y_3064_);
v___x_3066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3059_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
return v___x_3066_;
}
v___jp_3067_:
{
lean_object* v_a_3070_; 
v_a_3070_ = lean_ctor_get(v___y_3068_, 1);
lean_inc(v_a_3070_);
lean_dec_ref(v___y_3068_);
v___y_3063_ = v___y_3069_;
v___y_3064_ = v_a_3070_;
goto v___jp_3062_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object* v_b_3092_, lean_object* v___x_3093_, uint8_t v___x_3094_, lean_object* v_rx_3095_){
_start:
{
lean_object* v_task_3096_; lean_object* v___f_3097_; lean_object* v___x_3098_; 
v_task_3096_ = lean_ctor_get(v_b_3092_, 0);
lean_inc_ref(v_task_3096_);
lean_dec_ref(v_b_3092_);
lean_inc(v___x_3093_);
v___f_3097_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3097_, 0, v___x_3093_);
lean_closure_set(v___f_3097_, 1, v_rx_3095_);
v___x_3098_ = lean_task_map(v___f_3097_, v_task_3096_, v___x_3093_, v___x_3094_);
return v___x_3098_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_b_3092_ = stack[0].m_obj;
lean_object* v___x_3093_ = stack[1].m_obj;
uint8_t v___x_3094_ = stack[2].m_num;
lean_object* v_rx_3095_ = stack[3].m_obj;
lean_object* v_res_3099_;
v_res_3099_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_3092_, v___x_3093_, v___x_3094_, v_rx_3095_);
stack->m_obj
 = v_res_3099_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_b_3100_, lean_object* v___x_3101_, lean_object* v___x_3102_, lean_object* v_rx_3103_){
_start:
{
uint8_t v___x_511__boxed_3104_; lean_object* v_res_3105_; 
v___x_511__boxed_3104_ = lean_unbox(v___x_3102_);
v_res_3105_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_3100_, v___x_3101_, v___x_511__boxed_3104_, v_rx_3103_);
return v_res_3105_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(lean_object* v_as_3106_, size_t v_i_3107_, size_t v_stop_3108_, lean_object* v_b_3109_){
_start:
{
uint8_t v___x_3110_; 
v___x_3110_ = lean_usize_dec_eq(v_i_3107_, v_stop_3108_);
if (v___x_3110_ == 0)
{
size_t v___x_3111_; size_t v___x_3112_; lean_object* v___x_3113_; lean_object* v_task_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3129_; 
v___x_3111_ = ((size_t)1ULL);
v___x_3112_ = lean_usize_sub(v_i_3107_, v___x_3111_);
v___x_3113_ = lean_array_uget(v_as_3106_, v___x_3112_);
v_task_3114_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3129_ == 0)
{
lean_object* v_unused_3130_; lean_object* v_unused_3131_; 
v_unused_3130_ = lean_ctor_get(v___x_3113_, 2);
lean_dec(v_unused_3130_);
v_unused_3131_ = lean_ctor_get(v___x_3113_, 1);
lean_dec(v_unused_3131_);
v___x_3116_ = v___x_3113_;
v_isShared_3117_ = v_isSharedCheck_3129_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_task_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3129_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; uint8_t v___x_3120_; lean_object* v___x_3121_; lean_object* v___f_3122_; lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3118_ = lean_box(0);
v___x_3119_ = lean_unsigned_to_nat(0u);
v___x_3120_ = 1;
v___x_3121_ = lean_box(v___x_3120_);
v___f_3122_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3122_, 0, v_b_3109_);
lean_closure_set(v___f_3122_, 1, v___x_3119_);
lean_closure_set(v___f_3122_, 2, v___x_3121_);
v___x_3123_ = lean_task_bind(v_task_3114_, v___f_3122_, v___x_3119_, v___x_3120_);
v___x_3124_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 2, v___x_3124_);
lean_ctor_set(v___x_3116_, 1, v___x_3118_);
lean_ctor_set(v___x_3116_, 0, v___x_3123_);
v___x_3126_ = v___x_3116_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v___x_3123_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v___x_3118_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_ctor_set_uint8(v___x_3126_, sizeof(void*)*3, v___x_3110_);
v_i_3107_ = v___x_3112_;
v_b_3109_ = v___x_3126_;
goto _start;
}
}
}
else
{
return v_b_3109_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3106_ = stack[0].m_obj;
size_t v_i_3107_ = stack[1].m_num;
size_t v_stop_3108_ = stack[2].m_num;
lean_object* v_b_3109_ = stack[3].m_obj;
lean_object* v_res_3132_;
v_res_3132_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_3106_, v_i_3107_, v_stop_3108_, v_b_3109_);
stack->m_obj
 = v_res_3132_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object* v_as_3133_, lean_object* v_i_3134_, lean_object* v_stop_3135_, lean_object* v_b_3136_){
_start:
{
size_t v_i_boxed_3137_; size_t v_stop_boxed_3138_; lean_object* v_res_3139_; 
v_i_boxed_3137_ = lean_unbox_usize(v_i_3134_);
lean_dec(v_i_3134_);
v_stop_boxed_3138_ = lean_unbox_usize(v_stop_3135_);
lean_dec(v_stop_3135_);
v_res_3139_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_3133_, v_i_boxed_3137_, v_stop_boxed_3138_, v_b_3136_);
lean_dec_ref(v_as_3133_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(lean_object* v_init_3140_, lean_object* v_l_3141_){
_start:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v___x_3142_ = lean_array_mk(v_l_3141_);
v___x_3143_ = lean_array_get_size(v___x_3142_);
v___x_3144_ = lean_unsigned_to_nat(0u);
v___x_3145_ = lean_nat_dec_lt(v___x_3144_, v___x_3143_);
if (v___x_3145_ == 0)
{
lean_dec_ref(v___x_3142_);
return v_init_3140_;
}
else
{
size_t v___x_3146_; size_t v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = lean_usize_of_nat(v___x_3143_);
v___x_3147_ = ((size_t)0ULL);
v___x_3148_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v___x_3142_, v___x_3146_, v___x_3147_, v_init_3140_);
lean_dec_ref(v___x_3142_);
return v___x_3148_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object* v_jobs_3149_, lean_object* v_traceCaption_3150_){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; uint8_t v___x_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3151_ = lean_box(0);
v___x_3152_ = lean_box(0);
v___x_3153_ = lean_unsigned_to_nat(0u);
v___x_3154_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3155_ = 0;
v___x_3156_ = 0;
v___x_3157_ = l_Lake_BuildTrace_nil(v_traceCaption_3150_);
v___x_3158_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3158_, 0, v___x_3154_);
lean_ctor_set(v___x_3158_, 1, v___x_3157_);
lean_ctor_set(v___x_3158_, 2, v___x_3153_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*3, v___x_3155_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*3 + 1, v___x_3156_);
lean_ctor_set_uint8(v___x_3158_, sizeof(void*)*3 + 2, v___x_3156_);
v___x_3159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3151_);
lean_ctor_set(v___x_3159_, 1, v___x_3158_);
v___x_3160_ = lean_task_pure(v___x_3159_);
v___x_3161_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3162_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3162_, 0, v___x_3160_);
lean_ctor_set(v___x_3162_, 1, v___x_3152_);
lean_ctor_set(v___x_3162_, 2, v___x_3161_);
lean_ctor_set_uint8(v___x_3162_, sizeof(void*)*3, v___x_3156_);
v___x_3163_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v___x_3162_, v_jobs_3149_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object* v_00_u03b1_3164_, lean_object* v_jobs_3165_, lean_object* v_traceCaption_3166_){
_start:
{
lean_object* v___x_3167_; 
v___x_3167_ = l_Lake_Job_collectList___redArg(v_jobs_3165_, v_traceCaption_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0(lean_object* v_00_u03b1_3168_, lean_object* v_init_3169_, lean_object* v_l_3170_){
_start:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v_init_3169_, v_l_3170_);
return v___x_3171_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_object* v_00_u03b1_3172_, lean_object* v_as_3173_, size_t v_i_3174_, size_t v_stop_3175_, lean_object* v_b_3176_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_3173_, v_i_3174_, v_stop_3175_, v_b_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3173_ = stack[1].m_obj;
size_t v_i_3174_ = stack[2].m_num;
size_t v_stop_3175_ = stack[3].m_num;
lean_object* v_b_3176_ = stack[4].m_obj;
lean_object* v_res_3178_;
v_res_3178_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_box(0), v_as_3173_, v_i_3174_, v_stop_3175_, v_b_3176_);
stack->m_obj
 = v_res_3178_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_3179_, lean_object* v_as_3180_, lean_object* v_i_3181_, lean_object* v_stop_3182_, lean_object* v_b_3183_){
_start:
{
size_t v_i_boxed_3184_; size_t v_stop_boxed_3185_; lean_object* v_res_3186_; 
v_i_boxed_3184_ = lean_unbox_usize(v_i_3181_);
lean_dec(v_i_3181_);
v_stop_boxed_3185_ = lean_unbox_usize(v_stop_3182_);
lean_dec(v_stop_3182_);
v_res_3186_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(v_00_u03b1_3179_, v_as_3180_, v_i_boxed_3184_, v_stop_boxed_3185_, v_b_3183_);
lean_dec_ref(v_as_3180_);
return v_res_3186_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object* v___x_3187_, lean_object* v_rx_3188_, lean_object* v_ry_3189_){
_start:
{
lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3196_; lean_object* v___y_3197_; 
if (lean_obj_tag(v_rx_3188_) == 0)
{
if (lean_obj_tag(v_ry_3189_) == 0)
{
lean_object* v_a_3199_; lean_object* v_a_3200_; lean_object* v_a_3201_; lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3211_; 
lean_dec(v___x_3187_);
v_a_3199_ = lean_ctor_get(v_rx_3188_, 0);
lean_inc(v_a_3199_);
v_a_3200_ = lean_ctor_get(v_rx_3188_, 1);
lean_inc(v_a_3200_);
lean_dec_ref_known(v_rx_3188_, 2);
v_a_3201_ = lean_ctor_get(v_ry_3189_, 0);
v_a_3202_ = lean_ctor_get(v_ry_3189_, 1);
v_isSharedCheck_3211_ = !lean_is_exclusive(v_ry_3189_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3204_ = v_ry_3189_;
v_isShared_3205_ = v_isSharedCheck_3211_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_inc(v_a_3201_);
lean_dec(v_ry_3189_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3211_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3206_ = lean_array_push(v_a_3199_, v_a_3201_);
v___x_3207_ = l_Lake_JobState_merge(v_a_3200_, v_a_3202_);
if (v_isShared_3205_ == 0)
{
lean_ctor_set(v___x_3204_, 1, v___x_3207_);
lean_ctor_set(v___x_3204_, 0, v___x_3206_);
v___x_3209_ = v___x_3204_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3206_);
lean_ctor_set(v_reuseFailAlloc_3210_, 1, v___x_3207_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
else
{
lean_object* v_a_3212_; 
v_a_3212_ = lean_ctor_get(v_rx_3188_, 1);
lean_inc(v_a_3212_);
lean_dec_ref_known(v_rx_3188_, 2);
v___y_3196_ = v_ry_3189_;
v___y_3197_ = v_a_3212_;
goto v___jp_3195_;
}
}
else
{
lean_object* v_a_3213_; 
v_a_3213_ = lean_ctor_get(v_rx_3188_, 1);
lean_inc(v_a_3213_);
lean_dec_ref(v_rx_3188_);
v___y_3196_ = v_ry_3189_;
v___y_3197_ = v_a_3213_;
goto v___jp_3195_;
}
v___jp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3193_ = l_Lake_JobState_merge(v___y_3191_, v___y_3192_);
v___x_3194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3187_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
return v___x_3194_;
}
v___jp_3195_:
{
lean_object* v_a_3198_; 
v_a_3198_ = lean_ctor_get(v___y_3196_, 1);
lean_inc(v_a_3198_);
lean_dec_ref(v___y_3196_);
v___y_3191_ = v___y_3197_;
v___y_3192_ = v_a_3198_;
goto v___jp_3190_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object* v___x_3214_, lean_object* v___x_3215_, uint8_t v___x_3216_, lean_object* v_rx_3217_){
_start:
{
lean_object* v_task_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; 
v_task_3218_ = lean_ctor_get(v___x_3214_, 0);
lean_inc_ref(v_task_3218_);
lean_dec_ref(v___x_3214_);
lean_inc(v___x_3215_);
v___f_3219_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_3219_, 0, v___x_3215_);
lean_closure_set(v___f_3219_, 1, v_rx_3217_);
v___x_3220_ = lean_task_map(v___f_3219_, v_task_3218_, v___x_3215_, v___x_3216_);
return v___x_3220_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3214_ = stack[0].m_obj;
lean_object* v___x_3215_ = stack[1].m_obj;
uint8_t v___x_3216_ = stack[2].m_num;
lean_object* v_rx_3217_ = stack[3].m_obj;
lean_object* v_res_3221_;
v_res_3221_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_3214_, v___x_3215_, v___x_3216_, v_rx_3217_);
stack->m_obj
 = v_res_3221_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object* v___x_3222_, lean_object* v___x_3223_, lean_object* v___x_3224_, lean_object* v_rx_3225_){
_start:
{
uint8_t v___x_439__boxed_3226_; lean_object* v_res_3227_; 
v___x_439__boxed_3226_ = lean_unbox(v___x_3224_);
v_res_3227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_3222_, v___x_3223_, v___x_439__boxed_3226_, v_rx_3225_);
return v_res_3227_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(lean_object* v_as_3228_, size_t v_i_3229_, size_t v_stop_3230_, lean_object* v_b_3231_){
_start:
{
uint8_t v___x_3232_; 
v___x_3232_ = lean_usize_dec_eq(v_i_3229_, v_stop_3230_);
if (v___x_3232_ == 0)
{
lean_object* v_task_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3251_; 
v_task_3233_ = lean_ctor_get(v_b_3231_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v_b_3231_);
if (v_isSharedCheck_3251_ == 0)
{
lean_object* v_unused_3252_; lean_object* v_unused_3253_; 
v_unused_3252_ = lean_ctor_get(v_b_3231_, 2);
lean_dec(v_unused_3252_);
v_unused_3253_ = lean_ctor_get(v_b_3231_, 1);
lean_dec(v_unused_3253_);
v___x_3235_ = v_b_3231_;
v_isShared_3236_ = v_isSharedCheck_3251_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_task_3233_);
lean_dec(v_b_3231_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3251_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; lean_object* v___x_3241_; lean_object* v___f_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3237_ = lean_box(0);
v___x_3238_ = lean_array_uget_borrowed(v_as_3228_, v_i_3229_);
v___x_3239_ = lean_unsigned_to_nat(0u);
v___x_3240_ = 1;
v___x_3241_ = lean_box(v___x_3240_);
lean_inc(v___x_3238_);
v___f_3242_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_3242_, 0, v___x_3238_);
lean_closure_set(v___f_3242_, 1, v___x_3239_);
lean_closure_set(v___f_3242_, 2, v___x_3241_);
v___x_3243_ = lean_task_bind(v_task_3233_, v___f_3242_, v___x_3239_, v___x_3240_);
v___x_3244_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_3236_ == 0)
{
lean_ctor_set(v___x_3235_, 2, v___x_3244_);
lean_ctor_set(v___x_3235_, 1, v___x_3237_);
lean_ctor_set(v___x_3235_, 0, v___x_3243_);
v___x_3246_ = v___x_3235_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3250_, 1, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3250_, 2, v___x_3244_);
v___x_3246_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
size_t v___x_3247_; size_t v___x_3248_; 
lean_ctor_set_uint8(v___x_3246_, sizeof(void*)*3, v___x_3232_);
v___x_3247_ = ((size_t)1ULL);
v___x_3248_ = lean_usize_add(v_i_3229_, v___x_3247_);
v_i_3229_ = v___x_3248_;
v_b_3231_ = v___x_3246_;
goto _start;
}
}
}
else
{
return v_b_3231_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3228_ = stack[0].m_obj;
size_t v_i_3229_ = stack[1].m_num;
size_t v_stop_3230_ = stack[2].m_num;
lean_object* v_b_3231_ = stack[3].m_obj;
lean_object* v_res_3254_;
v_res_3254_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3228_, v_i_3229_, v_stop_3230_, v_b_3231_);
stack->m_obj
 = v_res_3254_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(lean_object* v_as_3255_, lean_object* v_i_3256_, lean_object* v_stop_3257_, lean_object* v_b_3258_){
_start:
{
size_t v_i_boxed_3259_; size_t v_stop_boxed_3260_; lean_object* v_res_3261_; 
v_i_boxed_3259_ = lean_unbox_usize(v_i_3256_);
lean_dec(v_i_3256_);
v_stop_boxed_3260_ = lean_unbox_usize(v_stop_3257_);
lean_dec(v_stop_3257_);
v_res_3261_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3255_, v_i_boxed_3259_, v_stop_boxed_3260_, v_b_3258_);
lean_dec_ref(v_as_3255_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object* v_jobs_3262_, lean_object* v_traceCaption_3263_){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; uint8_t v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; uint8_t v___x_3277_; 
v___x_3264_ = lean_array_get_size(v_jobs_3262_);
v___x_3265_ = lean_mk_empty_array_with_capacity(v___x_3264_);
v___x_3266_ = lean_box(0);
v___x_3267_ = lean_unsigned_to_nat(0u);
v___x_3268_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3269_ = 0;
v___x_3270_ = 0;
v___x_3271_ = l_Lake_BuildTrace_nil(v_traceCaption_3263_);
v___x_3272_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3272_, 0, v___x_3268_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
lean_ctor_set(v___x_3272_, 2, v___x_3267_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*3, v___x_3269_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*3 + 1, v___x_3270_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*3 + 2, v___x_3270_);
v___x_3273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3265_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = lean_task_pure(v___x_3273_);
v___x_3275_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3276_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3266_);
lean_ctor_set(v___x_3276_, 2, v___x_3275_);
lean_ctor_set_uint8(v___x_3276_, sizeof(void*)*3, v___x_3270_);
v___x_3277_ = lean_nat_dec_lt(v___x_3267_, v___x_3264_);
if (v___x_3277_ == 0)
{
return v___x_3276_;
}
else
{
uint8_t v___x_3278_; 
v___x_3278_ = lean_nat_dec_le(v___x_3264_, v___x_3264_);
if (v___x_3278_ == 0)
{
if (v___x_3277_ == 0)
{
return v___x_3276_;
}
else
{
size_t v___x_3279_; size_t v___x_3280_; lean_object* v___x_3281_; 
v___x_3279_ = ((size_t)0ULL);
v___x_3280_ = lean_usize_of_nat(v___x_3264_);
v___x_3281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_3262_, v___x_3279_, v___x_3280_, v___x_3276_);
return v___x_3281_;
}
}
else
{
size_t v___x_3282_; size_t v___x_3283_; lean_object* v___x_3284_; 
v___x_3282_ = ((size_t)0ULL);
v___x_3283_ = lean_usize_of_nat(v___x_3264_);
v___x_3284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_3262_, v___x_3282_, v___x_3283_, v___x_3276_);
return v___x_3284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object* v_jobs_3285_, lean_object* v_traceCaption_3286_){
_start:
{
lean_object* v_res_3287_; 
v_res_3287_ = l_Lake_Job_collectArray___redArg(v_jobs_3285_, v_traceCaption_3286_);
lean_dec_ref(v_jobs_3285_);
return v_res_3287_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object* v_00_u03b1_3288_, lean_object* v_jobs_3289_, lean_object* v_traceCaption_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Lake_Job_collectArray___redArg(v_jobs_3289_, v_traceCaption_3290_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object* v_00_u03b1_3292_, lean_object* v_jobs_3293_, lean_object* v_traceCaption_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Lake_Job_collectArray(v_00_u03b1_3292_, v_jobs_3293_, v_traceCaption_3294_);
lean_dec_ref(v_jobs_3293_);
return v_res_3295_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_object* v_00_u03b1_3296_, lean_object* v_as_3297_, size_t v_i_3298_, size_t v_stop_3299_, lean_object* v_b_3300_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3297_, v_i_3298_, v_stop_3299_, v_b_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_3297_ = stack[1].m_obj;
size_t v_i_3298_ = stack[2].m_num;
size_t v_stop_3299_ = stack[3].m_num;
lean_object* v_b_3300_ = stack[4].m_obj;
lean_object* v_res_3302_;
v_res_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_box(0), v_as_3297_, v_i_3298_, v_stop_3299_, v_b_3300_);
stack->m_obj
 = v_res_3302_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(lean_object* v_00_u03b1_3303_, lean_object* v_as_3304_, lean_object* v_i_3305_, lean_object* v_stop_3306_, lean_object* v_b_3307_){
_start:
{
size_t v_i_boxed_3308_; size_t v_stop_boxed_3309_; lean_object* v_res_3310_; 
v_i_boxed_3308_ = lean_unbox_usize(v_i_3305_);
lean_dec(v_i_3305_);
v_stop_boxed_3309_ = lean_unbox_usize(v_stop_3306_);
lean_dec(v_stop_3306_);
v_res_3310_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(v_00_u03b1_3303_, v_as_3304_, v_i_boxed_3308_, v_stop_boxed_3309_, v_b_3307_);
lean_dec_ref(v_as_3304_);
return v_res_3310_;
}
}
lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg(){
_start:
{
lean_object* v___x_3312_; 
v___x_3312_ = lean_box(0);
return v___x_3312_;
}
}
LEAN_EXPORT void l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3313_;
v_res_3313_ = l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg();
stack->m_obj
 = v_res_3313_;
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg___boxed(lean_object* v___dummy_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1___redArg();
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(lean_object* v_00_u03b1_3316_, lean_object* v_inst_3317_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = lean_box(0);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0(lean_object* v___x_3319_, lean_object* v_rx_3320_, lean_object* v_i_3321_, lean_object* v_ry_3322_){
_start:
{
lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3329_; lean_object* v___y_3330_; 
if (lean_obj_tag(v_rx_3320_) == 0)
{
if (lean_obj_tag(v_ry_3322_) == 0)
{
lean_object* v_a_3332_; lean_object* v_a_3333_; lean_object* v_a_3334_; lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v___x_3319_);
v_a_3332_ = lean_ctor_get(v_rx_3320_, 0);
lean_inc(v_a_3332_);
v_a_3333_ = lean_ctor_get(v_rx_3320_, 1);
lean_inc(v_a_3333_);
lean_dec_ref_known(v_rx_3320_, 2);
v_a_3334_ = lean_ctor_get(v_ry_3322_, 0);
v_a_3335_ = lean_ctor_get(v_ry_3322_, 1);
v_isSharedCheck_3344_ = !lean_is_exclusive(v_ry_3322_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3337_ = v_ry_3322_;
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_inc(v_a_3334_);
lean_dec(v_ry_3322_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3344_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3342_; 
v___x_3339_ = lean_array_fset(v_a_3332_, v_i_3321_, v_a_3334_);
v___x_3340_ = l_Lake_JobState_merge(v_a_3333_, v_a_3335_);
if (v_isShared_3338_ == 0)
{
lean_ctor_set(v___x_3337_, 1, v___x_3340_);
lean_ctor_set(v___x_3337_, 0, v___x_3339_);
v___x_3342_ = v___x_3337_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3343_, 1, v___x_3340_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
else
{
lean_object* v_a_3345_; 
v_a_3345_ = lean_ctor_get(v_rx_3320_, 1);
lean_inc(v_a_3345_);
lean_dec_ref_known(v_rx_3320_, 2);
v___y_3329_ = v_ry_3322_;
v___y_3330_ = v_a_3345_;
goto v___jp_3328_;
}
}
else
{
lean_object* v_a_3346_; 
v_a_3346_ = lean_ctor_get(v_rx_3320_, 1);
lean_inc(v_a_3346_);
lean_dec_ref(v_rx_3320_);
v___y_3329_ = v_ry_3322_;
v___y_3330_ = v_a_3346_;
goto v___jp_3328_;
}
v___jp_3323_:
{
lean_object* v___x_3326_; lean_object* v___x_3327_; 
v___x_3326_ = l_Lake_JobState_merge(v___y_3324_, v___y_3325_);
v___x_3327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3319_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
return v___x_3327_;
}
v___jp_3328_:
{
lean_object* v_a_3331_; 
v_a_3331_ = lean_ctor_get(v___y_3329_, 1);
lean_inc(v_a_3331_);
lean_dec_ref(v___y_3329_);
v___y_3324_ = v___y_3330_;
v___y_3325_ = v_a_3331_;
goto v___jp_3323_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0___boxed(lean_object* v___x_3347_, lean_object* v_rx_3348_, lean_object* v_i_3349_, lean_object* v_ry_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_Lake_Job_collectVector___redArg___lam__0(v___x_3347_, v_rx_3348_, v_i_3349_, v_ry_3350_);
lean_dec(v_i_3349_);
return v_res_3351_;
}
}
lean_object* l_Lake_Job_collectVector___redArg___lam__1(lean_object* v___x_3352_, lean_object* v___x_3353_, lean_object* v_i_3354_, uint8_t v___x_3355_, lean_object* v_rx_3356_){
_start:
{
lean_object* v_task_3357_; lean_object* v___f_3358_; lean_object* v___x_3359_; 
v_task_3357_ = lean_ctor_get(v___x_3352_, 0);
lean_inc_ref(v_task_3357_);
lean_dec_ref(v___x_3352_);
lean_inc(v___x_3353_);
v___f_3358_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3358_, 0, v___x_3353_);
lean_closure_set(v___f_3358_, 1, v_rx_3356_);
lean_closure_set(v___f_3358_, 2, v_i_3354_);
v___x_3359_ = lean_task_map(v___f_3358_, v_task_3357_, v___x_3353_, v___x_3355_);
return v___x_3359_;
}
}
LEAN_EXPORT void l_Lake_Job_collectVector___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_3352_ = stack[0].m_obj;
lean_object* v___x_3353_ = stack[1].m_obj;
lean_object* v_i_3354_ = stack[2].m_obj;
uint8_t v___x_3355_ = stack[3].m_num;
lean_object* v_rx_3356_ = stack[4].m_obj;
lean_object* v_res_3360_;
v_res_3360_ = l_Lake_Job_collectVector___redArg___lam__1(v___x_3352_, v___x_3353_, v_i_3354_, v___x_3355_, v_rx_3356_);
stack->m_obj
 = v_res_3360_;
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1___boxed(lean_object* v___x_3361_, lean_object* v___x_3362_, lean_object* v_i_3363_, lean_object* v___x_3364_, lean_object* v_rx_3365_){
_start:
{
uint8_t v___x_217__boxed_3366_; lean_object* v_res_3367_; 
v___x_217__boxed_3366_ = lean_unbox(v___x_3364_);
v_res_3367_ = l_Lake_Job_collectVector___redArg___lam__1(v___x_3361_, v___x_3362_, v_i_3363_, v___x_217__boxed_3366_, v_rx_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2(lean_object* v_jobs_3368_, lean_object* v___x_3369_, lean_object* v_i_3370_, lean_object* v_h_3371_, lean_object* v_job_3372_){
_start:
{
lean_object* v_task_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3388_; 
v_task_3373_ = lean_ctor_get(v_job_3372_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v_job_3372_);
if (v_isSharedCheck_3388_ == 0)
{
lean_object* v_unused_3389_; lean_object* v_unused_3390_; 
v_unused_3389_ = lean_ctor_get(v_job_3372_, 2);
lean_dec(v_unused_3389_);
v_unused_3390_ = lean_ctor_get(v_job_3372_, 1);
lean_dec(v_unused_3390_);
v___x_3375_ = v_job_3372_;
v_isShared_3376_ = v_isSharedCheck_3388_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_task_3373_);
lean_dec(v_job_3372_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3388_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; lean_object* v___x_3380_; lean_object* v___f_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; uint8_t v___x_3384_; lean_object* v___x_3386_; 
v___x_3377_ = lean_array_fget_borrowed(v_jobs_3368_, v_i_3370_);
v___x_3378_ = lean_unsigned_to_nat(0u);
v___x_3379_ = 1;
v___x_3380_ = lean_box(v___x_3379_);
lean_inc(v___x_3377_);
v___f_3381_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3381_, 0, v___x_3377_);
lean_closure_set(v___f_3381_, 1, v___x_3378_);
lean_closure_set(v___f_3381_, 2, v_i_3370_);
lean_closure_set(v___f_3381_, 3, v___x_3380_);
v___x_3382_ = lean_task_bind(v_task_3373_, v___f_3381_, v___x_3378_, v___x_3379_);
v___x_3383_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3384_ = 0;
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 2, v___x_3383_);
lean_ctor_set(v___x_3375_, 1, v___x_3369_);
lean_ctor_set(v___x_3375_, 0, v___x_3382_);
v___x_3386_ = v___x_3375_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v___x_3382_);
lean_ctor_set(v_reuseFailAlloc_3387_, 1, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3387_, 2, v___x_3383_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_ctor_set_uint8(v___x_3386_, sizeof(void*)*3, v___x_3384_);
return v___x_3386_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2___boxed(lean_object* v_jobs_3391_, lean_object* v___x_3392_, lean_object* v_i_3393_, lean_object* v_h_3394_, lean_object* v_job_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_Lake_Job_collectVector___redArg___lam__2(v_jobs_3391_, v___x_3392_, v_i_3393_, v_h_3394_, v_job_3395_);
lean_dec_ref(v_jobs_3391_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg(lean_object* v_n_3397_, lean_object* v_jobs_3398_, lean_object* v_traceCaption_3399_){
_start:
{
lean_object* v_placeholder_3400_; lean_object* v___x_3401_; lean_object* v___f_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; uint8_t v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_placeholder_3400_ = lean_box(0);
v___x_3401_ = lean_box(0);
v___f_3402_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3402_, 0, v_jobs_3398_);
lean_closure_set(v___f_3402_, 1, v___x_3401_);
lean_inc_n(v_n_3397_, 2);
v___x_3403_ = lean_mk_array(v_n_3397_, v_placeholder_3400_);
v___x_3404_ = lean_unsigned_to_nat(0u);
v___x_3405_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3406_ = 0;
v___x_3407_ = 0;
v___x_3408_ = l_Lake_BuildTrace_nil(v_traceCaption_3399_);
v___x_3409_ = lean_alloc_ctor(0, 3, 3);
lean_ctor_set(v___x_3409_, 0, v___x_3405_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
lean_ctor_set(v___x_3409_, 2, v___x_3404_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*3, v___x_3406_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*3 + 1, v___x_3407_);
lean_ctor_set_uint8(v___x_3409_, sizeof(void*)*3 + 2, v___x_3407_);
v___x_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3403_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = lean_task_pure(v___x_3410_);
v___x_3412_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3413_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3413_, 0, v___x_3411_);
lean_ctor_set(v___x_3413_, 1, v___x_3401_);
lean_ctor_set(v___x_3413_, 2, v___x_3412_);
lean_ctor_set_uint8(v___x_3413_, sizeof(void*)*3, v___x_3407_);
v___x_3414_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3397_, v___f_3402_, v_n_3397_, lean_box(0), v___x_3413_);
lean_dec(v_n_3397_);
return v___x_3414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector(lean_object* v_n_3415_, lean_object* v_00_u03b1_3416_, lean_object* v_inst_3417_, lean_object* v_jobs_3418_, lean_object* v_traceCaption_3419_){
_start:
{
lean_object* v___x_3420_; 
v___x_3420_ = l_Lake_Job_collectVector___redArg(v_n_3415_, v_jobs_3418_, v_traceCaption_3419_);
return v___x_3420_;
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
