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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_string_from_utf8_unchecked(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_ByteArray_empty;
lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object*, lean_object*);
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
lean_object* v___x_83_; lean_object* v_get_84_; lean_object* v_set_85_; lean_object* v_modifyGet_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_111_; 
v___x_83_ = lean_obj_once(&l_Lake_instMonadStateOfJobStateJobM___closed__1, &l_Lake_instMonadStateOfJobStateJobM___closed__1_once, _init_l_Lake_instMonadStateOfJobStateJobM___closed__1);
v_get_84_ = lean_ctor_get(v___x_83_, 0);
v_set_85_ = lean_ctor_get(v___x_83_, 1);
v_modifyGet_86_ = lean_ctor_get(v___x_83_, 2);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_83_);
if (v_isSharedCheck_111_ == 0)
{
v___x_88_ = v___x_83_;
v_isShared_89_ = v_isSharedCheck_111_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_modifyGet_86_);
lean_inc(v_set_85_);
lean_inc(v_get_84_);
lean_dec(v___x_83_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_111_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___f_93_; lean_object* v___f_94_; lean_object* v___x_95_; lean_object* v___f_96_; lean_object* v___f_97_; lean_object* v___x_98_; lean_object* v___f_99_; lean_object* v___f_100_; lean_object* v___x_101_; lean_object* v___f_102_; lean_object* v___f_103_; lean_object* v___x_104_; lean_object* v___f_105_; lean_object* v___f_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_90_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__2));
v___f_91_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__3));
v___x_92_ = ((lean_object*)(l_Lake_instMonadStateOfJobStateJobM___closed__4));
v___f_93_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_93_, 0, v_set_85_);
lean_closure_set(v___f_93_, 1, v___f_91_);
v___f_94_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_94_, 0, v_modifyGet_86_);
lean_closure_set(v___f_94_, 1, v___f_91_);
v___x_95_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_95_, 0, lean_box(0));
lean_closure_set(v___x_95_, 1, v_get_84_);
v___f_96_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_96_, 0, v___f_93_);
lean_closure_set(v___f_96_, 1, v___x_92_);
v___f_97_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_97_, 0, v___f_94_);
lean_closure_set(v___f_97_, 1, v___x_92_);
v___x_98_ = lean_alloc_closure((void*)(l_StateRefT_x27_lift___boxed), 6, 5);
lean_closure_set(v___x_98_, 0, lean_box(0));
lean_closure_set(v___x_98_, 1, lean_box(0));
lean_closure_set(v___x_98_, 2, lean_box(0));
lean_closure_set(v___x_98_, 3, lean_box(0));
lean_closure_set(v___x_98_, 4, v___x_95_);
v___f_99_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_99_, 0, v___f_96_);
lean_closure_set(v___f_99_, 1, v___f_91_);
v___f_100_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_100_, 0, v___f_97_);
lean_closure_set(v___f_100_, 1, v___f_91_);
v___x_101_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_101_, 0, lean_box(0));
lean_closure_set(v___x_101_, 1, v___x_98_);
v___f_102_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_102_, 0, v___f_99_);
lean_closure_set(v___f_102_, 1, v___f_91_);
v___f_103_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_103_, 0, v___f_100_);
lean_closure_set(v___f_103_, 1, v___f_91_);
v___x_104_ = lean_alloc_closure((void*)(l_ReaderT_instMonadLift___lam__0___boxed), 3, 2);
lean_closure_set(v___x_104_, 0, lean_box(0));
lean_closure_set(v___x_104_, 1, v___x_101_);
v___f_105_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__0), 3, 2);
lean_closure_set(v___f_105_, 0, v___f_102_);
lean_closure_set(v___f_105_, 1, v___x_90_);
v___f_106_ = lean_alloc_closure((void*)(l_instMonadStateOfOfMonadLift___redArg___lam__1), 4, 2);
lean_closure_set(v___f_106_, 0, v___f_103_);
lean_closure_set(v___f_106_, 1, v___x_90_);
v___x_107_ = lean_alloc_closure((void*)(l_Lake_EquipT_lift___boxed), 5, 4);
lean_closure_set(v___x_107_, 0, lean_box(0));
lean_closure_set(v___x_107_, 1, lean_box(0));
lean_closure_set(v___x_107_, 2, lean_box(0));
lean_closure_set(v___x_107_, 3, v___x_104_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 2, v___f_106_);
lean_ctor_set(v___x_88_, 1, v___f_105_);
lean_ctor_set(v___x_88_, 0, v___x_107_);
v___x_109_ = v___x_88_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___f_105_);
lean_ctor_set(v_reuseFailAlloc_110_, 2, v___f_106_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0(lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v_log_119_; lean_object* v___x_120_; 
v_log_119_ = lean_ctor_get(v___y_117_, 0);
lean_inc_ref(v_log_119_);
v___x_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_120_, 0, v_log_119_);
lean_ctor_set(v___x_120_, 1, v___y_117_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__0___boxed(lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lake_instMonadStateOfLogJobM___lam__0(v___y_121_, v___y_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1(lean_object* v_log_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
uint8_t v_action_137_; uint8_t v_wantsRebuild_138_; lean_object* v_trace_139_; lean_object* v_buildTime_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_149_; 
v_action_137_ = lean_ctor_get_uint8(v___y_135_, sizeof(void*)*3);
v_wantsRebuild_138_ = lean_ctor_get_uint8(v___y_135_, sizeof(void*)*3 + 1);
v_trace_139_ = lean_ctor_get(v___y_135_, 1);
v_buildTime_140_ = lean_ctor_get(v___y_135_, 2);
v_isSharedCheck_149_ = !lean_is_exclusive(v___y_135_);
if (v_isSharedCheck_149_ == 0)
{
lean_object* v_unused_150_; 
v_unused_150_ = lean_ctor_get(v___y_135_, 0);
lean_dec(v_unused_150_);
v___x_142_ = v___y_135_;
v_isShared_143_ = v_isSharedCheck_149_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_buildTime_140_);
lean_inc(v_trace_139_);
lean_dec(v___y_135_);
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
lean_ctor_set(v___x_142_, 0, v_log_129_);
v___x_146_ = v___x_142_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v_log_129_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v_trace_139_);
lean_ctor_set(v_reuseFailAlloc_148_, 2, v_buildTime_140_);
lean_ctor_set_uint8(v_reuseFailAlloc_148_, sizeof(void*)*3, v_action_137_);
lean_ctor_set_uint8(v_reuseFailAlloc_148_, sizeof(void*)*3 + 1, v_wantsRebuild_138_);
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
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__1___boxed(lean_object* v_log_151_, lean_object* v___y_152_, lean_object* v___y_153_, lean_object* v___y_154_, lean_object* v___y_155_, lean_object* v___y_156_, lean_object* v___y_157_, lean_object* v___y_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l_Lake_instMonadStateOfLogJobM___lam__1(v_log_151_, v___y_152_, v___y_153_, v___y_154_, v___y_155_, v___y_156_, v___y_157_);
lean_dec_ref(v___y_156_);
lean_dec(v___y_155_);
lean_dec(v___y_154_);
lean_dec(v___y_153_);
lean_dec_ref(v___y_152_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2(lean_object* v_00_u03b1_160_, lean_object* v_f_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v_log_169_; uint8_t v_action_170_; uint8_t v_wantsRebuild_171_; lean_object* v_trace_172_; lean_object* v_buildTime_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_190_; 
v_log_169_ = lean_ctor_get(v___y_167_, 0);
v_action_170_ = lean_ctor_get_uint8(v___y_167_, sizeof(void*)*3);
v_wantsRebuild_171_ = lean_ctor_get_uint8(v___y_167_, sizeof(void*)*3 + 1);
v_trace_172_ = lean_ctor_get(v___y_167_, 1);
v_buildTime_173_ = lean_ctor_get(v___y_167_, 2);
v_isSharedCheck_190_ = !lean_is_exclusive(v___y_167_);
if (v_isSharedCheck_190_ == 0)
{
v___x_175_ = v___y_167_;
v_isShared_176_ = v_isSharedCheck_190_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_buildTime_173_);
lean_inc(v_trace_172_);
lean_inc(v_log_169_);
lean_dec(v___y_167_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_190_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_177_; lean_object* v_fst_178_; lean_object* v_snd_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_189_; 
v___x_177_ = lean_apply_1(v_f_161_, v_log_169_);
v_fst_178_ = lean_ctor_get(v___x_177_, 0);
v_snd_179_ = lean_ctor_get(v___x_177_, 1);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_177_);
if (v_isSharedCheck_189_ == 0)
{
v___x_181_ = v___x_177_;
v_isShared_182_ = v_isSharedCheck_189_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_snd_179_);
lean_inc(v_fst_178_);
lean_dec(v___x_177_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_189_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_184_; 
if (v_isShared_176_ == 0)
{
lean_ctor_set(v___x_175_, 0, v_snd_179_);
v___x_184_ = v___x_175_;
goto v_reusejp_183_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_snd_179_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v_trace_172_);
lean_ctor_set(v_reuseFailAlloc_188_, 2, v_buildTime_173_);
lean_ctor_set_uint8(v_reuseFailAlloc_188_, sizeof(void*)*3, v_action_170_);
lean_ctor_set_uint8(v_reuseFailAlloc_188_, sizeof(void*)*3 + 1, v_wantsRebuild_171_);
v___x_184_ = v_reuseFailAlloc_188_;
goto v_reusejp_183_;
}
v_reusejp_183_:
{
lean_object* v___x_186_; 
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_184_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_fst_178_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadStateOfLogJobM___lam__2___boxed(lean_object* v_00_u03b1_191_, lean_object* v_f_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lake_instMonadStateOfLogJobM___lam__2(v_00_u03b1_191_, v_f_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_, v___y_197_, v___y_198_);
lean_dec_ref(v___y_197_);
lean_dec(v___y_196_);
lean_dec(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0(lean_object* v_00_u03b1_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_log_221_; uint8_t v_action_222_; uint8_t v_wantsRebuild_223_; lean_object* v_trace_224_; lean_object* v_buildTime_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_237_; 
v_log_221_ = lean_ctor_get(v___y_219_, 0);
v_action_222_ = lean_ctor_get_uint8(v___y_219_, sizeof(void*)*3);
v_wantsRebuild_223_ = lean_ctor_get_uint8(v___y_219_, sizeof(void*)*3 + 1);
v_trace_224_ = lean_ctor_get(v___y_219_, 1);
v_buildTime_225_ = lean_ctor_get(v___y_219_, 2);
v_isSharedCheck_237_ = !lean_is_exclusive(v___y_219_);
if (v_isSharedCheck_237_ == 0)
{
v___x_227_ = v___y_219_;
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_buildTime_225_);
lean_inc(v_trace_224_);
lean_inc(v_log_221_);
lean_dec(v___y_219_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_237_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
uint8_t v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_229_ = 3;
v___x_230_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_230_, 0, v___y_213_);
lean_ctor_set_uint8(v___x_230_, sizeof(void*)*1, v___x_229_);
v___x_231_ = lean_array_get_size(v_log_221_);
v___x_232_ = lean_array_push(v_log_221_, v___x_230_);
if (v_isShared_228_ == 0)
{
lean_ctor_set(v___x_227_, 0, v___x_232_);
v___x_234_ = v___x_227_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_232_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v_trace_224_);
lean_ctor_set(v_reuseFailAlloc_236_, 2, v_buildTime_225_);
lean_ctor_set_uint8(v_reuseFailAlloc_236_, sizeof(void*)*3, v_action_222_);
lean_ctor_set_uint8(v_reuseFailAlloc_236_, sizeof(void*)*3 + 1, v_wantsRebuild_223_);
v___x_234_ = v_reuseFailAlloc_236_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; 
v___x_235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_231_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadErrorJobM___lam__0___boxed(lean_object* v_00_u03b1_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lake_instMonadErrorJobM___lam__0(v_00_u03b1_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec(v___y_242_);
lean_dec(v___y_241_);
lean_dec_ref(v___y_240_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0(lean_object* v_00_u03b1_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_log_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_log_258_ = lean_ctor_get(v___y_256_, 0);
v___x_259_ = lean_array_get_size(v_log_258_);
v___x_260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___y_256_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__0___boxed(lean_object* v_00_u03b1_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lake_instAlternativeJobM___lam__0(v_00_u03b1_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1(lean_object* v_00_u03b1_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
lean_inc_ref(v___y_277_);
lean_inc(v___y_276_);
lean_inc(v___y_275_);
lean_inc(v___y_274_);
lean_inc_ref(v___y_273_);
v___x_280_ = lean_apply_7(v___y_271_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_, lean_box(0));
if (lean_obj_tag(v___x_280_) == 0)
{
lean_dec_ref(v___y_273_);
lean_dec_ref(v___y_272_);
return v___x_280_;
}
else
{
lean_object* v_a_281_; lean_object* v_a_282_; lean_object* v_log_283_; uint8_t v_action_284_; uint8_t v_wantsRebuild_285_; lean_object* v_trace_286_; lean_object* v_buildTime_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_297_; 
v_a_281_ = lean_ctor_get(v___x_280_, 1);
lean_inc(v_a_281_);
v_a_282_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_a_282_);
lean_dec_ref(v___x_280_);
v_log_283_ = lean_ctor_get(v_a_281_, 0);
v_action_284_ = lean_ctor_get_uint8(v_a_281_, sizeof(void*)*3);
v_wantsRebuild_285_ = lean_ctor_get_uint8(v_a_281_, sizeof(void*)*3 + 1);
v_trace_286_ = lean_ctor_get(v_a_281_, 1);
v_buildTime_287_ = lean_ctor_get(v_a_281_, 2);
v_isSharedCheck_297_ = !lean_is_exclusive(v_a_281_);
if (v_isSharedCheck_297_ == 0)
{
v___x_289_ = v_a_281_;
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_buildTime_287_);
lean_inc(v_trace_286_);
lean_inc(v_log_283_);
lean_dec(v_a_281_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_297_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = l_Array_shrink___redArg(v_log_283_, v_a_282_);
lean_dec(v_a_282_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_trace_286_);
lean_ctor_set(v_reuseFailAlloc_296_, 2, v_buildTime_287_);
lean_ctor_set_uint8(v_reuseFailAlloc_296_, sizeof(void*)*3, v_action_284_);
lean_ctor_set_uint8(v_reuseFailAlloc_296_, sizeof(void*)*3 + 1, v_wantsRebuild_285_);
v___x_293_ = v_reuseFailAlloc_296_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(0);
lean_inc_ref(v___y_277_);
lean_inc(v___y_276_);
lean_inc(v___y_275_);
lean_inc(v___y_274_);
v___x_295_ = lean_apply_8(v___y_272_, v___x_294_, v___y_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_, v___x_293_, lean_box(0));
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instAlternativeJobM___lam__1___boxed(lean_object* v_00_u03b1_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lake_instAlternativeJobM___lam__1(v_00_u03b1_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec(v___y_303_);
lean_dec(v___y_302_);
return v_res_308_;
}
}
static lean_object* _init_l_Lake_instAlternativeJobM(void){
_start:
{
lean_object* v___x_311_; lean_object* v_toApplicative_312_; lean_object* v_toBind_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_347_; 
v___x_311_ = l_instMonadBaseIO;
v_toApplicative_312_ = lean_ctor_get(v___x_311_, 0);
v_toBind_313_ = lean_ctor_get(v___x_311_, 1);
v_isSharedCheck_347_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_347_ == 0)
{
v___x_315_ = v___x_311_;
v_isShared_316_ = v_isSharedCheck_347_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_toBind_313_);
lean_inc(v_toApplicative_312_);
lean_dec(v___x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_347_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_toFunctor_317_; lean_object* v_toPure_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_343_; 
v_toFunctor_317_ = lean_ctor_get(v_toApplicative_312_, 0);
v_toPure_318_ = lean_ctor_get(v_toApplicative_312_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_toApplicative_312_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; lean_object* v_unused_345_; lean_object* v_unused_346_; 
v_unused_344_ = lean_ctor_get(v_toApplicative_312_, 4);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_toApplicative_312_, 3);
lean_dec(v_unused_345_);
v_unused_346_ = lean_ctor_get(v_toApplicative_312_, 2);
lean_dec(v_unused_346_);
v___x_320_ = v_toApplicative_312_;
v_isShared_321_ = v_isSharedCheck_343_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_toPure_318_);
lean_inc(v_toFunctor_317_);
lean_dec(v_toApplicative_312_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_343_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
lean_object* v___f_322_; lean_object* v___f_323_; lean_object* v___f_324_; lean_object* v___f_325_; lean_object* v___x_326_; lean_object* v___f_327_; lean_object* v___x_329_; 
lean_inc(v_toBind_313_);
lean_inc(v_toPure_318_);
v___f_322_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__1), 7, 2);
lean_closure_set(v___f_322_, 0, v_toPure_318_);
lean_closure_set(v___f_322_, 1, v_toBind_313_);
lean_inc(v_toBind_313_);
lean_inc(v_toPure_318_);
v___f_323_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__3), 7, 2);
lean_closure_set(v___f_323_, 0, v_toPure_318_);
lean_closure_set(v___f_323_, 1, v_toBind_313_);
lean_inc_ref(v___f_322_);
lean_inc(v_toPure_318_);
v___f_324_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__5), 7, 2);
lean_closure_set(v___f_324_, 0, v_toPure_318_);
lean_closure_set(v___f_324_, 1, v___f_322_);
lean_inc(v_toPure_318_);
lean_inc_ref(v_toFunctor_317_);
v___f_325_ = lean_alloc_closure((void*)(l_Lake_EStateT_instMonad___redArg___lam__9), 8, 3);
lean_closure_set(v___f_325_, 0, v_toFunctor_317_);
lean_closure_set(v___f_325_, 1, v_toPure_318_);
lean_closure_set(v___f_325_, 2, v_toBind_313_);
v___x_326_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_317_);
v___f_327_ = lean_alloc_closure((void*)(l_Lake_EStateT_instPure___redArg___lam__0), 4, 1);
lean_closure_set(v___f_327_, 0, v_toPure_318_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 4, v___f_323_);
lean_ctor_set(v___x_320_, 3, v___f_324_);
lean_ctor_set(v___x_320_, 2, v___f_325_);
lean_ctor_set(v___x_320_, 1, v___f_327_);
lean_ctor_set(v___x_320_, 0, v___x_326_);
v___x_329_ = v___x_320_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___f_327_);
lean_ctor_set(v_reuseFailAlloc_342_, 2, v___f_325_);
lean_ctor_set(v_reuseFailAlloc_342_, 3, v___f_324_);
lean_ctor_set(v_reuseFailAlloc_342_, 4, v___f_323_);
v___x_329_ = v_reuseFailAlloc_342_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_331_; 
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 1, v___f_322_);
lean_ctor_set(v___x_315_, 0, v___x_329_);
v___x_331_ = v___x_315_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_329_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___f_322_);
v___x_331_ = v_reuseFailAlloc_341_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_toApplicative_337_; lean_object* v___f_338_; lean_object* v___f_339_; lean_object* v___x_340_; 
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0(lean_object* v_00_u03b1_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v_log_357_; uint8_t v_action_358_; uint8_t v_wantsRebuild_359_; lean_object* v_trace_360_; lean_object* v_buildTime_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_390_; 
v_log_357_ = lean_ctor_get(v___y_355_, 0);
v_action_358_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*3);
v_wantsRebuild_359_ = lean_ctor_get_uint8(v___y_355_, sizeof(void*)*3 + 1);
v_trace_360_ = lean_ctor_get(v___y_355_, 1);
v_buildTime_361_ = lean_ctor_get(v___y_355_, 2);
v_isSharedCheck_390_ = !lean_is_exclusive(v___y_355_);
if (v_isSharedCheck_390_ == 0)
{
v___x_363_ = v___y_355_;
v_isShared_364_ = v_isSharedCheck_390_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_buildTime_361_);
lean_inc(v_trace_360_);
lean_inc(v_log_357_);
lean_dec(v___y_355_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_390_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_365_; 
v___x_365_ = lean_apply_2(v___y_349_, v_log_357_, lean_box(0));
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_a_366_; lean_object* v_a_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_377_; 
v_a_366_ = lean_ctor_get(v___x_365_, 0);
v_a_367_ = lean_ctor_get(v___x_365_, 1);
v_isSharedCheck_377_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_377_ == 0)
{
v___x_369_ = v___x_365_;
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_a_367_);
lean_inc(v_a_366_);
lean_dec(v___x_365_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_377_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_372_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v_a_367_);
v___x_372_ = v___x_363_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_a_367_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v_trace_360_);
lean_ctor_set(v_reuseFailAlloc_376_, 2, v_buildTime_361_);
lean_ctor_set_uint8(v_reuseFailAlloc_376_, sizeof(void*)*3, v_action_358_);
lean_ctor_set_uint8(v_reuseFailAlloc_376_, sizeof(void*)*3 + 1, v_wantsRebuild_359_);
v___x_372_ = v_reuseFailAlloc_376_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
lean_object* v___x_374_; 
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_372_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_366_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
else
{
lean_object* v_a_378_; lean_object* v_a_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_389_; 
v_a_378_ = lean_ctor_get(v___x_365_, 0);
v_a_379_ = lean_ctor_get(v___x_365_, 1);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_365_);
if (v_isSharedCheck_389_ == 0)
{
v___x_381_ = v___x_365_;
v_isShared_382_ = v_isSharedCheck_389_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_a_379_);
lean_inc(v_a_378_);
lean_dec(v___x_365_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_389_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_384_; 
if (v_isShared_364_ == 0)
{
lean_ctor_set(v___x_363_, 0, v_a_379_);
v___x_384_ = v___x_363_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_379_);
lean_ctor_set(v_reuseFailAlloc_388_, 1, v_trace_360_);
lean_ctor_set(v_reuseFailAlloc_388_, 2, v_buildTime_361_);
lean_ctor_set_uint8(v_reuseFailAlloc_388_, sizeof(void*)*3, v_action_358_);
lean_ctor_set_uint8(v_reuseFailAlloc_388_, sizeof(void*)*3 + 1, v_wantsRebuild_359_);
v___x_384_ = v_reuseFailAlloc_388_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_386_; 
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 1, v___x_384_);
v___x_386_ = v___x_381_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_378_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v___x_384_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instMonadLiftLogIOJobM___lam__0___boxed(lean_object* v_00_u03b1_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Lake_instMonadLiftLogIOJobM___lam__0(v_00_u03b1_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg(uint8_t v_action_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_log_406_; uint8_t v_action_407_; uint8_t v_wantsRebuild_408_; lean_object* v_trace_409_; lean_object* v_buildTime_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_420_; 
v_log_406_ = lean_ctor_get(v_a_404_, 0);
v_action_407_ = lean_ctor_get_uint8(v_a_404_, sizeof(void*)*3);
v_wantsRebuild_408_ = lean_ctor_get_uint8(v_a_404_, sizeof(void*)*3 + 1);
v_trace_409_ = lean_ctor_get(v_a_404_, 1);
v_buildTime_410_ = lean_ctor_get(v_a_404_, 2);
v_isSharedCheck_420_ = !lean_is_exclusive(v_a_404_);
if (v_isSharedCheck_420_ == 0)
{
v___x_412_ = v_a_404_;
v_isShared_413_ = v_isSharedCheck_420_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_buildTime_410_);
lean_inc(v_trace_409_);
lean_inc(v_log_406_);
lean_dec(v_a_404_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_420_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; uint8_t v___x_415_; lean_object* v___x_417_; 
v___x_414_ = lean_box(0);
v___x_415_ = l_Lake_JobAction_merge(v_action_407_, v_action_403_);
if (v_isShared_413_ == 0)
{
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_log_406_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_trace_409_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_buildTime_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*3 + 1, v_wantsRebuild_408_);
v___x_417_ = v_reuseFailAlloc_419_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_418_; 
lean_ctor_set_uint8(v___x_417_, sizeof(void*)*3, v___x_415_);
v___x_418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_418_, 0, v___x_414_);
lean_ctor_set(v___x_418_, 1, v___x_417_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___redArg___boxed(lean_object* v_action_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
uint8_t v_action_boxed_424_; lean_object* v_res_425_; 
v_action_boxed_424_ = lean_unbox(v_action_421_);
v_res_425_ = l_Lake_updateAction___redArg(v_action_boxed_424_, v_a_422_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction(uint8_t v_action_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_log_434_; uint8_t v_action_435_; uint8_t v_wantsRebuild_436_; lean_object* v_trace_437_; lean_object* v_buildTime_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_448_; 
v_log_434_ = lean_ctor_get(v_a_432_, 0);
v_action_435_ = lean_ctor_get_uint8(v_a_432_, sizeof(void*)*3);
v_wantsRebuild_436_ = lean_ctor_get_uint8(v_a_432_, sizeof(void*)*3 + 1);
v_trace_437_ = lean_ctor_get(v_a_432_, 1);
v_buildTime_438_ = lean_ctor_get(v_a_432_, 2);
v_isSharedCheck_448_ = !lean_is_exclusive(v_a_432_);
if (v_isSharedCheck_448_ == 0)
{
v___x_440_ = v_a_432_;
v_isShared_441_ = v_isSharedCheck_448_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_buildTime_438_);
lean_inc(v_trace_437_);
lean_inc(v_log_434_);
lean_dec(v_a_432_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_448_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v___x_442_; uint8_t v___x_443_; lean_object* v___x_445_; 
v___x_442_ = lean_box(0);
v___x_443_ = l_Lake_JobAction_merge(v_action_435_, v_action_426_);
if (v_isShared_441_ == 0)
{
v___x_445_ = v___x_440_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_log_434_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_trace_437_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v_buildTime_438_);
lean_ctor_set_uint8(v_reuseFailAlloc_447_, sizeof(void*)*3 + 1, v_wantsRebuild_436_);
v___x_445_ = v_reuseFailAlloc_447_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; 
lean_ctor_set_uint8(v___x_445_, sizeof(void*)*3, v___x_443_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_442_);
lean_ctor_set(v___x_446_, 1, v___x_445_);
return v___x_446_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_updateAction___boxed(lean_object* v_action_449_, lean_object* v_a_450_, lean_object* v_a_451_, lean_object* v_a_452_, lean_object* v_a_453_, lean_object* v_a_454_, lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
uint8_t v_action_boxed_457_; lean_object* v_res_458_; 
v_action_boxed_457_ = lean_unbox(v_action_449_);
v_res_458_ = l_Lake_updateAction(v_action_boxed_457_, v_a_450_, v_a_451_, v_a_452_, v_a_453_, v_a_454_, v_a_455_);
lean_dec_ref(v_a_454_);
lean_dec(v_a_453_);
lean_dec(v_a_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_a_450_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg(lean_object* v_a_459_){
_start:
{
lean_object* v_trace_461_; lean_object* v___x_462_; 
v_trace_461_ = lean_ctor_get(v_a_459_, 1);
lean_inc_ref(v_trace_461_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v_trace_461_);
lean_ctor_set(v___x_462_, 1, v_a_459_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace___redArg___boxed(lean_object* v_a_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Lake_getTrace___redArg(v_a_463_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lake_getTrace(lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_){
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
LEAN_EXPORT lean_object* l_Lake_getTrace___boxed(lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Lake_getTrace(v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_);
lean_dec_ref(v_a_479_);
lean_dec(v_a_478_);
lean_dec(v_a_477_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg(lean_object* v_trace_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_log_486_; uint8_t v_action_487_; uint8_t v_wantsRebuild_488_; lean_object* v_buildTime_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_498_; 
v_log_486_ = lean_ctor_get(v_a_484_, 0);
v_action_487_ = lean_ctor_get_uint8(v_a_484_, sizeof(void*)*3);
v_wantsRebuild_488_ = lean_ctor_get_uint8(v_a_484_, sizeof(void*)*3 + 1);
v_buildTime_489_ = lean_ctor_get(v_a_484_, 2);
v_isSharedCheck_498_ = !lean_is_exclusive(v_a_484_);
if (v_isSharedCheck_498_ == 0)
{
lean_object* v_unused_499_; 
v_unused_499_ = lean_ctor_get(v_a_484_, 1);
lean_dec(v_unused_499_);
v___x_491_ = v_a_484_;
v_isShared_492_ = v_isSharedCheck_498_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_buildTime_489_);
lean_inc(v_log_486_);
lean_dec(v_a_484_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_498_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_493_ = lean_box(0);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v_trace_483_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_497_; 
v_reuseFailAlloc_497_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_497_, 0, v_log_486_);
lean_ctor_set(v_reuseFailAlloc_497_, 1, v_trace_483_);
lean_ctor_set(v_reuseFailAlloc_497_, 2, v_buildTime_489_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*3, v_action_487_);
lean_ctor_set_uint8(v_reuseFailAlloc_497_, sizeof(void*)*3 + 1, v_wantsRebuild_488_);
v___x_495_ = v_reuseFailAlloc_497_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
lean_object* v___x_496_; 
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_493_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___redArg___boxed(lean_object* v_trace_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lake_setTrace___redArg(v_trace_500_, v_a_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace(lean_object* v_trace_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v_log_512_; uint8_t v_action_513_; uint8_t v_wantsRebuild_514_; lean_object* v_buildTime_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_524_; 
v_log_512_ = lean_ctor_get(v_a_510_, 0);
v_action_513_ = lean_ctor_get_uint8(v_a_510_, sizeof(void*)*3);
v_wantsRebuild_514_ = lean_ctor_get_uint8(v_a_510_, sizeof(void*)*3 + 1);
v_buildTime_515_ = lean_ctor_get(v_a_510_, 2);
v_isSharedCheck_524_ = !lean_is_exclusive(v_a_510_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v_a_510_, 1);
lean_dec(v_unused_525_);
v___x_517_ = v_a_510_;
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_buildTime_515_);
lean_inc(v_log_512_);
lean_dec(v_a_510_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_524_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_box(0);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 1, v_trace_504_);
v___x_521_ = v___x_517_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_log_512_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_trace_504_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_buildTime_515_);
lean_ctor_set_uint8(v_reuseFailAlloc_523_, sizeof(void*)*3, v_action_513_);
lean_ctor_set_uint8(v_reuseFailAlloc_523_, sizeof(void*)*3 + 1, v_wantsRebuild_514_);
v___x_521_ = v_reuseFailAlloc_523_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_519_);
lean_ctor_set(v___x_522_, 1, v___x_521_);
return v___x_522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTrace___boxed(lean_object* v_trace_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Lake_setTrace(v_trace_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_, v_a_532_);
lean_dec_ref(v_a_531_);
lean_dec(v_a_530_);
lean_dec(v_a_529_);
lean_dec(v_a_528_);
lean_dec_ref(v_a_527_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg(lean_object* v_caption_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_log_538_; uint8_t v_action_539_; uint8_t v_wantsRebuild_540_; lean_object* v_buildTime_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_551_; 
v_log_538_ = lean_ctor_get(v_a_536_, 0);
v_action_539_ = lean_ctor_get_uint8(v_a_536_, sizeof(void*)*3);
v_wantsRebuild_540_ = lean_ctor_get_uint8(v_a_536_, sizeof(void*)*3 + 1);
v_buildTime_541_ = lean_ctor_get(v_a_536_, 2);
v_isSharedCheck_551_ = !lean_is_exclusive(v_a_536_);
if (v_isSharedCheck_551_ == 0)
{
lean_object* v_unused_552_; 
v_unused_552_ = lean_ctor_get(v_a_536_, 1);
lean_dec(v_unused_552_);
v___x_543_ = v_a_536_;
v_isShared_544_ = v_isSharedCheck_551_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_buildTime_541_);
lean_inc(v_log_538_);
lean_dec(v_a_536_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_551_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_545_ = l_Lake_BuildTrace_nil(v_caption_535_);
v___x_546_ = lean_box(0);
if (v_isShared_544_ == 0)
{
lean_ctor_set(v___x_543_, 1, v___x_545_);
v___x_548_ = v___x_543_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_log_538_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v___x_545_);
lean_ctor_set(v_reuseFailAlloc_550_, 2, v_buildTime_541_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*3, v_action_539_);
lean_ctor_set_uint8(v_reuseFailAlloc_550_, sizeof(void*)*3 + 1, v_wantsRebuild_540_);
v___x_548_ = v_reuseFailAlloc_550_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
lean_object* v___x_549_; 
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_546_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___redArg___boxed(lean_object* v_caption_553_, lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lake_newTrace___redArg(v_caption_553_, v_a_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace(lean_object* v_caption_557_, lean_object* v_a_558_, lean_object* v_a_559_, lean_object* v_a_560_, lean_object* v_a_561_, lean_object* v_a_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_log_565_; uint8_t v_action_566_; uint8_t v_wantsRebuild_567_; lean_object* v_buildTime_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_578_; 
v_log_565_ = lean_ctor_get(v_a_563_, 0);
v_action_566_ = lean_ctor_get_uint8(v_a_563_, sizeof(void*)*3);
v_wantsRebuild_567_ = lean_ctor_get_uint8(v_a_563_, sizeof(void*)*3 + 1);
v_buildTime_568_ = lean_ctor_get(v_a_563_, 2);
v_isSharedCheck_578_ = !lean_is_exclusive(v_a_563_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v_a_563_, 1);
lean_dec(v_unused_579_);
v___x_570_ = v_a_563_;
v_isShared_571_ = v_isSharedCheck_578_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_buildTime_568_);
lean_inc(v_log_565_);
lean_dec(v_a_563_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_578_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_572_ = l_Lake_BuildTrace_nil(v_caption_557_);
v___x_573_ = lean_box(0);
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 1, v___x_572_);
v___x_575_ = v___x_570_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_log_565_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v___x_572_);
lean_ctor_set(v_reuseFailAlloc_577_, 2, v_buildTime_568_);
lean_ctor_set_uint8(v_reuseFailAlloc_577_, sizeof(void*)*3, v_action_566_);
lean_ctor_set_uint8(v_reuseFailAlloc_577_, sizeof(void*)*3 + 1, v_wantsRebuild_567_);
v___x_575_ = v_reuseFailAlloc_577_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
lean_object* v___x_576_; 
v___x_576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_573_);
lean_ctor_set(v___x_576_, 1, v___x_575_);
return v___x_576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_newTrace___boxed(lean_object* v_caption_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lake_newTrace(v_caption_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_, v_a_585_, v_a_586_);
lean_dec_ref(v_a_585_);
lean_dec(v_a_584_);
lean_dec(v_a_583_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg(lean_object* v_f_589_, lean_object* v_a_590_){
_start:
{
lean_object* v_log_592_; uint8_t v_action_593_; uint8_t v_wantsRebuild_594_; lean_object* v_trace_595_; lean_object* v_buildTime_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_606_; 
v_log_592_ = lean_ctor_get(v_a_590_, 0);
v_action_593_ = lean_ctor_get_uint8(v_a_590_, sizeof(void*)*3);
v_wantsRebuild_594_ = lean_ctor_get_uint8(v_a_590_, sizeof(void*)*3 + 1);
v_trace_595_ = lean_ctor_get(v_a_590_, 1);
v_buildTime_596_ = lean_ctor_get(v_a_590_, 2);
v_isSharedCheck_606_ = !lean_is_exclusive(v_a_590_);
if (v_isSharedCheck_606_ == 0)
{
v___x_598_ = v_a_590_;
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_buildTime_596_);
lean_inc(v_trace_595_);
lean_inc(v_log_592_);
lean_dec(v_a_590_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_603_; 
v___x_600_ = lean_box(0);
v___x_601_ = lean_apply_1(v_f_589_, v_trace_595_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v___x_601_);
v___x_603_ = v___x_598_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_log_592_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_601_);
lean_ctor_set(v_reuseFailAlloc_605_, 2, v_buildTime_596_);
lean_ctor_set_uint8(v_reuseFailAlloc_605_, sizeof(void*)*3, v_action_593_);
lean_ctor_set_uint8(v_reuseFailAlloc_605_, sizeof(void*)*3 + 1, v_wantsRebuild_594_);
v___x_603_ = v_reuseFailAlloc_605_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; 
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_600_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___redArg___boxed(lean_object* v_f_607_, lean_object* v_a_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lake_modifyTrace___redArg(v_f_607_, v_a_608_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace(lean_object* v_f_611_, lean_object* v_a_612_, lean_object* v_a_613_, lean_object* v_a_614_, lean_object* v_a_615_, lean_object* v_a_616_, lean_object* v_a_617_){
_start:
{
lean_object* v_log_619_; uint8_t v_action_620_; uint8_t v_wantsRebuild_621_; lean_object* v_trace_622_; lean_object* v_buildTime_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_633_; 
v_log_619_ = lean_ctor_get(v_a_617_, 0);
v_action_620_ = lean_ctor_get_uint8(v_a_617_, sizeof(void*)*3);
v_wantsRebuild_621_ = lean_ctor_get_uint8(v_a_617_, sizeof(void*)*3 + 1);
v_trace_622_ = lean_ctor_get(v_a_617_, 1);
v_buildTime_623_ = lean_ctor_get(v_a_617_, 2);
v_isSharedCheck_633_ = !lean_is_exclusive(v_a_617_);
if (v_isSharedCheck_633_ == 0)
{
v___x_625_ = v_a_617_;
v_isShared_626_ = v_isSharedCheck_633_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_buildTime_623_);
lean_inc(v_trace_622_);
lean_inc(v_log_619_);
lean_dec(v_a_617_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_633_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v___x_627_ = lean_box(0);
v___x_628_ = lean_apply_1(v_f_611_, v_trace_622_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_628_);
v___x_630_ = v___x_625_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_log_619_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_buildTime_623_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*3, v_action_620_);
lean_ctor_set_uint8(v_reuseFailAlloc_632_, sizeof(void*)*3 + 1, v_wantsRebuild_621_);
v___x_630_ = v_reuseFailAlloc_632_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
lean_object* v___x_631_; 
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_627_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_modifyTrace___boxed(lean_object* v_f_634_, lean_object* v_a_635_, lean_object* v_a_636_, lean_object* v_a_637_, lean_object* v_a_638_, lean_object* v_a_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lake_modifyTrace(v_f_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_, v_a_640_);
lean_dec_ref(v_a_639_);
lean_dec(v_a_638_);
lean_dec(v_a_637_);
lean_dec(v_a_636_);
lean_dec_ref(v_a_635_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg(lean_object* v_caption_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_trace_646_; lean_object* v_log_647_; uint8_t v_action_648_; uint8_t v_wantsRebuild_649_; lean_object* v_buildTime_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_670_; 
v_trace_646_ = lean_ctor_get(v_a_644_, 1);
v_log_647_ = lean_ctor_get(v_a_644_, 0);
v_action_648_ = lean_ctor_get_uint8(v_a_644_, sizeof(void*)*3);
v_wantsRebuild_649_ = lean_ctor_get_uint8(v_a_644_, sizeof(void*)*3 + 1);
v_buildTime_650_ = lean_ctor_get(v_a_644_, 2);
v_isSharedCheck_670_ = !lean_is_exclusive(v_a_644_);
if (v_isSharedCheck_670_ == 0)
{
v___x_652_ = v_a_644_;
v_isShared_653_ = v_isSharedCheck_670_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_buildTime_650_);
lean_inc(v_trace_646_);
lean_inc(v_log_647_);
lean_dec(v_a_644_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_670_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_inputs_654_; uint64_t v_hash_655_; lean_object* v_mtime_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_668_; 
v_inputs_654_ = lean_ctor_get(v_trace_646_, 1);
v_hash_655_ = lean_ctor_get_uint64(v_trace_646_, sizeof(void*)*3);
v_mtime_656_ = lean_ctor_get(v_trace_646_, 2);
v_isSharedCheck_668_ = !lean_is_exclusive(v_trace_646_);
if (v_isSharedCheck_668_ == 0)
{
lean_object* v_unused_669_; 
v_unused_669_ = lean_ctor_get(v_trace_646_, 0);
lean_dec(v_unused_669_);
v___x_658_ = v_trace_646_;
v_isShared_659_ = v_isSharedCheck_668_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_mtime_656_);
lean_inc(v_inputs_654_);
lean_dec(v_trace_646_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_668_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_660_ = lean_box(0);
if (v_isShared_659_ == 0)
{
lean_ctor_set(v___x_658_, 0, v_caption_643_);
v___x_662_ = v___x_658_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_caption_643_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_inputs_654_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_mtime_656_);
lean_ctor_set_uint64(v_reuseFailAlloc_667_, sizeof(void*)*3, v_hash_655_);
v___x_662_ = v_reuseFailAlloc_667_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 1, v___x_662_);
v___x_664_ = v___x_652_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_log_647_);
lean_ctor_set(v_reuseFailAlloc_666_, 1, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_666_, 2, v_buildTime_650_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*3, v_action_648_);
lean_ctor_set_uint8(v_reuseFailAlloc_666_, sizeof(void*)*3 + 1, v_wantsRebuild_649_);
v___x_664_ = v_reuseFailAlloc_666_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; 
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_660_);
lean_ctor_set(v___x_665_, 1, v___x_664_);
return v___x_665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___redArg___boxed(lean_object* v_caption_671_, lean_object* v_a_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_res_674_; 
v_res_674_ = l_Lake_setTraceCaption___redArg(v_caption_671_, v_a_672_);
return v_res_674_;
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption(lean_object* v_caption_675_, lean_object* v_a_676_, lean_object* v_a_677_, lean_object* v_a_678_, lean_object* v_a_679_, lean_object* v_a_680_, lean_object* v_a_681_){
_start:
{
lean_object* v_trace_683_; lean_object* v_log_684_; uint8_t v_action_685_; uint8_t v_wantsRebuild_686_; lean_object* v_buildTime_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_707_; 
v_trace_683_ = lean_ctor_get(v_a_681_, 1);
v_log_684_ = lean_ctor_get(v_a_681_, 0);
v_action_685_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*3);
v_wantsRebuild_686_ = lean_ctor_get_uint8(v_a_681_, sizeof(void*)*3 + 1);
v_buildTime_687_ = lean_ctor_get(v_a_681_, 2);
v_isSharedCheck_707_ = !lean_is_exclusive(v_a_681_);
if (v_isSharedCheck_707_ == 0)
{
v___x_689_ = v_a_681_;
v_isShared_690_ = v_isSharedCheck_707_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_buildTime_687_);
lean_inc(v_trace_683_);
lean_inc(v_log_684_);
lean_dec(v_a_681_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_707_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_inputs_691_; uint64_t v_hash_692_; lean_object* v_mtime_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_705_; 
v_inputs_691_ = lean_ctor_get(v_trace_683_, 1);
v_hash_692_ = lean_ctor_get_uint64(v_trace_683_, sizeof(void*)*3);
v_mtime_693_ = lean_ctor_get(v_trace_683_, 2);
v_isSharedCheck_705_ = !lean_is_exclusive(v_trace_683_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v_trace_683_, 0);
lean_dec(v_unused_706_);
v___x_695_ = v_trace_683_;
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_mtime_693_);
lean_inc(v_inputs_691_);
lean_dec(v_trace_683_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_705_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v___x_697_; lean_object* v___x_699_; 
v___x_697_ = lean_box(0);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 0, v_caption_675_);
v___x_699_ = v___x_695_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 3, 8);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_caption_675_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_inputs_691_);
lean_ctor_set(v_reuseFailAlloc_704_, 2, v_mtime_693_);
lean_ctor_set_uint64(v_reuseFailAlloc_704_, sizeof(void*)*3, v_hash_692_);
v___x_699_ = v_reuseFailAlloc_704_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
lean_object* v___x_701_; 
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 1, v___x_699_);
v___x_701_ = v___x_689_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_log_684_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_703_, 2, v_buildTime_687_);
lean_ctor_set_uint8(v_reuseFailAlloc_703_, sizeof(void*)*3, v_action_685_);
lean_ctor_set_uint8(v_reuseFailAlloc_703_, sizeof(void*)*3 + 1, v_wantsRebuild_686_);
v___x_701_ = v_reuseFailAlloc_703_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_702_; 
v___x_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_702_, 0, v___x_697_);
lean_ctor_set(v___x_702_, 1, v___x_701_);
return v___x_702_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_setTraceCaption___boxed(lean_object* v_caption_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_, lean_object* v_a_713_, lean_object* v_a_714_, lean_object* v_a_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lake_setTraceCaption(v_caption_708_, v_a_709_, v_a_710_, v_a_711_, v_a_712_, v_a_713_, v_a_714_);
lean_dec_ref(v_a_713_);
lean_dec(v_a_712_);
lean_dec(v_a_711_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
return v_res_716_;
}
}
static lean_object* _init_l_Lake_takeTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l_Lake_takeTrace___redArg___closed__0));
v___x_719_ = l_Lake_BuildTrace_nil(v___x_718_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg(lean_object* v_a_720_){
_start:
{
lean_object* v_log_722_; uint8_t v_action_723_; uint8_t v_wantsRebuild_724_; lean_object* v_trace_725_; lean_object* v_buildTime_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_735_; 
v_log_722_ = lean_ctor_get(v_a_720_, 0);
v_action_723_ = lean_ctor_get_uint8(v_a_720_, sizeof(void*)*3);
v_wantsRebuild_724_ = lean_ctor_get_uint8(v_a_720_, sizeof(void*)*3 + 1);
v_trace_725_ = lean_ctor_get(v_a_720_, 1);
v_buildTime_726_ = lean_ctor_get(v_a_720_, 2);
v_isSharedCheck_735_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_735_ == 0)
{
v___x_728_ = v_a_720_;
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_buildTime_726_);
lean_inc(v_trace_725_);
lean_inc(v_log_722_);
lean_dec(v_a_720_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_735_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_log_722_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_734_, 2, v_buildTime_726_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, sizeof(void*)*3, v_action_723_);
lean_ctor_set_uint8(v_reuseFailAlloc_734_, sizeof(void*)*3 + 1, v_wantsRebuild_724_);
v___x_732_ = v_reuseFailAlloc_734_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_trace_725_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
return v___x_733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___redArg___boxed(lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Lake_takeTrace___redArg(v_a_736_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace(lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v_log_746_; uint8_t v_action_747_; uint8_t v_wantsRebuild_748_; lean_object* v_trace_749_; lean_object* v_buildTime_750_; lean_object* v___x_752_; uint8_t v_isShared_753_; uint8_t v_isSharedCheck_759_; 
v_log_746_ = lean_ctor_get(v_a_744_, 0);
v_action_747_ = lean_ctor_get_uint8(v_a_744_, sizeof(void*)*3);
v_wantsRebuild_748_ = lean_ctor_get_uint8(v_a_744_, sizeof(void*)*3 + 1);
v_trace_749_ = lean_ctor_get(v_a_744_, 1);
v_buildTime_750_ = lean_ctor_get(v_a_744_, 2);
v_isSharedCheck_759_ = !lean_is_exclusive(v_a_744_);
if (v_isSharedCheck_759_ == 0)
{
v___x_752_ = v_a_744_;
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
else
{
lean_inc(v_buildTime_750_);
lean_inc(v_trace_749_);
lean_inc(v_log_746_);
lean_dec(v_a_744_);
v___x_752_ = lean_box(0);
v_isShared_753_ = v_isSharedCheck_759_;
goto v_resetjp_751_;
}
v_resetjp_751_:
{
lean_object* v___x_754_; lean_object* v___x_756_; 
v___x_754_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
if (v_isShared_753_ == 0)
{
lean_ctor_set(v___x_752_, 1, v___x_754_);
v___x_756_ = v___x_752_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_log_746_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v___x_754_);
lean_ctor_set(v_reuseFailAlloc_758_, 2, v_buildTime_750_);
lean_ctor_set_uint8(v_reuseFailAlloc_758_, sizeof(void*)*3, v_action_747_);
lean_ctor_set_uint8(v_reuseFailAlloc_758_, sizeof(void*)*3 + 1, v_wantsRebuild_748_);
v___x_756_ = v_reuseFailAlloc_758_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_757_; 
v___x_757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_757_, 0, v_trace_749_);
lean_ctor_set(v___x_757_, 1, v___x_756_);
return v___x_757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeTrace___boxed(lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l_Lake_takeTrace(v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec(v_a_762_);
lean_dec(v_a_761_);
lean_dec_ref(v_a_760_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg(lean_object* v_trace_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_log_771_; uint8_t v_action_772_; uint8_t v_wantsRebuild_773_; lean_object* v_trace_774_; lean_object* v_buildTime_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_783_; 
v_log_771_ = lean_ctor_get(v_a_769_, 0);
v_action_772_ = lean_ctor_get_uint8(v_a_769_, sizeof(void*)*3);
v_wantsRebuild_773_ = lean_ctor_get_uint8(v_a_769_, sizeof(void*)*3 + 1);
v_trace_774_ = lean_ctor_get(v_a_769_, 1);
v_buildTime_775_ = lean_ctor_get(v_a_769_, 2);
v_isSharedCheck_783_ = !lean_is_exclusive(v_a_769_);
if (v_isSharedCheck_783_ == 0)
{
v___x_777_ = v_a_769_;
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_buildTime_775_);
lean_inc(v_trace_774_);
lean_inc(v_log_771_);
lean_dec(v_a_769_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_783_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v___x_780_; 
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 1, v_trace_768_);
v___x_780_ = v___x_777_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_log_771_);
lean_ctor_set(v_reuseFailAlloc_782_, 1, v_trace_768_);
lean_ctor_set(v_reuseFailAlloc_782_, 2, v_buildTime_775_);
lean_ctor_set_uint8(v_reuseFailAlloc_782_, sizeof(void*)*3, v_action_772_);
lean_ctor_set_uint8(v_reuseFailAlloc_782_, sizeof(void*)*3 + 1, v_wantsRebuild_773_);
v___x_780_ = v_reuseFailAlloc_782_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
lean_object* v___x_781_; 
v___x_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_781_, 0, v_trace_774_);
lean_ctor_set(v___x_781_, 1, v___x_780_);
return v___x_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___redArg___boxed(lean_object* v_trace_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lake_swapTrace___redArg(v_trace_784_, v_a_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace(lean_object* v_trace_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_log_796_; uint8_t v_action_797_; uint8_t v_wantsRebuild_798_; lean_object* v_trace_799_; lean_object* v_buildTime_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_808_; 
v_log_796_ = lean_ctor_get(v_a_794_, 0);
v_action_797_ = lean_ctor_get_uint8(v_a_794_, sizeof(void*)*3);
v_wantsRebuild_798_ = lean_ctor_get_uint8(v_a_794_, sizeof(void*)*3 + 1);
v_trace_799_ = lean_ctor_get(v_a_794_, 1);
v_buildTime_800_ = lean_ctor_get(v_a_794_, 2);
v_isSharedCheck_808_ = !lean_is_exclusive(v_a_794_);
if (v_isSharedCheck_808_ == 0)
{
v___x_802_ = v_a_794_;
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_buildTime_800_);
lean_inc(v_trace_799_);
lean_inc(v_log_796_);
lean_dec(v_a_794_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_808_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set(v___x_802_, 1, v_trace_788_);
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_log_796_);
lean_ctor_set(v_reuseFailAlloc_807_, 1, v_trace_788_);
lean_ctor_set(v_reuseFailAlloc_807_, 2, v_buildTime_800_);
lean_ctor_set_uint8(v_reuseFailAlloc_807_, sizeof(void*)*3, v_action_797_);
lean_ctor_set_uint8(v_reuseFailAlloc_807_, sizeof(void*)*3 + 1, v_wantsRebuild_798_);
v___x_805_ = v_reuseFailAlloc_807_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_806_; 
v___x_806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_806_, 0, v_trace_799_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
return v___x_806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_swapTrace___boxed(lean_object* v_trace_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Lake_swapTrace(v_trace_809_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_);
lean_dec_ref(v_a_814_);
lean_dec(v_a_813_);
lean_dec(v_a_812_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg(lean_object* v_trace_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_log_821_; uint8_t v_action_822_; uint8_t v_wantsRebuild_823_; lean_object* v_trace_824_; lean_object* v_buildTime_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_835_; 
v_log_821_ = lean_ctor_get(v_a_819_, 0);
v_action_822_ = lean_ctor_get_uint8(v_a_819_, sizeof(void*)*3);
v_wantsRebuild_823_ = lean_ctor_get_uint8(v_a_819_, sizeof(void*)*3 + 1);
v_trace_824_ = lean_ctor_get(v_a_819_, 1);
v_buildTime_825_ = lean_ctor_get(v_a_819_, 2);
v_isSharedCheck_835_ = !lean_is_exclusive(v_a_819_);
if (v_isSharedCheck_835_ == 0)
{
v___x_827_ = v_a_819_;
v_isShared_828_ = v_isSharedCheck_835_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_buildTime_825_);
lean_inc(v_trace_824_);
lean_inc(v_log_821_);
lean_dec(v_a_819_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_835_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_829_ = lean_box(0);
v___x_830_ = l_Lake_BuildTrace_mix(v_trace_824_, v_trace_818_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 1, v___x_830_);
v___x_832_ = v___x_827_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_log_821_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v___x_830_);
lean_ctor_set(v_reuseFailAlloc_834_, 2, v_buildTime_825_);
lean_ctor_set_uint8(v_reuseFailAlloc_834_, sizeof(void*)*3, v_action_822_);
lean_ctor_set_uint8(v_reuseFailAlloc_834_, sizeof(void*)*3 + 1, v_wantsRebuild_823_);
v___x_832_ = v_reuseFailAlloc_834_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
lean_object* v___x_833_; 
v___x_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_829_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
return v___x_833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace___redArg___boxed(lean_object* v_trace_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lake_addTrace___redArg(v_trace_836_, v_a_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lake_addTrace(lean_object* v_trace_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_log_848_; uint8_t v_action_849_; uint8_t v_wantsRebuild_850_; lean_object* v_trace_851_; lean_object* v_buildTime_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_862_; 
v_log_848_ = lean_ctor_get(v_a_846_, 0);
v_action_849_ = lean_ctor_get_uint8(v_a_846_, sizeof(void*)*3);
v_wantsRebuild_850_ = lean_ctor_get_uint8(v_a_846_, sizeof(void*)*3 + 1);
v_trace_851_ = lean_ctor_get(v_a_846_, 1);
v_buildTime_852_ = lean_ctor_get(v_a_846_, 2);
v_isSharedCheck_862_ = !lean_is_exclusive(v_a_846_);
if (v_isSharedCheck_862_ == 0)
{
v___x_854_ = v_a_846_;
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_buildTime_852_);
lean_inc(v_trace_851_);
lean_inc(v_log_848_);
lean_dec(v_a_846_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_862_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_859_; 
v___x_856_ = lean_box(0);
v___x_857_ = l_Lake_BuildTrace_mix(v_trace_851_, v_trace_840_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_857_);
v___x_859_ = v___x_854_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_log_848_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_buildTime_852_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*3, v_action_849_);
lean_ctor_set_uint8(v_reuseFailAlloc_861_, sizeof(void*)*3 + 1, v_wantsRebuild_850_);
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
lean_object* v_log_881_; uint8_t v_action_882_; uint8_t v_wantsRebuild_883_; lean_object* v_trace_884_; lean_object* v_buildTime_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_916_; 
v_log_881_ = lean_ctor_get(v_a_879_, 0);
v_action_882_ = lean_ctor_get_uint8(v_a_879_, sizeof(void*)*3);
v_wantsRebuild_883_ = lean_ctor_get_uint8(v_a_879_, sizeof(void*)*3 + 1);
v_trace_884_ = lean_ctor_get(v_a_879_, 1);
v_buildTime_885_ = lean_ctor_get(v_a_879_, 2);
v_isSharedCheck_916_ = !lean_is_exclusive(v_a_879_);
if (v_isSharedCheck_916_ == 0)
{
v___x_887_ = v_a_879_;
v_isShared_888_ = v_isSharedCheck_916_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_buildTime_885_);
lean_inc(v_trace_884_);
lean_inc(v_log_881_);
lean_dec(v_a_879_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_916_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = l_Lake_BuildTrace_nil(v_caption_872_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v___x_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_915_; 
v_reuseFailAlloc_915_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_915_, 0, v_log_881_);
lean_ctor_set(v_reuseFailAlloc_915_, 1, v___x_889_);
lean_ctor_set(v_reuseFailAlloc_915_, 2, v_buildTime_885_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3, v_action_882_);
lean_ctor_set_uint8(v_reuseFailAlloc_915_, sizeof(void*)*3 + 1, v_wantsRebuild_883_);
v___x_891_ = v_reuseFailAlloc_915_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_892_; 
lean_inc_ref(v_a_878_);
lean_inc(v_a_877_);
lean_inc(v_a_876_);
lean_inc(v_a_875_);
v___x_892_ = lean_apply_7(v_x_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v___x_891_, lean_box(0));
if (lean_obj_tag(v___x_892_) == 0)
{
lean_object* v_a_893_; lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_914_; 
v_a_893_ = lean_ctor_get(v___x_892_, 1);
v_a_894_ = lean_ctor_get(v___x_892_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_892_);
if (v_isSharedCheck_914_ == 0)
{
v___x_896_ = v___x_892_;
v_isShared_897_ = v_isSharedCheck_914_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_893_);
lean_inc(v_a_894_);
lean_dec(v___x_892_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_914_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v_log_898_; uint8_t v_action_899_; uint8_t v_wantsRebuild_900_; lean_object* v_trace_901_; lean_object* v_buildTime_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_913_; 
v_log_898_ = lean_ctor_get(v_a_893_, 0);
v_action_899_ = lean_ctor_get_uint8(v_a_893_, sizeof(void*)*3);
v_wantsRebuild_900_ = lean_ctor_get_uint8(v_a_893_, sizeof(void*)*3 + 1);
v_trace_901_ = lean_ctor_get(v_a_893_, 1);
v_buildTime_902_ = lean_ctor_get(v_a_893_, 2);
v_isSharedCheck_913_ = !lean_is_exclusive(v_a_893_);
if (v_isSharedCheck_913_ == 0)
{
v___x_904_ = v_a_893_;
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_buildTime_902_);
lean_inc(v_trace_901_);
lean_inc(v_log_898_);
lean_dec(v_a_893_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_908_; 
v___x_906_ = l_Lake_BuildTrace_mix(v_trace_884_, v_trace_901_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 1, v___x_906_);
v___x_908_ = v___x_904_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_log_898_);
lean_ctor_set(v_reuseFailAlloc_912_, 1, v___x_906_);
lean_ctor_set(v_reuseFailAlloc_912_, 2, v_buildTime_902_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3, v_action_899_);
lean_ctor_set_uint8(v_reuseFailAlloc_912_, sizeof(void*)*3 + 1, v_wantsRebuild_900_);
v___x_908_ = v_reuseFailAlloc_912_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
lean_object* v___x_910_; 
if (v_isShared_897_ == 0)
{
lean_ctor_set(v___x_896_, 1, v___x_908_);
v___x_910_ = v___x_896_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_894_);
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
lean_dec_ref(v_trace_884_);
return v___x_892_;
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
lean_dec(v_a_922_);
lean_dec(v_a_921_);
lean_dec(v_a_920_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace(lean_object* v_00_u03b1_927_, lean_object* v_caption_928_, lean_object* v_x_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_){
_start:
{
lean_object* v_log_937_; uint8_t v_action_938_; uint8_t v_wantsRebuild_939_; lean_object* v_trace_940_; lean_object* v_buildTime_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_972_; 
v_log_937_ = lean_ctor_get(v_a_935_, 0);
v_action_938_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*3);
v_wantsRebuild_939_ = lean_ctor_get_uint8(v_a_935_, sizeof(void*)*3 + 1);
v_trace_940_ = lean_ctor_get(v_a_935_, 1);
v_buildTime_941_ = lean_ctor_get(v_a_935_, 2);
v_isSharedCheck_972_ = !lean_is_exclusive(v_a_935_);
if (v_isSharedCheck_972_ == 0)
{
v___x_943_ = v_a_935_;
v_isShared_944_ = v_isSharedCheck_972_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_buildTime_941_);
lean_inc(v_trace_940_);
lean_inc(v_log_937_);
lean_dec(v_a_935_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_972_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_947_; 
v___x_945_ = l_Lake_BuildTrace_nil(v_caption_928_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 1, v___x_945_);
v___x_947_ = v___x_943_;
goto v_reusejp_946_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_log_937_);
lean_ctor_set(v_reuseFailAlloc_971_, 1, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_971_, 2, v_buildTime_941_);
lean_ctor_set_uint8(v_reuseFailAlloc_971_, sizeof(void*)*3, v_action_938_);
lean_ctor_set_uint8(v_reuseFailAlloc_971_, sizeof(void*)*3 + 1, v_wantsRebuild_939_);
v___x_947_ = v_reuseFailAlloc_971_;
goto v_reusejp_946_;
}
v_reusejp_946_:
{
lean_object* v___x_948_; 
lean_inc_ref(v_a_934_);
lean_inc(v_a_933_);
lean_inc(v_a_932_);
lean_inc(v_a_931_);
v___x_948_ = lean_apply_7(v_x_929_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v___x_947_, lean_box(0));
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_970_; 
v_a_949_ = lean_ctor_get(v___x_948_, 1);
v_a_950_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_970_ == 0)
{
v___x_952_ = v___x_948_;
v_isShared_953_ = v_isSharedCheck_970_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_949_);
lean_inc(v_a_950_);
lean_dec(v___x_948_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_970_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v_log_954_; uint8_t v_action_955_; uint8_t v_wantsRebuild_956_; lean_object* v_trace_957_; lean_object* v_buildTime_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_969_; 
v_log_954_ = lean_ctor_get(v_a_949_, 0);
v_action_955_ = lean_ctor_get_uint8(v_a_949_, sizeof(void*)*3);
v_wantsRebuild_956_ = lean_ctor_get_uint8(v_a_949_, sizeof(void*)*3 + 1);
v_trace_957_ = lean_ctor_get(v_a_949_, 1);
v_buildTime_958_ = lean_ctor_get(v_a_949_, 2);
v_isSharedCheck_969_ = !lean_is_exclusive(v_a_949_);
if (v_isSharedCheck_969_ == 0)
{
v___x_960_ = v_a_949_;
v_isShared_961_ = v_isSharedCheck_969_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_buildTime_958_);
lean_inc(v_trace_957_);
lean_inc(v_log_954_);
lean_dec(v_a_949_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_969_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = l_Lake_BuildTrace_mix(v_trace_940_, v_trace_957_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 1, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_log_954_);
lean_ctor_set(v_reuseFailAlloc_968_, 1, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_968_, 2, v_buildTime_958_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*3, v_action_955_);
lean_ctor_set_uint8(v_reuseFailAlloc_968_, sizeof(void*)*3 + 1, v_wantsRebuild_956_);
v___x_964_ = v_reuseFailAlloc_968_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_966_; 
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 1, v___x_964_);
v___x_966_ = v___x_952_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_950_);
lean_ctor_set(v_reuseFailAlloc_967_, 1, v___x_964_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
}
else
{
lean_dec_ref(v_trace_940_);
return v___x_948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_addSubTrace___boxed(lean_object* v_00_u03b1_973_, lean_object* v_caption_974_, lean_object* v_x_975_, lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lake_addSubTrace(v_00_u03b1_973_, v_caption_974_, v_x_975_, v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_);
lean_dec_ref(v_a_980_);
lean_dec(v_a_979_);
lean_dec(v_a_978_);
lean_dec(v_a_977_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg(lean_object* v_f_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; 
lean_inc_ref(v_a_990_);
lean_inc_ref(v_a_989_);
lean_inc(v_a_988_);
lean_inc(v_a_987_);
lean_inc(v_a_986_);
v___x_992_ = lean_apply_7(v_f_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, lean_box(0));
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___redArg___boxed(lean_object* v_f_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lake_SpawnM_ofFn___redArg(v_f_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_);
lean_dec_ref(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec(v_a_996_);
lean_dec(v_a_995_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn(lean_object* v_00_u03b1_1002_, lean_object* v_f_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v___x_1011_; 
lean_inc_ref(v_a_1009_);
lean_inc_ref(v_a_1008_);
lean_inc(v_a_1007_);
lean_inc(v_a_1006_);
lean_inc(v_a_1005_);
v___x_1011_ = lean_apply_7(v_f_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_, v_a_1009_, lean_box(0));
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_ofFn___boxed(lean_object* v_00_u03b1_1012_, lean_object* v_f_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Lake_SpawnM_ofFn(v_00_u03b1_1012_, v_f_1013_, v_a_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_);
lean_dec_ref(v_a_1019_);
lean_dec_ref(v_a_1018_);
lean_dec(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec(v_a_1015_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg(lean_object* v_self_1022_, lean_object* v_fetch_1023_, lean_object* v_pkg_x3f_1024_, lean_object* v_stack_1025_, lean_object* v_store_1026_, lean_object* v_ctx_1027_, lean_object* v_s_1028_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_apply_7(v_self_1022_, v_fetch_1023_, v_pkg_x3f_1024_, v_stack_1025_, v_store_1026_, v_ctx_1027_, v_s_1028_, lean_box(0));
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___redArg___boxed(lean_object* v_self_1031_, lean_object* v_fetch_1032_, lean_object* v_pkg_x3f_1033_, lean_object* v_stack_1034_, lean_object* v_store_1035_, lean_object* v_ctx_1036_, lean_object* v_s_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lake_SpawnM_toFn___redArg(v_self_1031_, v_fetch_1032_, v_pkg_x3f_1033_, v_stack_1034_, v_store_1035_, v_ctx_1036_, v_s_1037_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn(lean_object* v_00_u03b1_1040_, lean_object* v_self_1041_, lean_object* v_fetch_1042_, lean_object* v_pkg_x3f_1043_, lean_object* v_stack_1044_, lean_object* v_store_1045_, lean_object* v_ctx_1046_, lean_object* v_s_1047_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_apply_7(v_self_1041_, v_fetch_1042_, v_pkg_x3f_1043_, v_stack_1044_, v_store_1045_, v_ctx_1046_, v_s_1047_, lean_box(0));
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Lake_SpawnM_toFn___boxed(lean_object* v_00_u03b1_1050_, lean_object* v_self_1051_, lean_object* v_fetch_1052_, lean_object* v_pkg_x3f_1053_, lean_object* v_stack_1054_, lean_object* v_store_1055_, lean_object* v_ctx_1056_, lean_object* v_s_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lake_SpawnM_toFn(v_00_u03b1_1050_, v_self_1051_, v_fetch_1052_, v_pkg_x3f_1053_, v_stack_1054_, v_store_1055_, v_ctx_1056_, v_s_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg(lean_object* v_x_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_){
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
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___redArg___boxed(lean_object* v_x_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lake_JobM_runSpawnM___redArg(v_x_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec(v_a_1073_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM(lean_object* v_00_u03b1_1080_, lean_object* v_x_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_){
_start:
{
lean_object* v_trace_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v_trace_1089_ = lean_ctor_get(v_a_1087_, 1);
lean_inc_ref(v_trace_1089_);
lean_inc_ref(v_a_1086_);
lean_inc(v_a_1085_);
lean_inc(v_a_1084_);
lean_inc(v_a_1083_);
v___x_1090_ = lean_apply_7(v_x_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_trace_1089_, lean_box(0));
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
lean_ctor_set(v___x_1091_, 1, v_a_1087_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runSpawnM___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_x_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Lake_JobM_runSpawnM(v_00_u03b1_1092_, v_x_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_);
lean_dec_ref(v_a_1098_);
lean_dec(v_a_1097_);
lean_dec(v_a_1096_);
lean_dec(v_a_1095_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg(lean_object* v_x_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
uint8_t v___x_1112_; uint8_t v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1112_ = 0;
v___x_1113_ = 0;
v___x_1114_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1115_ = lean_unsigned_to_nat(0u);
v___x_1116_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1116_, 0, v_a_1110_);
lean_ctor_set(v___x_1116_, 1, v___x_1114_);
lean_ctor_set(v___x_1116_, 2, v___x_1115_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3, v___x_1112_);
lean_ctor_set_uint8(v___x_1116_, sizeof(void*)*3 + 1, v___x_1113_);
lean_inc_ref(v_a_1109_);
lean_inc(v_a_1108_);
lean_inc(v_a_1107_);
lean_inc(v_a_1106_);
v___x_1117_ = lean_apply_7(v_x_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v___x_1116_, lean_box(0));
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1127_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 1);
v_a_1119_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1121_ = v___x_1117_;
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1118_);
lean_inc(v_a_1119_);
lean_dec(v___x_1117_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1127_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v_log_1123_; lean_object* v___x_1125_; 
v_log_1123_ = lean_ctor_get(v_a_1118_, 0);
lean_inc_ref(v_log_1123_);
lean_dec(v_a_1118_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_log_1123_);
v___x_1125_ = v___x_1121_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1119_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_log_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_a_1128_ = lean_ctor_get(v___x_1117_, 1);
v_a_1129_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1131_ = v___x_1117_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1128_);
lean_inc(v_a_1129_);
lean_dec(v___x_1117_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_log_1133_; lean_object* v___x_1135_; 
v_log_1133_ = lean_ctor_get(v_a_1128_, 0);
lean_inc_ref(v_log_1133_);
lean_dec(v_a_1128_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 1, v_log_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1129_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_log_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___redArg___boxed(lean_object* v_x_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Lake_FetchM_runJobM___redArg(v_x_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
lean_dec_ref(v_a_1143_);
lean_dec(v_a_1142_);
lean_dec(v_a_1141_);
lean_dec(v_a_1140_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM(lean_object* v_00_u03b1_1147_, lean_object* v_x_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_){
_start:
{
uint8_t v___x_1156_; uint8_t v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1156_ = 0;
v___x_1157_ = 0;
v___x_1158_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1159_ = lean_unsigned_to_nat(0u);
v___x_1160_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1160_, 0, v_a_1154_);
lean_ctor_set(v___x_1160_, 1, v___x_1158_);
lean_ctor_set(v___x_1160_, 2, v___x_1159_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*3, v___x_1156_);
lean_ctor_set_uint8(v___x_1160_, sizeof(void*)*3 + 1, v___x_1157_);
lean_inc_ref(v_a_1153_);
lean_inc(v_a_1152_);
lean_inc(v_a_1151_);
lean_inc(v_a_1150_);
v___x_1161_ = lean_apply_7(v_x_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v___x_1160_, lean_box(0));
if (lean_obj_tag(v___x_1161_) == 0)
{
lean_object* v_a_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1171_; 
v_a_1162_ = lean_ctor_get(v___x_1161_, 1);
v_a_1163_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1165_ = v___x_1161_;
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1162_);
lean_inc(v_a_1163_);
lean_dec(v___x_1161_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1171_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v_log_1167_; lean_object* v___x_1169_; 
v_log_1167_ = lean_ctor_get(v_a_1162_, 0);
lean_inc_ref(v_log_1167_);
lean_dec(v_a_1162_);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 1, v_log_1167_);
v___x_1169_ = v___x_1165_;
goto v_reusejp_1168_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1163_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_log_1167_);
v___x_1169_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1168_;
}
v_reusejp_1168_:
{
return v___x_1169_;
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1181_; 
v_a_1172_ = lean_ctor_get(v___x_1161_, 1);
v_a_1173_ = lean_ctor_get(v___x_1161_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1161_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1175_ = v___x_1161_;
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1172_);
lean_inc(v_a_1173_);
lean_dec(v___x_1161_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1181_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v_log_1177_; lean_object* v___x_1179_; 
v_log_1177_ = lean_ctor_get(v_a_1172_, 0);
lean_inc_ref(v_log_1177_);
lean_dec(v_a_1172_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_log_1177_);
v___x_1179_ = v___x_1175_;
goto v_reusejp_1178_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1173_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_log_1177_);
v___x_1179_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1178_;
}
v_reusejp_1178_:
{
return v___x_1179_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_FetchM_runJobM___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_x_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lake_FetchM_runJobM(v_00_u03b1_1182_, v_x_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_, v_a_1189_);
lean_dec_ref(v_a_1188_);
lean_dec(v_a_1187_);
lean_dec(v_a_1186_);
lean_dec(v_a_1185_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg(lean_object* v_x_1194_, lean_object* v_a_1195_, lean_object* v_a_1196_, lean_object* v_a_1197_, lean_object* v_a_1198_, lean_object* v_a_1199_, lean_object* v_a_1200_){
_start:
{
lean_object* v_log_1202_; uint8_t v_action_1203_; uint8_t v_wantsRebuild_1204_; lean_object* v_trace_1205_; lean_object* v_buildTime_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1235_; 
v_log_1202_ = lean_ctor_get(v_a_1200_, 0);
v_action_1203_ = lean_ctor_get_uint8(v_a_1200_, sizeof(void*)*3);
v_wantsRebuild_1204_ = lean_ctor_get_uint8(v_a_1200_, sizeof(void*)*3 + 1);
v_trace_1205_ = lean_ctor_get(v_a_1200_, 1);
v_buildTime_1206_ = lean_ctor_get(v_a_1200_, 2);
v_isSharedCheck_1235_ = !lean_is_exclusive(v_a_1200_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1208_ = v_a_1200_;
v_isShared_1209_ = v_isSharedCheck_1235_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_buildTime_1206_);
lean_inc(v_trace_1205_);
lean_inc(v_log_1202_);
lean_dec(v_a_1200_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1235_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; 
lean_inc_ref(v_a_1199_);
lean_inc(v_a_1198_);
lean_inc(v_a_1197_);
lean_inc(v_a_1196_);
v___x_1210_ = lean_apply_7(v_x_1194_, v_a_1195_, v_a_1196_, v_a_1197_, v_a_1198_, v_a_1199_, v_log_1202_, lean_box(0));
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1222_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
v_a_1212_ = lean_ctor_get(v___x_1210_, 1);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1214_ = v___x_1210_;
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_inc(v_a_1211_);
lean_dec(v___x_1210_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1222_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v_a_1212_);
v___x_1217_ = v___x_1208_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1212_);
lean_ctor_set(v_reuseFailAlloc_1221_, 1, v_trace_1205_);
lean_ctor_set(v_reuseFailAlloc_1221_, 2, v_buildTime_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1221_, sizeof(void*)*3, v_action_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1221_, sizeof(void*)*3 + 1, v_wantsRebuild_1204_);
v___x_1217_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
lean_object* v___x_1219_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 1, v___x_1217_);
v___x_1219_ = v___x_1214_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1211_);
lean_ctor_set(v_reuseFailAlloc_1220_, 1, v___x_1217_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v_a_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1234_; 
v_a_1223_ = lean_ctor_get(v___x_1210_, 0);
v_a_1224_ = lean_ctor_get(v___x_1210_, 1);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1226_ = v___x_1210_;
v_isShared_1227_ = v_isSharedCheck_1234_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_a_1224_);
lean_inc(v_a_1223_);
lean_dec(v___x_1210_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1234_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1229_; 
if (v_isShared_1209_ == 0)
{
lean_ctor_set(v___x_1208_, 0, v_a_1224_);
v___x_1229_ = v___x_1208_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_a_1224_);
lean_ctor_set(v_reuseFailAlloc_1233_, 1, v_trace_1205_);
lean_ctor_set(v_reuseFailAlloc_1233_, 2, v_buildTime_1206_);
lean_ctor_set_uint8(v_reuseFailAlloc_1233_, sizeof(void*)*3, v_action_1203_);
lean_ctor_set_uint8(v_reuseFailAlloc_1233_, sizeof(void*)*3 + 1, v_wantsRebuild_1204_);
v___x_1229_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 1, v___x_1229_);
v___x_1231_ = v___x_1226_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1223_);
lean_ctor_set(v_reuseFailAlloc_1232_, 1, v___x_1229_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___redArg___boxed(lean_object* v_x_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_, lean_object* v_a_1239_, lean_object* v_a_1240_, lean_object* v_a_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Lake_JobM_runFetchM___redArg(v_x_1236_, v_a_1237_, v_a_1238_, v_a_1239_, v_a_1240_, v_a_1241_, v_a_1242_);
lean_dec_ref(v_a_1241_);
lean_dec(v_a_1240_);
lean_dec(v_a_1239_);
lean_dec(v_a_1238_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM(lean_object* v_00_u03b1_1245_, lean_object* v_x_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_){
_start:
{
lean_object* v_log_1254_; uint8_t v_action_1255_; uint8_t v_wantsRebuild_1256_; lean_object* v_trace_1257_; lean_object* v_buildTime_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1287_; 
v_log_1254_ = lean_ctor_get(v_a_1252_, 0);
v_action_1255_ = lean_ctor_get_uint8(v_a_1252_, sizeof(void*)*3);
v_wantsRebuild_1256_ = lean_ctor_get_uint8(v_a_1252_, sizeof(void*)*3 + 1);
v_trace_1257_ = lean_ctor_get(v_a_1252_, 1);
v_buildTime_1258_ = lean_ctor_get(v_a_1252_, 2);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_a_1252_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1260_ = v_a_1252_;
v_isShared_1261_ = v_isSharedCheck_1287_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_buildTime_1258_);
lean_inc(v_trace_1257_);
lean_inc(v_log_1254_);
lean_dec(v_a_1252_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1287_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; 
lean_inc_ref(v_a_1251_);
lean_inc(v_a_1250_);
lean_inc(v_a_1249_);
lean_inc(v_a_1248_);
v___x_1262_ = lean_apply_7(v_x_1246_, v_a_1247_, v_a_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_log_1254_, lean_box(0));
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1274_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_a_1264_ = lean_ctor_get(v___x_1262_, 1);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1266_ = v___x_1262_;
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1274_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_a_1264_);
v___x_1269_ = v___x_1260_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_a_1264_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_trace_1257_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_buildTime_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3, v_action_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1273_, sizeof(void*)*3 + 1, v_wantsRebuild_1256_);
v___x_1269_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
lean_object* v___x_1271_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v___x_1269_);
v___x_1271_ = v___x_1266_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1263_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1269_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v_a_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1286_; 
v_a_1275_ = lean_ctor_get(v___x_1262_, 0);
v_a_1276_ = lean_ctor_get(v___x_1262_, 1);
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1278_ = v___x_1262_;
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_a_1276_);
lean_inc(v_a_1275_);
lean_dec(v___x_1262_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1286_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___x_1281_; 
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_a_1276_);
v___x_1281_ = v___x_1260_;
goto v_reusejp_1280_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_a_1276_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_trace_1257_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_buildTime_1258_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*3, v_action_1255_);
lean_ctor_set_uint8(v_reuseFailAlloc_1285_, sizeof(void*)*3 + 1, v_wantsRebuild_1256_);
v___x_1281_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1280_;
}
v_reusejp_1280_:
{
lean_object* v___x_1283_; 
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_a_1275_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_JobM_runFetchM___boxed(lean_object* v_00_u03b1_1288_, lean_object* v_x_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lake_JobM_runFetchM(v_00_u03b1_1288_, v_x_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec(v_a_1291_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0(lean_object* v_inst_1300_, lean_object* v_caption_1301_, uint8_t v_optional_1302_, lean_object* v_toPure_1303_, lean_object* v_____do__lift_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1305_, 0, v_____do__lift_1304_);
lean_ctor_set(v___x_1305_, 1, v_inst_1300_);
lean_ctor_set(v___x_1305_, 2, v_caption_1301_);
lean_ctor_set_uint8(v___x_1305_, sizeof(void*)*3, v_optional_1302_);
v___x_1306_ = lean_apply_2(v_toPure_1303_, lean_box(0), v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg___lam__0___boxed(lean_object* v_inst_1307_, lean_object* v_caption_1308_, lean_object* v_optional_1309_, lean_object* v_toPure_1310_, lean_object* v_____do__lift_1311_){
_start:
{
uint8_t v_optional_boxed_1312_; lean_object* v_res_1313_; 
v_optional_boxed_1312_ = lean_unbox(v_optional_1309_);
v_res_1313_ = l_Lake_Job_bindTask___redArg___lam__0(v_inst_1307_, v_caption_1308_, v_optional_boxed_1312_, v_toPure_1310_, v_____do__lift_1311_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask___redArg(lean_object* v_inst_1314_, lean_object* v_inst_1315_, lean_object* v_f_1316_, lean_object* v_self_1317_){
_start:
{
lean_object* v_toApplicative_1318_; lean_object* v_toBind_1319_; lean_object* v_task_1320_; lean_object* v_caption_1321_; uint8_t v_optional_1322_; lean_object* v_toPure_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___f_1326_; lean_object* v___x_1327_; 
v_toApplicative_1318_ = lean_ctor_get(v_inst_1314_, 0);
lean_inc_ref(v_toApplicative_1318_);
v_toBind_1319_ = lean_ctor_get(v_inst_1314_, 1);
lean_inc(v_toBind_1319_);
lean_dec_ref(v_inst_1314_);
v_task_1320_ = lean_ctor_get(v_self_1317_, 0);
lean_inc_ref(v_task_1320_);
v_caption_1321_ = lean_ctor_get(v_self_1317_, 2);
lean_inc_ref(v_caption_1321_);
v_optional_1322_ = lean_ctor_get_uint8(v_self_1317_, sizeof(void*)*3);
lean_dec_ref(v_self_1317_);
v_toPure_1323_ = lean_ctor_get(v_toApplicative_1318_, 1);
lean_inc(v_toPure_1323_);
lean_dec_ref(v_toApplicative_1318_);
v___x_1324_ = lean_apply_1(v_f_1316_, v_task_1320_);
v___x_1325_ = lean_box(v_optional_1322_);
v___f_1326_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1326_, 0, v_inst_1315_);
lean_closure_set(v___f_1326_, 1, v_caption_1321_);
lean_closure_set(v___f_1326_, 2, v___x_1325_);
lean_closure_set(v___f_1326_, 3, v_toPure_1323_);
v___x_1327_ = lean_apply_4(v_toBind_1319_, lean_box(0), lean_box(0), v___x_1324_, v___f_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindTask(lean_object* v_m_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_00_u03b1_1330_, lean_object* v_inst_1331_, lean_object* v_inst_1332_, lean_object* v_f_1333_, lean_object* v_self_1334_){
_start:
{
lean_object* v_toApplicative_1335_; lean_object* v_toBind_1336_; lean_object* v_task_1337_; lean_object* v_caption_1338_; uint8_t v_optional_1339_; lean_object* v_toPure_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___f_1343_; lean_object* v___x_1344_; 
v_toApplicative_1335_ = lean_ctor_get(v_inst_1331_, 0);
lean_inc_ref(v_toApplicative_1335_);
v_toBind_1336_ = lean_ctor_get(v_inst_1331_, 1);
lean_inc(v_toBind_1336_);
lean_dec_ref(v_inst_1331_);
v_task_1337_ = lean_ctor_get(v_self_1334_, 0);
lean_inc_ref(v_task_1337_);
v_caption_1338_ = lean_ctor_get(v_self_1334_, 2);
lean_inc_ref(v_caption_1338_);
v_optional_1339_ = lean_ctor_get_uint8(v_self_1334_, sizeof(void*)*3);
lean_dec_ref(v_self_1334_);
v_toPure_1340_ = lean_ctor_get(v_toApplicative_1335_, 1);
lean_inc(v_toPure_1340_);
lean_dec_ref(v_toApplicative_1335_);
v___x_1341_ = lean_apply_1(v_f_1333_, v_task_1337_);
v___x_1342_ = lean_box(v_optional_1339_);
v___f_1343_ = lean_alloc_closure((void*)(l_Lake_Job_bindTask___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_1343_, 0, v_inst_1332_);
lean_closure_set(v___f_1343_, 1, v_caption_1338_);
lean_closure_set(v___f_1343_, 2, v___x_1342_);
lean_closure_set(v___f_1343_, 3, v_toPure_1340_);
v___x_1344_ = lean_apply_4(v_toBind_1336_, lean_box(0), lean_box(0), v___x_1341_, v___f_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lake_Job_sync_spec__0(lean_object* v_msg_1346_){
_start:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; 
v___x_1347_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_1348_ = lean_panic_fn(v___x_1347_, v_msg_1346_);
return v___x_1348_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0(lean_object* v_val_1349_, lean_object* v_val_1350_, lean_object* v_a_x3f_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1354_ = lean_get_set_stdout(v_val_1349_);
lean_dec_ref(v___x_1354_);
v___x_1355_ = lean_get_set_stderr(v_val_1350_);
lean_dec_ref(v___x_1355_);
v___x_1356_ = lean_box(0);
v___x_1357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
lean_ctor_set(v___x_1357_, 1, v___y_1352_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__0___boxed(lean_object* v_val_1358_, lean_object* v_val_1359_, lean_object* v_a_x3f_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Lake_Job_sync___redArg___lam__0(v_val_1358_, v_val_1359_, v_a_x3f_1360_, v___y_1361_);
lean_dec(v_a_x3f_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1(lean_object* v_a_1364_, lean_object* v_____r_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_a_1364_);
lean_ctor_set(v___x_1373_, 1, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___lam__1___boxed(lean_object* v_a_1374_, lean_object* v_____r_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Lake_Job_sync___redArg___lam__1(v_a_1374_, v_____r_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1383_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__0(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1384_ = lean_unsigned_to_nat(0u);
v___x_1385_ = l_ByteArray_empty;
v___x_1386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1386_, 0, v___x_1385_);
lean_ctor_set(v___x_1386_, 1, v___x_1384_);
return v___x_1386_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__2(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1391_ = 0;
v___x_1392_ = 0;
v___x_1393_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1394_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
lean_ctor_set(v___x_1394_, 1, v___x_1390_);
lean_ctor_set(v___x_1394_, 2, v___x_1389_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*3, v___x_1392_);
lean_ctor_set_uint8(v___x_1394_, sizeof(void*)*3 + 1, v___x_1391_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lake_Job_sync___redArg___closed__7(void){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1399_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__6));
v___x_1400_ = lean_unsigned_to_nat(46u);
v___x_1401_ = lean_unsigned_to_nat(193u);
v___x_1402_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__5));
v___x_1403_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__4));
v___x_1404_ = l_mkPanicMessageWithDecl(v___x_1403_, v___x_1402_, v___x_1401_, v___x_1400_, v___x_1399_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg(lean_object* v_inst_1405_, lean_object* v_act_1406_, lean_object* v_caption_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_){
_start:
{
lean_object* v_val_1415_; lean_object* v___y_1420_; lean_object* v_a_1422_; lean_object* v_a_1423_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1425_ = lean_unsigned_to_nat(0u);
v___x_1426_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1427_ = lean_st_mk_ref(v___x_1426_);
lean_inc(v___x_1427_);
v___x_1428_ = l_IO_FS_Stream_ofBuffer(v___x_1427_);
lean_inc_ref(v___x_1428_);
v___x_1429_ = lean_get_set_stdout(v___x_1428_);
v___x_1430_ = lean_get_set_stderr(v___x_1428_);
v___x_1431_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__2, &l_Lake_Job_sync___redArg___closed__2_once, _init_l_Lake_Job_sync___redArg___closed__2);
lean_inc_ref(v_a_1412_);
lean_inc(v_a_1411_);
lean_inc(v_a_1410_);
lean_inc(v_a_1409_);
lean_inc_ref(v_a_1408_);
v___x_1432_ = lean_apply_7(v_act_1406_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v___x_1431_, lean_box(0));
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_a_1433_; lean_object* v_a_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v_a_1437_; lean_object* v___x_1438_; lean_object* v_log_1439_; uint8_t v_action_1440_; uint8_t v_wantsRebuild_1441_; lean_object* v_trace_1442_; lean_object* v_buildTime_1443_; lean_object* v_data_1444_; lean_object* v___y_1446_; uint8_t v___x_1471_; 
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
v_a_1434_ = lean_ctor_get(v___x_1432_, 1);
lean_inc(v_a_1434_);
lean_dec_ref(v___x_1432_);
lean_inc(v_a_1433_);
v___x_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1435_, 0, v_a_1433_);
v___x_1436_ = l_Lake_Job_sync___redArg___lam__0(v___x_1429_, v___x_1430_, v___x_1435_, v_a_1434_);
lean_dec_ref(v___x_1435_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 1);
lean_inc(v_a_1437_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = lean_st_ref_get(v___x_1427_);
lean_dec(v___x_1427_);
v_log_1439_ = lean_ctor_get(v_a_1437_, 0);
v_action_1440_ = lean_ctor_get_uint8(v_a_1437_, sizeof(void*)*3);
v_wantsRebuild_1441_ = lean_ctor_get_uint8(v_a_1437_, sizeof(void*)*3 + 1);
v_trace_1442_ = lean_ctor_get(v_a_1437_, 1);
v_buildTime_1443_ = lean_ctor_get(v_a_1437_, 2);
v_data_1444_ = lean_ctor_get(v___x_1438_, 0);
lean_inc_ref(v_data_1444_);
lean_dec(v___x_1438_);
v___x_1471_ = lean_string_validate_utf8(v_data_1444_);
if (v___x_1471_ == 0)
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
lean_dec_ref(v_data_1444_);
v___x_1472_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1473_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1472_);
v___y_1446_ = v___x_1473_;
goto v___jp_1445_;
}
else
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_string_from_utf8_unchecked(v_data_1444_);
v___y_1446_ = v___x_1474_;
goto v___jp_1445_;
}
v___jp_1445_:
{
lean_object* v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = lean_string_utf8_byte_size(v___y_1446_);
v___x_1448_ = lean_nat_dec_eq(v___x_1447_, v___x_1425_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1465_; 
lean_inc(v_buildTime_1443_);
lean_inc_ref(v_trace_1442_);
lean_inc_ref(v_log_1439_);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_a_1437_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; lean_object* v_unused_1467_; lean_object* v_unused_1468_; 
v_unused_1466_ = lean_ctor_get(v_a_1437_, 2);
lean_dec(v_unused_1466_);
v_unused_1467_ = lean_ctor_get(v_a_1437_, 1);
lean_dec(v_unused_1467_);
v_unused_1468_ = lean_ctor_get(v_a_1437_, 0);
lean_dec(v_unused_1468_);
v___x_1450_ = v_a_1437_;
v_isShared_1451_ = v_isSharedCheck_1465_;
goto v_resetjp_1449_;
}
else
{
lean_dec(v_a_1437_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1465_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; uint8_t v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1452_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1453_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1453_, 0, v___y_1446_);
lean_ctor_set(v___x_1453_, 1, v___x_1425_);
lean_ctor_set(v___x_1453_, 2, v___x_1447_);
v___x_1454_ = l_String_Slice_trimAscii(v___x_1453_);
v___x_1455_ = l_String_Slice_toString(v___x_1454_);
lean_dec_ref(v___x_1454_);
v___x_1456_ = lean_string_append(v___x_1452_, v___x_1455_);
lean_dec_ref(v___x_1455_);
v___x_1457_ = 1;
v___x_1458_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set_uint8(v___x_1458_, sizeof(void*)*1, v___x_1457_);
v___x_1459_ = lean_box(0);
v___x_1460_ = lean_array_push(v_log_1439_, v___x_1458_);
if (v_isShared_1451_ == 0)
{
lean_ctor_set(v___x_1450_, 0, v___x_1460_);
v___x_1462_ = v___x_1450_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1460_);
lean_ctor_set(v_reuseFailAlloc_1464_, 1, v_trace_1442_);
lean_ctor_set(v_reuseFailAlloc_1464_, 2, v_buildTime_1443_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*3, v_action_1440_);
lean_ctor_set_uint8(v_reuseFailAlloc_1464_, sizeof(void*)*3 + 1, v_wantsRebuild_1441_);
v___x_1462_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Lake_Job_sync___redArg___lam__1(v_a_1433_, v___x_1459_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v___x_1462_);
lean_dec_ref(v_a_1408_);
v___y_1420_ = v___x_1463_;
goto v___jp_1419_;
}
}
}
else
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec_ref(v___y_1446_);
v___x_1469_ = lean_box(0);
v___x_1470_ = l_Lake_Job_sync___redArg___lam__1(v_a_1433_, v___x_1469_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1437_);
lean_dec_ref(v_a_1408_);
v___y_1420_ = v___x_1470_;
goto v___jp_1419_;
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v_a_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v_a_1479_; 
lean_dec(v___x_1427_);
lean_dec_ref(v_a_1408_);
v_a_1475_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1475_);
v_a_1476_ = lean_ctor_get(v___x_1432_, 1);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1432_);
v___x_1477_ = lean_box(0);
v___x_1478_ = l_Lake_Job_sync___redArg___lam__0(v___x_1429_, v___x_1430_, v___x_1477_, v_a_1476_);
v_a_1479_ = lean_ctor_get(v___x_1478_, 1);
lean_inc(v_a_1479_);
lean_dec_ref(v___x_1478_);
v_a_1422_ = v_a_1475_;
v_a_1423_ = v_a_1479_;
goto v___jp_1421_;
}
v___jp_1414_:
{
lean_object* v___x_1416_; uint8_t v___x_1417_; lean_object* v___x_1418_; 
v___x_1416_ = lean_task_pure(v_val_1415_);
v___x_1417_ = 0;
v___x_1418_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1418_, 0, v___x_1416_);
lean_ctor_set(v___x_1418_, 1, v_inst_1405_);
lean_ctor_set(v___x_1418_, 2, v_caption_1407_);
lean_ctor_set_uint8(v___x_1418_, sizeof(void*)*3, v___x_1417_);
return v___x_1418_;
}
v___jp_1419_:
{
v_val_1415_ = v___y_1420_;
goto v___jp_1414_;
}
v___jp_1421_:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1424_, 0, v_a_1422_);
lean_ctor_set(v___x_1424_, 1, v_a_1423_);
v_val_1415_ = v___x_1424_;
goto v___jp_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___redArg___boxed(lean_object* v_inst_1480_, lean_object* v_act_1481_, lean_object* v_caption_1482_, lean_object* v_a_1483_, lean_object* v_a_1484_, lean_object* v_a_1485_, lean_object* v_a_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Lake_Job_sync___redArg(v_inst_1480_, v_act_1481_, v_caption_1482_, v_a_1483_, v_a_1484_, v_a_1485_, v_a_1486_, v_a_1487_);
lean_dec_ref(v_a_1487_);
lean_dec(v_a_1486_);
lean_dec(v_a_1485_);
lean_dec(v_a_1484_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync(lean_object* v_00_u03b1_1490_, lean_object* v_inst_1491_, lean_object* v_act_1492_, lean_object* v_caption_1493_, lean_object* v_a_1494_, lean_object* v_a_1495_, lean_object* v_a_1496_, lean_object* v_a_1497_, lean_object* v_a_1498_, lean_object* v_a_1499_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lake_Job_sync___redArg(v_inst_1491_, v_act_1492_, v_caption_1493_, v_a_1494_, v_a_1495_, v_a_1496_, v_a_1497_, v_a_1498_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_sync___boxed(lean_object* v_00_u03b1_1502_, lean_object* v_inst_1503_, lean_object* v_act_1504_, lean_object* v_caption_1505_, lean_object* v_a_1506_, lean_object* v_a_1507_, lean_object* v_a_1508_, lean_object* v_a_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lake_Job_sync(v_00_u03b1_1502_, v_inst_1503_, v_act_1504_, v_caption_1505_, v_a_1506_, v_a_1507_, v_a_1508_, v_a_1509_, v_a_1510_, v_a_1511_);
lean_dec_ref(v_a_1511_);
lean_dec_ref(v_a_1510_);
lean_dec(v_a_1509_);
lean_dec(v_a_1508_);
lean_dec(v_a_1507_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1(lean_object* v___x_1514_, lean_object* v___x_1515_, uint8_t v___x_1516_, uint8_t v___x_1517_, lean_object* v___x_1518_, lean_object* v___x_1519_, lean_object* v_act_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_a_1528_; lean_object* v_a_1529_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; 
v___x_1531_ = lean_st_mk_ref(v___x_1514_);
lean_inc(v___x_1531_);
v___x_1532_ = l_IO_FS_Stream_ofBuffer(v___x_1531_);
lean_inc_ref(v___x_1532_);
v___x_1533_ = lean_get_set_stdout(v___x_1532_);
v___x_1534_ = lean_get_set_stderr(v___x_1532_);
lean_inc(v___x_1519_);
v___x_1535_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1535_, 0, v___x_1515_);
lean_ctor_set(v___x_1535_, 1, v___x_1518_);
lean_ctor_set(v___x_1535_, 2, v___x_1519_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*3, v___x_1516_);
lean_ctor_set_uint8(v___x_1535_, sizeof(void*)*3 + 1, v___x_1517_);
lean_inc_ref(v_a_1525_);
lean_inc(v_a_1524_);
lean_inc(v_a_1523_);
lean_inc(v_a_1522_);
v___x_1536_ = lean_apply_7(v_act_1520_, v_a_1521_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_, v___x_1535_, lean_box(0));
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1583_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_a_1538_ = lean_ctor_get(v___x_1536_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1540_ = v___x_1536_;
v_isShared_1541_ = v_isSharedCheck_1583_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1583_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___y_1543_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v_a_1549_; lean_object* v___x_1550_; lean_object* v_log_1551_; uint8_t v_action_1552_; uint8_t v_wantsRebuild_1553_; lean_object* v_trace_1554_; lean_object* v_buildTime_1555_; lean_object* v___y_1557_; lean_object* v_data_1578_; uint8_t v___x_1579_; 
lean_inc(v_a_1537_);
v___x_1547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1547_, 0, v_a_1537_);
v___x_1548_ = l_Lake_Job_sync___redArg___lam__0(v___x_1533_, v___x_1534_, v___x_1547_, v_a_1538_);
lean_dec_ref(v___x_1547_);
v_a_1549_ = lean_ctor_get(v___x_1548_, 1);
lean_inc(v_a_1549_);
lean_dec_ref(v___x_1548_);
v___x_1550_ = lean_st_ref_get(v___x_1531_);
lean_dec(v___x_1531_);
v_log_1551_ = lean_ctor_get(v_a_1549_, 0);
v_action_1552_ = lean_ctor_get_uint8(v_a_1549_, sizeof(void*)*3);
v_wantsRebuild_1553_ = lean_ctor_get_uint8(v_a_1549_, sizeof(void*)*3 + 1);
v_trace_1554_ = lean_ctor_get(v_a_1549_, 1);
v_buildTime_1555_ = lean_ctor_get(v_a_1549_, 2);
v_data_1578_ = lean_ctor_get(v___x_1550_, 0);
lean_inc_ref(v_data_1578_);
lean_dec(v___x_1550_);
v___x_1579_ = lean_string_validate_utf8(v_data_1578_);
if (v___x_1579_ == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; 
lean_dec_ref(v_data_1578_);
v___x_1580_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1581_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1580_);
v___y_1557_ = v___x_1581_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1582_; 
v___x_1582_ = lean_string_from_utf8_unchecked(v_data_1578_);
v___y_1557_ = v___x_1582_;
goto v___jp_1556_;
}
v___jp_1542_:
{
lean_object* v___x_1545_; 
if (v_isShared_1541_ == 0)
{
lean_ctor_set(v___x_1540_, 1, v___y_1543_);
v___x_1545_ = v___x_1540_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1537_);
lean_ctor_set(v_reuseFailAlloc_1546_, 1, v___y_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
v___jp_1556_:
{
lean_object* v___x_1558_; uint8_t v___x_1559_; 
v___x_1558_ = lean_string_utf8_byte_size(v___y_1557_);
v___x_1559_ = lean_nat_dec_eq(v___x_1558_, v___x_1519_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1574_; 
lean_inc(v_buildTime_1555_);
lean_inc_ref(v_trace_1554_);
lean_inc_ref(v_log_1551_);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_a_1549_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; 
v_unused_1575_ = lean_ctor_get(v_a_1549_, 2);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_a_1549_, 1);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_a_1549_, 0);
lean_dec(v_unused_1577_);
v___x_1561_ = v_a_1549_;
v_isShared_1562_ = v_isSharedCheck_1574_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v_a_1549_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1574_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; uint8_t v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1563_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1564_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1564_, 0, v___y_1557_);
lean_ctor_set(v___x_1564_, 1, v___x_1519_);
lean_ctor_set(v___x_1564_, 2, v___x_1558_);
v___x_1565_ = l_String_Slice_trimAscii(v___x_1564_);
v___x_1566_ = l_String_Slice_toString(v___x_1565_);
lean_dec_ref(v___x_1565_);
v___x_1567_ = lean_string_append(v___x_1563_, v___x_1566_);
lean_dec_ref(v___x_1566_);
v___x_1568_ = 1;
v___x_1569_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1569_, 0, v___x_1567_);
lean_ctor_set_uint8(v___x_1569_, sizeof(void*)*1, v___x_1568_);
v___x_1570_ = lean_array_push(v_log_1551_, v___x_1569_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1570_);
v___x_1572_ = v___x_1561_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v___x_1570_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_trace_1554_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v_buildTime_1555_);
lean_ctor_set_uint8(v_reuseFailAlloc_1573_, sizeof(void*)*3, v_action_1552_);
lean_ctor_set_uint8(v_reuseFailAlloc_1573_, sizeof(void*)*3 + 1, v_wantsRebuild_1553_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
v___y_1543_ = v___x_1572_;
goto v___jp_1542_;
}
}
}
else
{
lean_dec_ref(v___y_1557_);
lean_dec(v___x_1519_);
v___y_1543_ = v_a_1549_;
goto v___jp_1542_;
}
}
}
}
else
{
lean_object* v_a_1584_; lean_object* v_a_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_a_1588_; 
lean_dec(v___x_1531_);
lean_dec(v___x_1519_);
v_a_1584_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1584_);
v_a_1585_ = lean_ctor_get(v___x_1536_, 1);
lean_inc(v_a_1585_);
lean_dec_ref(v___x_1536_);
v___x_1586_ = lean_box(0);
v___x_1587_ = l_Lake_Job_sync___redArg___lam__0(v___x_1533_, v___x_1534_, v___x_1586_, v_a_1585_);
v_a_1588_ = lean_ctor_get(v___x_1587_, 1);
lean_inc(v_a_1588_);
lean_dec_ref(v___x_1587_);
v_a_1528_ = v_a_1584_;
v_a_1529_ = v_a_1588_;
goto v___jp_1527_;
}
v___jp_1527_:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1530_, 0, v_a_1528_);
lean_ctor_set(v___x_1530_, 1, v_a_1529_);
return v___x_1530_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___lam__1___boxed(lean_object* v___x_1589_, lean_object* v___x_1590_, lean_object* v___x_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v___x_1594_, lean_object* v_act_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v___x_22647__boxed_1602_; uint8_t v___x_22648__boxed_1603_; lean_object* v_res_1604_; 
v___x_22647__boxed_1602_ = lean_unbox(v___x_1591_);
v___x_22648__boxed_1603_ = lean_unbox(v___x_1592_);
v_res_1604_ = l_Lake_Job_async___redArg___lam__1(v___x_1589_, v___x_1590_, v___x_22647__boxed_1602_, v___x_22648__boxed_1603_, v___x_1593_, v___x_1594_, v_act_1595_, v_a_1596_, v_a_1597_, v_a_1598_, v_a_1599_, v_a_1600_);
lean_dec_ref(v_a_1600_);
lean_dec(v_a_1599_);
lean_dec(v_a_1598_);
lean_dec(v_a_1597_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg(lean_object* v_inst_1605_, lean_object* v_act_1606_, lean_object* v_prio_1607_, lean_object* v_caption_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; uint8_t v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___f_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1617_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_1618_ = 0;
v___x_1619_ = 0;
v___x_1620_ = lean_obj_once(&l_Lake_takeTrace___redArg___closed__1, &l_Lake_takeTrace___redArg___closed__1_once, _init_l_Lake_takeTrace___redArg___closed__1);
v___x_1621_ = lean_box(v___x_1618_);
v___x_1622_ = lean_box(v___x_1619_);
lean_inc_ref(v_a_1613_);
lean_inc(v_a_1612_);
lean_inc(v_a_1611_);
lean_inc(v_a_1610_);
v___f_1623_ = lean_alloc_closure((void*)(l_Lake_Job_async___redArg___lam__1___boxed), 13, 12);
lean_closure_set(v___f_1623_, 0, v___x_1616_);
lean_closure_set(v___f_1623_, 1, v___x_1617_);
lean_closure_set(v___f_1623_, 2, v___x_1621_);
lean_closure_set(v___f_1623_, 3, v___x_1622_);
lean_closure_set(v___f_1623_, 4, v___x_1620_);
lean_closure_set(v___f_1623_, 5, v___x_1615_);
lean_closure_set(v___f_1623_, 6, v_act_1606_);
lean_closure_set(v___f_1623_, 7, v_a_1609_);
lean_closure_set(v___f_1623_, 8, v_a_1610_);
lean_closure_set(v___f_1623_, 9, v_a_1611_);
lean_closure_set(v___f_1623_, 10, v_a_1612_);
lean_closure_set(v___f_1623_, 11, v_a_1613_);
v___x_1624_ = lean_io_as_task(v___f_1623_, v_prio_1607_);
v___x_1625_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_1625_, 0, v___x_1624_);
lean_ctor_set(v___x_1625_, 1, v_inst_1605_);
lean_ctor_set(v___x_1625_, 2, v_caption_1608_);
lean_ctor_set_uint8(v___x_1625_, sizeof(void*)*3, v___x_1619_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___redArg___boxed(lean_object* v_inst_1626_, lean_object* v_act_1627_, lean_object* v_prio_1628_, lean_object* v_caption_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lake_Job_async___redArg(v_inst_1626_, v_act_1627_, v_prio_1628_, v_caption_1629_, v_a_1630_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_);
lean_dec_ref(v_a_1634_);
lean_dec(v_a_1633_);
lean_dec(v_a_1632_);
lean_dec(v_a_1631_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async(lean_object* v_00_u03b1_1637_, lean_object* v_inst_1638_, lean_object* v_act_1639_, lean_object* v_prio_1640_, lean_object* v_caption_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lake_Job_async___redArg(v_inst_1638_, v_act_1639_, v_prio_1640_, v_caption_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_async___boxed(lean_object* v_00_u03b1_1650_, lean_object* v_inst_1651_, lean_object* v_act_1652_, lean_object* v_prio_1653_, lean_object* v_caption_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Lake_Job_async(v_00_u03b1_1650_, v_inst_1651_, v_act_1652_, v_prio_1653_, v_caption_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_);
lean_dec_ref(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec(v_a_1657_);
lean_dec(v_a_1656_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg(lean_object* v_self_1663_){
_start:
{
lean_object* v_task_1665_; lean_object* v___x_1666_; 
v_task_1665_ = lean_ctor_get(v_self_1663_, 0);
lean_inc_ref(v_task_1665_);
lean_dec_ref(v_self_1663_);
v___x_1666_ = lean_io_wait(v_task_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait___redArg___boxed(lean_object* v_self_1667_, lean_object* v_a_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lake_Job_wait___redArg(v_self_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait(lean_object* v_00_u03b1_1670_, lean_object* v_self_1671_){
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
LEAN_EXPORT lean_object* l_Lake_Job_wait___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_self_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Lake_Job_wait(v_00_u03b1_1675_, v_self_1676_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg(lean_object* v_self_1679_){
_start:
{
lean_object* v_task_1681_; lean_object* v___x_1682_; 
v_task_1681_ = lean_ctor_get(v_self_1679_, 0);
lean_inc_ref(v_task_1681_);
lean_dec_ref(v_self_1679_);
v___x_1682_ = lean_io_wait(v_task_1681_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1684_, 0, v_a_1683_);
return v___x_1684_;
}
else
{
lean_object* v___x_1685_; 
lean_dec_ref(v___x_1682_);
v___x_1685_ = lean_box(0);
return v___x_1685_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___redArg___boxed(lean_object* v_self_1686_, lean_object* v_a_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lake_Job_wait_x3f___redArg(v_self_1686_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f(lean_object* v_00_u03b1_1689_, lean_object* v_self_1690_){
_start:
{
lean_object* v_task_1692_; lean_object* v___x_1693_; 
v_task_1692_ = lean_ctor_get(v_self_1690_, 0);
lean_inc_ref(v_task_1692_);
lean_dec_ref(v_self_1690_);
v___x_1693_ = lean_io_wait(v_task_1692_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1695_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
lean_inc(v_a_1694_);
lean_dec_ref(v___x_1693_);
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v_a_1694_);
return v___x_1695_;
}
else
{
lean_object* v___x_1696_; 
lean_dec_ref(v___x_1693_);
v___x_1696_ = lean_box(0);
return v___x_1696_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_wait_x3f___boxed(lean_object* v_00_u03b1_1697_, lean_object* v_self_1698_, lean_object* v_a_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Lake_Job_wait_x3f(v_00_u03b1_1697_, v_self_1698_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(lean_object* v_as_1701_, size_t v_i_1702_, size_t v_stop_1703_, lean_object* v_b_1704_, lean_object* v___y_1705_){
_start:
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_usize_dec_eq(v_i_1702_, v_stop_1703_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; 
v___x_1708_ = lean_array_uget_borrowed(v_as_1701_, v_i_1702_);
v___x_1709_ = lean_box(0);
lean_inc(v___x_1708_);
v___x_1710_ = lean_array_push(v___y_1705_, v___x_1708_);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = lean_usize_add(v_i_1702_, v___x_1711_);
v_i_1702_ = v___x_1712_;
v_b_1704_ = v___x_1709_;
v___y_1705_ = v___x_1710_;
goto _start;
}
else
{
lean_object* v___x_1714_; 
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_b_1704_);
lean_ctor_set(v___x_1714_, 1, v___y_1705_);
return v___x_1714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0___boxed(lean_object* v_as_1715_, lean_object* v_i_1716_, lean_object* v_stop_1717_, lean_object* v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
size_t v_i_boxed_1721_; size_t v_stop_boxed_1722_; lean_object* v_res_1723_; 
v_i_boxed_1721_ = lean_unbox_usize(v_i_1716_);
lean_dec(v_i_1716_);
v_stop_boxed_1722_ = lean_unbox_usize(v_stop_1717_);
lean_dec(v_stop_1717_);
v_res_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_as_1715_, v_i_boxed_1721_, v_stop_boxed_1722_, v_b_1718_, v___y_1719_);
lean_dec_ref(v_as_1715_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg(lean_object* v_self_1724_, lean_object* v_a_1725_){
_start:
{
lean_object* v_task_1727_; lean_object* v___x_1728_; 
v_task_1727_ = lean_ctor_get(v_self_1724_, 0);
lean_inc_ref(v_task_1727_);
lean_dec_ref(v_self_1724_);
v___x_1728_ = lean_io_wait(v_task_1727_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; lean_object* v_a_1730_; lean_object* v___x_1732_; uint8_t v_isShared_1733_; uint8_t v_isSharedCheck_1763_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
v_a_1730_ = lean_ctor_get(v___x_1728_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1732_ = v___x_1728_;
v_isShared_1733_ = v_isSharedCheck_1763_;
goto v_resetjp_1731_;
}
else
{
lean_inc(v_a_1730_);
lean_inc(v_a_1729_);
lean_dec(v___x_1728_);
v___x_1732_ = lean_box(0);
v_isShared_1733_ = v_isSharedCheck_1763_;
goto v_resetjp_1731_;
}
v_resetjp_1731_:
{
lean_object* v_a_1735_; lean_object* v___y_1740_; lean_object* v_log_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_log_1751_ = lean_ctor_get(v_a_1730_, 0);
lean_inc_ref(v_log_1751_);
lean_dec(v_a_1730_);
v___x_1752_ = lean_unsigned_to_nat(0u);
v___x_1753_ = lean_array_get_size(v_log_1751_);
v___x_1754_ = lean_nat_dec_lt(v___x_1752_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec_ref(v_log_1751_);
v_a_1735_ = v_a_1725_;
goto v___jp_1734_;
}
else
{
lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1755_ = lean_box(0);
v___x_1756_ = lean_nat_dec_le(v___x_1753_, v___x_1753_);
if (v___x_1756_ == 0)
{
if (v___x_1754_ == 0)
{
lean_dec_ref(v_log_1751_);
v_a_1735_ = v_a_1725_;
goto v___jp_1734_;
}
else
{
size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = ((size_t)0ULL);
v___x_1758_ = lean_usize_of_nat(v___x_1753_);
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1751_, v___x_1757_, v___x_1758_, v___x_1755_, v_a_1725_);
lean_dec_ref(v_log_1751_);
v___y_1740_ = v___x_1759_;
goto v___jp_1739_;
}
}
else
{
size_t v___x_1760_; size_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1760_ = ((size_t)0ULL);
v___x_1761_ = lean_usize_of_nat(v___x_1753_);
v___x_1762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1751_, v___x_1760_, v___x_1761_, v___x_1755_, v_a_1725_);
lean_dec_ref(v_log_1751_);
v___y_1740_ = v___x_1762_;
goto v___jp_1739_;
}
}
v___jp_1734_:
{
lean_object* v___x_1737_; 
if (v_isShared_1733_ == 0)
{
lean_ctor_set(v___x_1732_, 1, v_a_1735_);
v___x_1737_ = v___x_1732_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1729_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_a_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
v___jp_1739_:
{
if (lean_obj_tag(v___y_1740_) == 0)
{
lean_object* v_a_1741_; 
v_a_1741_ = lean_ctor_get(v___y_1740_, 1);
lean_inc(v_a_1741_);
lean_dec_ref(v___y_1740_);
v_a_1735_ = v_a_1741_;
goto v___jp_1734_;
}
else
{
lean_object* v_a_1742_; lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_del_object(v___x_1732_);
lean_dec(v_a_1729_);
v_a_1742_ = lean_ctor_get(v___y_1740_, 0);
v_a_1743_ = lean_ctor_get(v___y_1740_, 1);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___y_1740_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___y_1740_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_inc(v_a_1742_);
lean_dec(v___y_1740_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1742_);
lean_ctor_set(v_reuseFailAlloc_1749_, 1, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1798_; 
v_a_1764_ = lean_ctor_get(v___x_1728_, 0);
v_a_1765_ = lean_ctor_get(v___x_1728_, 1);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1767_ = v___x_1728_;
v_isShared_1768_ = v_isSharedCheck_1798_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_inc(v_a_1764_);
lean_dec(v___x_1728_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1798_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_a_1770_; lean_object* v___y_1775_; lean_object* v_log_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_log_1786_ = lean_ctor_get(v_a_1765_, 0);
lean_inc_ref(v_log_1786_);
lean_dec(v_a_1765_);
v___x_1787_ = lean_unsigned_to_nat(0u);
v___x_1788_ = lean_array_get_size(v_log_1786_);
v___x_1789_ = lean_nat_dec_lt(v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_dec_ref(v_log_1786_);
v_a_1770_ = v_a_1725_;
goto v___jp_1769_;
}
else
{
lean_object* v___x_1790_; uint8_t v___x_1791_; 
v___x_1790_ = lean_box(0);
v___x_1791_ = lean_nat_dec_le(v___x_1788_, v___x_1788_);
if (v___x_1791_ == 0)
{
if (v___x_1789_ == 0)
{
lean_dec_ref(v_log_1786_);
v_a_1770_ = v_a_1725_;
goto v___jp_1769_;
}
else
{
size_t v___x_1792_; size_t v___x_1793_; lean_object* v___x_1794_; 
v___x_1792_ = ((size_t)0ULL);
v___x_1793_ = lean_usize_of_nat(v___x_1788_);
v___x_1794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1786_, v___x_1792_, v___x_1793_, v___x_1790_, v_a_1725_);
lean_dec_ref(v_log_1786_);
v___y_1775_ = v___x_1794_;
goto v___jp_1774_;
}
}
else
{
size_t v___x_1795_; size_t v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = ((size_t)0ULL);
v___x_1796_ = lean_usize_of_nat(v___x_1788_);
v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1786_, v___x_1795_, v___x_1796_, v___x_1790_, v_a_1725_);
lean_dec_ref(v_log_1786_);
v___y_1775_ = v___x_1797_;
goto v___jp_1774_;
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
v___jp_1774_:
{
if (lean_obj_tag(v___y_1775_) == 0)
{
lean_object* v_a_1776_; 
v_a_1776_ = lean_ctor_get(v___y_1775_, 1);
lean_inc(v_a_1776_);
lean_dec_ref(v___y_1775_);
v_a_1770_ = v_a_1776_;
goto v___jp_1769_;
}
else
{
lean_object* v_a_1777_; lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_del_object(v___x_1767_);
lean_dec(v_a_1764_);
v_a_1777_ = lean_ctor_get(v___y_1775_, 0);
v_a_1778_ = lean_ctor_get(v___y_1775_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___y_1775_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___y_1775_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_inc(v_a_1777_);
lean_dec(v___y_1775_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1777_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___boxed(lean_object* v_self_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Lake_Job_await___redArg(v_self_1799_, v_a_1800_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await(lean_object* v_00_u03b1_1803_, lean_object* v_self_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Lake_Job_await___redArg(v_self_1804_, v_a_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___boxed(lean_object* v_00_u03b1_1808_, lean_object* v_self_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Lake_Job_await(v_00_u03b1_1808_, v_self_1809_, v_a_1810_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1(lean_object* v_a_1813_, lean_object* v_f_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_x_1820_){
_start:
{
lean_object* v_a_1823_; lean_object* v_a_1824_; 
if (lean_obj_tag(v_x_1820_) == 0)
{
lean_object* v_a_1826_; lean_object* v_a_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v_log_1834_; uint8_t v_action_1835_; uint8_t v_wantsRebuild_1836_; lean_object* v_trace_1837_; lean_object* v_buildTime_1838_; lean_object* v___x_1840_; uint8_t v_isShared_1841_; uint8_t v_isSharedCheck_1899_; 
v_a_1826_ = lean_ctor_get(v_x_1820_, 0);
lean_inc(v_a_1826_);
v_a_1827_ = lean_ctor_get(v_x_1820_, 1);
lean_inc(v_a_1827_);
lean_dec_ref(v_x_1820_);
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1830_ = lean_st_mk_ref(v___x_1829_);
lean_inc(v___x_1830_);
v___x_1831_ = l_IO_FS_Stream_ofBuffer(v___x_1830_);
lean_inc_ref(v___x_1831_);
v___x_1832_ = lean_get_set_stdout(v___x_1831_);
v___x_1833_ = lean_get_set_stderr(v___x_1831_);
v_log_1834_ = lean_ctor_get(v_a_1827_, 0);
v_action_1835_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3);
v_wantsRebuild_1836_ = lean_ctor_get_uint8(v_a_1827_, sizeof(void*)*3 + 1);
v_trace_1837_ = lean_ctor_get(v_a_1827_, 1);
v_buildTime_1838_ = lean_ctor_get(v_a_1827_, 2);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_a_1827_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1840_ = v_a_1827_;
v_isShared_1841_ = v_isSharedCheck_1899_;
goto v_resetjp_1839_;
}
else
{
lean_inc(v_buildTime_1838_);
lean_inc(v_trace_1837_);
lean_inc(v_log_1834_);
lean_dec(v_a_1827_);
v___x_1840_ = lean_box(0);
v_isShared_1841_ = v_isSharedCheck_1899_;
goto v_resetjp_1839_;
}
v_resetjp_1839_:
{
lean_object* v_trace_1842_; lean_object* v___x_1844_; 
lean_inc_ref(v_a_1813_);
v_trace_1842_ = l_Lake_BuildTrace_mix(v_a_1813_, v_trace_1837_);
if (v_isShared_1841_ == 0)
{
lean_ctor_set(v___x_1840_, 1, v_trace_1842_);
v___x_1844_ = v___x_1840_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_log_1834_);
lean_ctor_set(v_reuseFailAlloc_1898_, 1, v_trace_1842_);
lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_buildTime_1838_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*3, v_action_1835_);
lean_ctor_set_uint8(v_reuseFailAlloc_1898_, sizeof(void*)*3 + 1, v_wantsRebuild_1836_);
v___x_1844_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1845_; 
lean_inc_ref(v_a_1819_);
lean_inc(v_a_1818_);
lean_inc(v_a_1817_);
lean_inc(v_a_1816_);
v___x_1845_ = lean_apply_8(v_f_1814_, v_a_1826_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v___x_1844_, lean_box(0));
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1892_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_a_1847_ = lean_ctor_get(v___x_1845_, 1);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1849_ = v___x_1845_;
v_isShared_1850_ = v_isSharedCheck_1892_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1892_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___y_1852_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v_a_1858_; lean_object* v___x_1859_; lean_object* v_log_1860_; uint8_t v_action_1861_; uint8_t v_wantsRebuild_1862_; lean_object* v_trace_1863_; lean_object* v_buildTime_1864_; lean_object* v___y_1866_; lean_object* v_data_1887_; uint8_t v___x_1888_; 
lean_inc(v_a_1846_);
v___x_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1856_, 0, v_a_1846_);
v___x_1857_ = l_Lake_Job_sync___redArg___lam__0(v___x_1832_, v___x_1833_, v___x_1856_, v_a_1847_);
lean_dec_ref(v___x_1856_);
v_a_1858_ = lean_ctor_get(v___x_1857_, 1);
lean_inc(v_a_1858_);
lean_dec_ref(v___x_1857_);
v___x_1859_ = lean_st_ref_get(v___x_1830_);
lean_dec(v___x_1830_);
v_log_1860_ = lean_ctor_get(v_a_1858_, 0);
v_action_1861_ = lean_ctor_get_uint8(v_a_1858_, sizeof(void*)*3);
v_wantsRebuild_1862_ = lean_ctor_get_uint8(v_a_1858_, sizeof(void*)*3 + 1);
v_trace_1863_ = lean_ctor_get(v_a_1858_, 1);
v_buildTime_1864_ = lean_ctor_get(v_a_1858_, 2);
v_data_1887_ = lean_ctor_get(v___x_1859_, 0);
lean_inc_ref(v_data_1887_);
lean_dec(v___x_1859_);
v___x_1888_ = lean_string_validate_utf8(v_data_1887_);
if (v___x_1888_ == 0)
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
lean_dec_ref(v_data_1887_);
v___x_1889_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1890_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1889_);
v___y_1866_ = v___x_1890_;
goto v___jp_1865_;
}
else
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_string_from_utf8_unchecked(v_data_1887_);
v___y_1866_ = v___x_1891_;
goto v___jp_1865_;
}
v___jp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 1, v___y_1852_);
v___x_1854_ = v___x_1849_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1846_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v___y_1852_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
v___jp_1865_:
{
lean_object* v___x_1867_; uint8_t v___x_1868_; 
v___x_1867_ = lean_string_utf8_byte_size(v___y_1866_);
v___x_1868_ = lean_nat_dec_eq(v___x_1867_, v___x_1828_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1883_; 
lean_inc(v_buildTime_1864_);
lean_inc_ref(v_trace_1863_);
lean_inc_ref(v_log_1860_);
v_isSharedCheck_1883_ = !lean_is_exclusive(v_a_1858_);
if (v_isSharedCheck_1883_ == 0)
{
lean_object* v_unused_1884_; lean_object* v_unused_1885_; lean_object* v_unused_1886_; 
v_unused_1884_ = lean_ctor_get(v_a_1858_, 2);
lean_dec(v_unused_1884_);
v_unused_1885_ = lean_ctor_get(v_a_1858_, 1);
lean_dec(v_unused_1885_);
v_unused_1886_ = lean_ctor_get(v_a_1858_, 0);
lean_dec(v_unused_1886_);
v___x_1870_ = v_a_1858_;
v_isShared_1871_ = v_isSharedCheck_1883_;
goto v_resetjp_1869_;
}
else
{
lean_dec(v_a_1858_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1883_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1881_; 
v___x_1872_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1873_, 0, v___y_1866_);
lean_ctor_set(v___x_1873_, 1, v___x_1828_);
lean_ctor_set(v___x_1873_, 2, v___x_1867_);
v___x_1874_ = l_String_Slice_trimAscii(v___x_1873_);
v___x_1875_ = l_String_Slice_toString(v___x_1874_);
lean_dec_ref(v___x_1874_);
v___x_1876_ = lean_string_append(v___x_1872_, v___x_1875_);
lean_dec_ref(v___x_1875_);
v___x_1877_ = 1;
v___x_1878_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1878_, 0, v___x_1876_);
lean_ctor_set_uint8(v___x_1878_, sizeof(void*)*1, v___x_1877_);
v___x_1879_ = lean_array_push(v_log_1860_, v___x_1878_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 0, v___x_1879_);
v___x_1881_ = v___x_1870_;
goto v_reusejp_1880_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v___x_1879_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_trace_1863_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v_buildTime_1864_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*3, v_action_1861_);
lean_ctor_set_uint8(v_reuseFailAlloc_1882_, sizeof(void*)*3 + 1, v_wantsRebuild_1862_);
v___x_1881_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1880_;
}
v_reusejp_1880_:
{
v___y_1852_ = v___x_1881_;
goto v___jp_1851_;
}
}
}
else
{
lean_dec_ref(v___y_1866_);
v___y_1852_ = v_a_1858_;
goto v___jp_1851_;
}
}
}
}
else
{
lean_object* v_a_1893_; lean_object* v_a_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v_a_1897_; 
lean_dec(v___x_1830_);
v_a_1893_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1893_);
v_a_1894_ = lean_ctor_get(v___x_1845_, 1);
lean_inc(v_a_1894_);
lean_dec_ref(v___x_1845_);
v___x_1895_ = lean_box(0);
v___x_1896_ = l_Lake_Job_sync___redArg___lam__0(v___x_1832_, v___x_1833_, v___x_1895_, v_a_1894_);
v_a_1897_ = lean_ctor_get(v___x_1896_, 1);
lean_inc(v_a_1897_);
lean_dec_ref(v___x_1896_);
v_a_1823_ = v_a_1893_;
v_a_1824_ = v_a_1897_;
goto v___jp_1822_;
}
}
}
}
else
{
lean_object* v_a_1900_; lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1908_; 
lean_dec_ref(v_a_1815_);
lean_dec_ref(v_f_1814_);
v_a_1900_ = lean_ctor_get(v_x_1820_, 0);
v_a_1901_ = lean_ctor_get(v_x_1820_, 1);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_x_1820_);
if (v_isSharedCheck_1908_ == 0)
{
v___x_1903_ = v_x_1820_;
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_inc(v_a_1900_);
lean_dec(v_x_1820_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1908_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1906_; 
if (v_isShared_1904_ == 0)
{
v___x_1906_ = v___x_1903_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_a_1900_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_a_1901_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
v___jp_1822_:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1825_, 0, v_a_1823_);
lean_ctor_set(v___x_1825_, 1, v_a_1824_);
return v___x_1825_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1___boxed(lean_object* v_a_1909_, lean_object* v_f_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_, lean_object* v_a_1914_, lean_object* v_a_1915_, lean_object* v_x_1916_, lean_object* v___y_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Lake_Job_mapM___redArg___lam__1(v_a_1909_, v_f_1910_, v_a_1911_, v_a_1912_, v_a_1913_, v_a_1914_, v_a_1915_, v_x_1916_);
lean_dec_ref(v_a_1915_);
lean_dec(v_a_1914_);
lean_dec(v_a_1913_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1909_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object* v_kind_1919_, lean_object* v_self_1920_, lean_object* v_f_1921_, lean_object* v_prio_1922_, uint8_t v_sync_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_, lean_object* v_a_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_){
_start:
{
lean_object* v_task_1931_; lean_object* v_caption_1932_; uint8_t v_optional_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1942_; 
v_task_1931_ = lean_ctor_get(v_self_1920_, 0);
v_caption_1932_ = lean_ctor_get(v_self_1920_, 2);
v_optional_1933_ = lean_ctor_get_uint8(v_self_1920_, sizeof(void*)*3);
v_isSharedCheck_1942_ = !lean_is_exclusive(v_self_1920_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v_self_1920_, 1);
lean_dec(v_unused_1943_);
v___x_1935_ = v_self_1920_;
v_isShared_1936_ = v_isSharedCheck_1942_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_caption_1932_);
lean_inc(v_task_1931_);
lean_dec(v_self_1920_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1942_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___f_1937_; lean_object* v___x_1938_; lean_object* v___x_1940_; 
lean_inc_ref(v_a_1928_);
lean_inc(v_a_1927_);
lean_inc(v_a_1926_);
lean_inc(v_a_1925_);
lean_inc_ref(v_a_1929_);
v___f_1937_ = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__1___boxed), 9, 7);
lean_closure_set(v___f_1937_, 0, v_a_1929_);
lean_closure_set(v___f_1937_, 1, v_f_1921_);
lean_closure_set(v___f_1937_, 2, v_a_1924_);
lean_closure_set(v___f_1937_, 3, v_a_1925_);
lean_closure_set(v___f_1937_, 4, v_a_1926_);
lean_closure_set(v___f_1937_, 5, v_a_1927_);
lean_closure_set(v___f_1937_, 6, v_a_1928_);
v___x_1938_ = lean_io_map_task(v___f_1937_, v_task_1931_, v_prio_1922_, v_sync_1923_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v_kind_1919_);
lean_ctor_set(v___x_1935_, 0, v___x_1938_);
v___x_1940_ = v___x_1935_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1938_);
lean_ctor_set(v_reuseFailAlloc_1941_, 1, v_kind_1919_);
lean_ctor_set(v_reuseFailAlloc_1941_, 2, v_caption_1932_);
lean_ctor_set_uint8(v_reuseFailAlloc_1941_, sizeof(void*)*3, v_optional_1933_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object* v_kind_1944_, lean_object* v_self_1945_, lean_object* v_f_1946_, lean_object* v_prio_1947_, lean_object* v_sync_1948_, lean_object* v_a_1949_, lean_object* v_a_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_, lean_object* v_a_1955_){
_start:
{
uint8_t v_sync_boxed_1956_; lean_object* v_res_1957_; 
v_sync_boxed_1956_ = lean_unbox(v_sync_1948_);
v_res_1957_ = l_Lake_Job_mapM___redArg(v_kind_1944_, v_self_1945_, v_f_1946_, v_prio_1947_, v_sync_boxed_1956_, v_a_1949_, v_a_1950_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
lean_dec_ref(v_a_1954_);
lean_dec_ref(v_a_1953_);
lean_dec(v_a_1952_);
lean_dec(v_a_1951_);
lean_dec(v_a_1950_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object* v_00_u03b2_1958_, lean_object* v_00_u03b1_1959_, lean_object* v_kind_1960_, lean_object* v_self_1961_, lean_object* v_f_1962_, lean_object* v_prio_1963_, uint8_t v_sync_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_, lean_object* v_a_1969_, lean_object* v_a_1970_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Lake_Job_mapM___redArg(v_kind_1960_, v_self_1961_, v_f_1962_, v_prio_1963_, v_sync_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_, v_a_1969_, v_a_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object* v_00_u03b2_1973_, lean_object* v_00_u03b1_1974_, lean_object* v_kind_1975_, lean_object* v_self_1976_, lean_object* v_f_1977_, lean_object* v_prio_1978_, lean_object* v_sync_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_, lean_object* v_a_1986_){
_start:
{
uint8_t v_sync_boxed_1987_; lean_object* v_res_1988_; 
v_sync_boxed_1987_ = lean_unbox(v_sync_1979_);
v_res_1988_ = l_Lake_Job_mapM(v_00_u03b2_1973_, v_00_u03b1_1974_, v_kind_1975_, v_self_1976_, v_f_1977_, v_prio_1978_, v_sync_boxed_1987_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_, v_a_1984_, v_a_1985_);
lean_dec_ref(v_a_1985_);
lean_dec_ref(v_a_1984_);
lean_dec(v_a_1983_);
lean_dec(v_a_1982_);
lean_dec(v_a_1981_);
return v_res_1988_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object* v_val_1989_, lean_object* v_val_1990_, lean_object* v_a_x3f_1991_, lean_object* v___y_1992_){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1994_ = lean_get_set_stdout(v_val_1989_);
lean_dec_ref(v___x_1994_);
v___x_1995_ = lean_get_set_stderr(v_val_1990_);
lean_dec_ref(v___x_1995_);
v___x_1996_ = lean_box(0);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v___y_1992_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0___boxed(lean_object* v_val_1998_, lean_object* v_val_1999_, lean_object* v_a_x3f_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_){
_start:
{
lean_object* v_res_2003_; 
v_res_2003_ = l_Lake_Job_bindM___redArg___lam__0(v_val_1998_, v_val_1999_, v_a_x3f_2000_, v___y_2001_);
lean_dec(v_a_x3f_2000_);
return v_res_2003_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object* v_a_2004_, lean_object* v_x_2005_){
_start:
{
if (lean_obj_tag(v_x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v_a_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2029_; 
v_a_2006_ = lean_ctor_get(v_x_2005_, 0);
v_a_2007_ = lean_ctor_get(v_x_2005_, 1);
v_isSharedCheck_2029_ = !lean_is_exclusive(v_x_2005_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2009_ = v_x_2005_;
v_isShared_2010_ = v_isSharedCheck_2029_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_a_2007_);
lean_inc(v_a_2006_);
lean_dec(v_x_2005_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2029_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; lean_object* v_log_2012_; uint8_t v_action_2013_; uint8_t v_wantsRebuild_2014_; lean_object* v_buildTime_2015_; lean_object* v_trace_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2026_; 
lean_inc(v_a_2007_);
v___x_2011_ = l_Lake_JobState_merge(v_a_2004_, v_a_2007_);
v_log_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc_ref(v_log_2012_);
v_action_2013_ = lean_ctor_get_uint8(v___x_2011_, sizeof(void*)*3);
v_wantsRebuild_2014_ = lean_ctor_get_uint8(v___x_2011_, sizeof(void*)*3 + 1);
v_buildTime_2015_ = lean_ctor_get(v___x_2011_, 2);
lean_inc(v_buildTime_2015_);
lean_dec_ref(v___x_2011_);
v_trace_2016_ = lean_ctor_get(v_a_2007_, 1);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_a_2007_);
if (v_isSharedCheck_2026_ == 0)
{
lean_object* v_unused_2027_; lean_object* v_unused_2028_; 
v_unused_2027_ = lean_ctor_get(v_a_2007_, 2);
lean_dec(v_unused_2027_);
v_unused_2028_ = lean_ctor_get(v_a_2007_, 0);
lean_dec(v_unused_2028_);
v___x_2018_ = v_a_2007_;
v_isShared_2019_ = v_isSharedCheck_2026_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_trace_2016_);
lean_dec(v_a_2007_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2026_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 2, v_buildTime_2015_);
lean_ctor_set(v___x_2018_, 0, v_log_2012_);
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_log_2012_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_trace_2016_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_buildTime_2015_);
v___x_2021_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
lean_object* v___x_2023_; 
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*3, v_action_2013_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*3 + 1, v_wantsRebuild_2014_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___x_2021_);
v___x_2023_ = v___x_2009_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2006_);
lean_ctor_set(v_reuseFailAlloc_2024_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v_a_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2056_; 
v_a_2030_ = lean_ctor_get(v_x_2005_, 0);
v_a_2031_ = lean_ctor_get(v_x_2005_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_x_2005_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2033_ = v_x_2005_;
v_isShared_2034_ = v_isSharedCheck_2056_;
goto v_resetjp_2032_;
}
else
{
lean_inc(v_a_2031_);
lean_inc(v_a_2030_);
lean_dec(v_x_2005_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2056_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v_log_2035_; lean_object* v___x_2036_; lean_object* v_log_2037_; uint8_t v_action_2038_; uint8_t v_wantsRebuild_2039_; lean_object* v_buildTime_2040_; lean_object* v_trace_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2053_; 
v_log_2035_ = lean_ctor_get(v_a_2004_, 0);
lean_inc_ref(v_log_2035_);
lean_inc(v_a_2031_);
v___x_2036_ = l_Lake_JobState_merge(v_a_2004_, v_a_2031_);
v_log_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc_ref(v_log_2037_);
v_action_2038_ = lean_ctor_get_uint8(v___x_2036_, sizeof(void*)*3);
v_wantsRebuild_2039_ = lean_ctor_get_uint8(v___x_2036_, sizeof(void*)*3 + 1);
v_buildTime_2040_ = lean_ctor_get(v___x_2036_, 2);
lean_inc(v_buildTime_2040_);
lean_dec_ref(v___x_2036_);
v_trace_2041_ = lean_ctor_get(v_a_2031_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_a_2031_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; lean_object* v_unused_2055_; 
v_unused_2054_ = lean_ctor_get(v_a_2031_, 2);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_a_2031_, 0);
lean_dec(v_unused_2055_);
v___x_2043_ = v_a_2031_;
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_trace_2041_);
lean_dec(v_a_2031_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2053_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2045_ = lean_array_get_size(v_log_2035_);
lean_dec_ref(v_log_2035_);
v___x_2046_ = lean_nat_add(v___x_2045_, v_a_2030_);
lean_dec(v_a_2030_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 2, v_buildTime_2040_);
lean_ctor_set(v___x_2043_, 0, v_log_2037_);
v___x_2048_ = v___x_2043_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_log_2037_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v_trace_2041_);
lean_ctor_set(v_reuseFailAlloc_2052_, 2, v_buildTime_2040_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*3, v_action_2038_);
lean_ctor_set_uint8(v___x_2048_, sizeof(void*)*3 + 1, v_wantsRebuild_2039_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 1, v___x_2048_);
lean_ctor_set(v___x_2033_, 0, v___x_2046_);
v___x_2050_ = v___x_2033_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2048_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object* v_a_2057_, lean_object* v_____r_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v___x_2066_; 
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v_a_2057_);
lean_ctor_set(v___x_2066_, 1, v___y_2064_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2___boxed(lean_object* v_a_2067_, lean_object* v_____r_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v_res_2076_; 
v_res_2076_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2067_, v_____r_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3(lean_object* v_a_2077_, lean_object* v_f_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_prio_2084_, lean_object* v_x_2085_){
_start:
{
lean_object* v_a_2088_; lean_object* v_a_2089_; lean_object* v___y_2093_; 
if (lean_obj_tag(v_x_2085_) == 0)
{
lean_object* v_a_2102_; lean_object* v_a_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v_log_2110_; uint8_t v_action_2111_; uint8_t v_wantsRebuild_2112_; lean_object* v_trace_2113_; lean_object* v_buildTime_2114_; lean_object* v___x_2116_; uint8_t v_isShared_2117_; uint8_t v_isSharedCheck_2170_; 
v_a_2102_ = lean_ctor_get(v_x_2085_, 0);
lean_inc(v_a_2102_);
v_a_2103_ = lean_ctor_get(v_x_2085_, 1);
lean_inc(v_a_2103_);
lean_dec_ref(v_x_2085_);
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_2106_ = lean_st_mk_ref(v___x_2105_);
lean_inc(v___x_2106_);
v___x_2107_ = l_IO_FS_Stream_ofBuffer(v___x_2106_);
lean_inc_ref(v___x_2107_);
v___x_2108_ = lean_get_set_stdout(v___x_2107_);
v___x_2109_ = lean_get_set_stderr(v___x_2107_);
v_log_2110_ = lean_ctor_get(v_a_2103_, 0);
v_action_2111_ = lean_ctor_get_uint8(v_a_2103_, sizeof(void*)*3);
v_wantsRebuild_2112_ = lean_ctor_get_uint8(v_a_2103_, sizeof(void*)*3 + 1);
v_trace_2113_ = lean_ctor_get(v_a_2103_, 1);
v_buildTime_2114_ = lean_ctor_get(v_a_2103_, 2);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_a_2103_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2116_ = v_a_2103_;
v_isShared_2117_ = v_isSharedCheck_2170_;
goto v_resetjp_2115_;
}
else
{
lean_inc(v_buildTime_2114_);
lean_inc(v_trace_2113_);
lean_inc(v_log_2110_);
lean_dec(v_a_2103_);
v___x_2116_ = lean_box(0);
v_isShared_2117_ = v_isSharedCheck_2170_;
goto v_resetjp_2115_;
}
v_resetjp_2115_:
{
lean_object* v_trace_2118_; lean_object* v___x_2120_; 
lean_inc_ref(v_a_2077_);
v_trace_2118_ = l_Lake_BuildTrace_mix(v_a_2077_, v_trace_2113_);
if (v_isShared_2117_ == 0)
{
lean_ctor_set(v___x_2116_, 1, v_trace_2118_);
v___x_2120_ = v___x_2116_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_log_2110_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v_trace_2118_);
lean_ctor_set(v_reuseFailAlloc_2169_, 2, v_buildTime_2114_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*3, v_action_2111_);
lean_ctor_set_uint8(v_reuseFailAlloc_2169_, sizeof(void*)*3 + 1, v_wantsRebuild_2112_);
v___x_2120_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2121_; 
lean_inc_ref(v_a_2083_);
lean_inc(v_a_2082_);
lean_inc(v_a_2081_);
lean_inc(v_a_2080_);
lean_inc_ref(v_a_2079_);
v___x_2121_ = lean_apply_8(v_f_2078_, v_a_2102_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v___x_2120_, lean_box(0));
if (lean_obj_tag(v___x_2121_) == 0)
{
lean_object* v_a_2122_; lean_object* v_a_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v_a_2126_; lean_object* v___x_2127_; lean_object* v_log_2128_; uint8_t v_action_2129_; uint8_t v_wantsRebuild_2130_; lean_object* v_trace_2131_; lean_object* v_buildTime_2132_; lean_object* v_data_2133_; lean_object* v___y_2135_; uint8_t v___x_2160_; 
v_a_2122_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2122_);
v_a_2123_ = lean_ctor_get(v___x_2121_, 1);
lean_inc(v_a_2123_);
lean_dec_ref(v___x_2121_);
lean_inc(v_a_2122_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v_a_2122_);
v___x_2125_ = l_Lake_Job_bindM___redArg___lam__0(v___x_2108_, v___x_2109_, v___x_2124_, v_a_2123_);
lean_dec_ref(v___x_2124_);
v_a_2126_ = lean_ctor_get(v___x_2125_, 1);
lean_inc(v_a_2126_);
lean_dec_ref(v___x_2125_);
v___x_2127_ = lean_st_ref_get(v___x_2106_);
lean_dec(v___x_2106_);
v_log_2128_ = lean_ctor_get(v_a_2126_, 0);
v_action_2129_ = lean_ctor_get_uint8(v_a_2126_, sizeof(void*)*3);
v_wantsRebuild_2130_ = lean_ctor_get_uint8(v_a_2126_, sizeof(void*)*3 + 1);
v_trace_2131_ = lean_ctor_get(v_a_2126_, 1);
v_buildTime_2132_ = lean_ctor_get(v_a_2126_, 2);
v_data_2133_ = lean_ctor_get(v___x_2127_, 0);
lean_inc_ref(v_data_2133_);
lean_dec(v___x_2127_);
v___x_2160_ = lean_string_validate_utf8(v_data_2133_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; 
lean_dec_ref(v_data_2133_);
v___x_2161_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2162_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2161_);
v___y_2135_ = v___x_2162_;
goto v___jp_2134_;
}
else
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_string_from_utf8_unchecked(v_data_2133_);
v___y_2135_ = v___x_2163_;
goto v___jp_2134_;
}
v___jp_2134_:
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2136_ = lean_string_utf8_byte_size(v___y_2135_);
v___x_2137_ = lean_nat_dec_eq(v___x_2136_, v___x_2104_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2154_; 
lean_inc(v_buildTime_2132_);
lean_inc_ref(v_trace_2131_);
lean_inc_ref(v_log_2128_);
v_isSharedCheck_2154_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2154_ == 0)
{
lean_object* v_unused_2155_; lean_object* v_unused_2156_; lean_object* v_unused_2157_; 
v_unused_2155_ = lean_ctor_get(v_a_2126_, 2);
lean_dec(v_unused_2155_);
v_unused_2156_ = lean_ctor_get(v_a_2126_, 1);
lean_dec(v_unused_2156_);
v_unused_2157_ = lean_ctor_get(v_a_2126_, 0);
lean_dec(v_unused_2157_);
v___x_2139_ = v_a_2126_;
v_isShared_2140_ = v_isSharedCheck_2154_;
goto v_resetjp_2138_;
}
else
{
lean_dec(v_a_2126_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2154_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; uint8_t v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2151_; 
v___x_2141_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_2142_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2142_, 0, v___y_2135_);
lean_ctor_set(v___x_2142_, 1, v___x_2104_);
lean_ctor_set(v___x_2142_, 2, v___x_2136_);
v___x_2143_ = l_String_Slice_trimAscii(v___x_2142_);
v___x_2144_ = l_String_Slice_toString(v___x_2143_);
lean_dec_ref(v___x_2143_);
v___x_2145_ = lean_string_append(v___x_2141_, v___x_2144_);
lean_dec_ref(v___x_2144_);
v___x_2146_ = 1;
v___x_2147_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set_uint8(v___x_2147_, sizeof(void*)*1, v___x_2146_);
v___x_2148_ = lean_box(0);
v___x_2149_ = lean_array_push(v_log_2128_, v___x_2147_);
if (v_isShared_2140_ == 0)
{
lean_ctor_set(v___x_2139_, 0, v___x_2149_);
v___x_2151_ = v___x_2139_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2153_, 1, v_trace_2131_);
lean_ctor_set(v_reuseFailAlloc_2153_, 2, v_buildTime_2132_);
lean_ctor_set_uint8(v_reuseFailAlloc_2153_, sizeof(void*)*3, v_action_2129_);
lean_ctor_set_uint8(v_reuseFailAlloc_2153_, sizeof(void*)*3 + 1, v_wantsRebuild_2130_);
v___x_2151_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2122_, v___x_2148_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v___x_2151_);
lean_dec_ref(v_a_2079_);
v___y_2093_ = v___x_2152_;
goto v___jp_2092_;
}
}
}
else
{
lean_object* v___x_2158_; lean_object* v___x_2159_; 
lean_dec_ref(v___y_2135_);
v___x_2158_ = lean_box(0);
v___x_2159_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2122_, v___x_2158_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2126_);
lean_dec_ref(v_a_2079_);
v___y_2093_ = v___x_2159_;
goto v___jp_2092_;
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v_a_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v_a_2168_; 
lean_dec(v___x_2106_);
lean_dec(v_prio_2084_);
lean_dec_ref(v_a_2079_);
v_a_2164_ = lean_ctor_get(v___x_2121_, 0);
lean_inc(v_a_2164_);
v_a_2165_ = lean_ctor_get(v___x_2121_, 1);
lean_inc(v_a_2165_);
lean_dec_ref(v___x_2121_);
v___x_2166_ = lean_box(0);
v___x_2167_ = l_Lake_Job_bindM___redArg___lam__0(v___x_2108_, v___x_2109_, v___x_2166_, v_a_2165_);
v_a_2168_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_a_2168_);
lean_dec_ref(v___x_2167_);
v_a_2088_ = v_a_2164_;
v_a_2089_ = v_a_2168_;
goto v___jp_2087_;
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_prio_2084_);
lean_dec_ref(v_a_2079_);
lean_dec_ref(v_f_2078_);
v_a_2171_ = lean_ctor_get(v_x_2085_, 0);
v_a_2172_ = lean_ctor_get(v_x_2085_, 1);
v_isSharedCheck_2180_ = !lean_is_exclusive(v_x_2085_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2174_ = v_x_2085_;
v_isShared_2175_ = v_isSharedCheck_2180_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_inc(v_a_2171_);
lean_dec(v_x_2085_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2180_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2171_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2178_; 
v___x_2178_ = lean_task_pure(v___x_2177_);
return v___x_2178_;
}
}
}
v___jp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2090_, 0, v_a_2088_);
lean_ctor_set(v___x_2090_, 1, v_a_2089_);
v___x_2091_ = lean_task_pure(v___x_2090_);
return v___x_2091_;
}
v___jp_2092_:
{
if (lean_obj_tag(v___y_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v_a_2095_; lean_object* v_task_2096_; lean_object* v___f_2097_; uint8_t v___x_2098_; lean_object* v___x_2099_; 
v_a_2094_ = lean_ctor_get(v___y_2093_, 0);
lean_inc(v_a_2094_);
v_a_2095_ = lean_ctor_get(v___y_2093_, 1);
lean_inc(v_a_2095_);
lean_dec_ref(v___y_2093_);
v_task_2096_ = lean_ctor_get(v_a_2094_, 0);
lean_inc_ref(v_task_2096_);
lean_dec(v_a_2094_);
v___f_2097_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2097_, 0, v_a_2095_);
v___x_2098_ = 1;
v___x_2099_ = lean_task_map(v___f_2097_, v_task_2096_, v_prio_2084_, v___x_2098_);
return v___x_2099_;
}
else
{
lean_object* v_a_2100_; lean_object* v_a_2101_; 
lean_dec(v_prio_2084_);
v_a_2100_ = lean_ctor_get(v___y_2093_, 0);
lean_inc(v_a_2100_);
v_a_2101_ = lean_ctor_get(v___y_2093_, 1);
lean_inc(v_a_2101_);
lean_dec_ref(v___y_2093_);
v_a_2088_ = v_a_2100_;
v_a_2089_ = v_a_2101_;
goto v___jp_2087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3___boxed(lean_object* v_a_2181_, lean_object* v_f_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_, lean_object* v_a_2187_, lean_object* v_prio_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lake_Job_bindM___redArg___lam__3(v_a_2181_, v_f_2182_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_, v_a_2187_, v_prio_2188_, v_x_2189_);
lean_dec_ref(v_a_2187_);
lean_dec(v_a_2186_);
lean_dec(v_a_2185_);
lean_dec(v_a_2184_);
lean_dec_ref(v_a_2181_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg(lean_object* v_kind_2192_, lean_object* v_self_2193_, lean_object* v_f_2194_, lean_object* v_prio_2195_, uint8_t v_sync_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_){
_start:
{
lean_object* v_task_2204_; lean_object* v_caption_2205_; uint8_t v_optional_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2215_; 
v_task_2204_ = lean_ctor_get(v_self_2193_, 0);
v_caption_2205_ = lean_ctor_get(v_self_2193_, 2);
v_optional_2206_ = lean_ctor_get_uint8(v_self_2193_, sizeof(void*)*3);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_self_2193_);
if (v_isSharedCheck_2215_ == 0)
{
lean_object* v_unused_2216_; 
v_unused_2216_ = lean_ctor_get(v_self_2193_, 1);
lean_dec(v_unused_2216_);
v___x_2208_ = v_self_2193_;
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_caption_2205_);
lean_inc(v_task_2204_);
lean_dec(v_self_2193_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2215_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___f_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
lean_inc(v_prio_2195_);
lean_inc_ref(v_a_2201_);
lean_inc(v_a_2200_);
lean_inc(v_a_2199_);
lean_inc(v_a_2198_);
lean_inc_ref(v_a_2202_);
v___f_2210_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__3___boxed), 10, 8);
lean_closure_set(v___f_2210_, 0, v_a_2202_);
lean_closure_set(v___f_2210_, 1, v_f_2194_);
lean_closure_set(v___f_2210_, 2, v_a_2197_);
lean_closure_set(v___f_2210_, 3, v_a_2198_);
lean_closure_set(v___f_2210_, 4, v_a_2199_);
lean_closure_set(v___f_2210_, 5, v_a_2200_);
lean_closure_set(v___f_2210_, 6, v_a_2201_);
lean_closure_set(v___f_2210_, 7, v_prio_2195_);
v___x_2211_ = lean_io_bind_task(v_task_2204_, v___f_2210_, v_prio_2195_, v_sync_2196_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 1, v_kind_2192_);
lean_ctor_set(v___x_2208_, 0, v___x_2211_);
v___x_2213_ = v___x_2208_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v_kind_2192_);
lean_ctor_set(v_reuseFailAlloc_2214_, 2, v_caption_2205_);
lean_ctor_set_uint8(v_reuseFailAlloc_2214_, sizeof(void*)*3, v_optional_2206_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object* v_kind_2217_, lean_object* v_self_2218_, lean_object* v_f_2219_, lean_object* v_prio_2220_, lean_object* v_sync_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_, lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_){
_start:
{
uint8_t v_sync_boxed_2229_; lean_object* v_res_2230_; 
v_sync_boxed_2229_ = lean_unbox(v_sync_2221_);
v_res_2230_ = l_Lake_Job_bindM___redArg(v_kind_2217_, v_self_2218_, v_f_2219_, v_prio_2220_, v_sync_boxed_2229_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_, v_a_2226_, v_a_2227_);
lean_dec_ref(v_a_2227_);
lean_dec_ref(v_a_2226_);
lean_dec(v_a_2225_);
lean_dec(v_a_2224_);
lean_dec(v_a_2223_);
return v_res_2230_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM(lean_object* v_00_u03b2_2231_, lean_object* v_00_u03b1_2232_, lean_object* v_kind_2233_, lean_object* v_self_2234_, lean_object* v_f_2235_, lean_object* v_prio_2236_, uint8_t v_sync_2237_, lean_object* v_a_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = l_Lake_Job_bindM___redArg(v_kind_2233_, v_self_2234_, v_f_2235_, v_prio_2236_, v_sync_2237_, v_a_2238_, v_a_2239_, v_a_2240_, v_a_2241_, v_a_2242_, v_a_2243_);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object* v_00_u03b2_2246_, lean_object* v_00_u03b1_2247_, lean_object* v_kind_2248_, lean_object* v_self_2249_, lean_object* v_f_2250_, lean_object* v_prio_2251_, lean_object* v_sync_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_, lean_object* v_a_2259_){
_start:
{
uint8_t v_sync_boxed_2260_; lean_object* v_res_2261_; 
v_sync_boxed_2260_ = lean_unbox(v_sync_2252_);
v_res_2261_ = l_Lake_Job_bindM(v_00_u03b2_2246_, v_00_u03b1_2247_, v_kind_2248_, v_self_2249_, v_f_2250_, v_prio_2251_, v_sync_boxed_2260_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
lean_dec_ref(v_a_2258_);
lean_dec_ref(v_a_2257_);
lean_dec(v_a_2256_);
lean_dec(v_a_2255_);
lean_dec(v_a_2254_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object* v_f_2262_, lean_object* v_rx_2263_, lean_object* v_ry_2264_){
_start:
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_apply_2(v_f_2262_, v_rx_2263_, v_ry_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object* v_other_2266_, lean_object* v_f_2267_, lean_object* v_prio_2268_, uint8_t v_sync_2269_, lean_object* v_rx_2270_){
_start:
{
lean_object* v_task_2271_; lean_object* v___f_2272_; lean_object* v___x_2273_; 
v_task_2271_ = lean_ctor_get(v_other_2266_, 0);
lean_inc_ref(v_task_2271_);
lean_dec_ref(v_other_2266_);
v___f_2272_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2272_, 0, v_f_2267_);
lean_closure_set(v___f_2272_, 1, v_rx_2270_);
v___x_2273_ = lean_task_map(v___f_2272_, v_task_2271_, v_prio_2268_, v_sync_2269_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object* v_other_2274_, lean_object* v_f_2275_, lean_object* v_prio_2276_, lean_object* v_sync_2277_, lean_object* v_rx_2278_){
_start:
{
uint8_t v_sync_boxed_2279_; lean_object* v_res_2280_; 
v_sync_boxed_2279_ = lean_unbox(v_sync_2277_);
v_res_2280_ = l_Lake_Job_zipResultWith___redArg___lam__1(v_other_2274_, v_f_2275_, v_prio_2276_, v_sync_boxed_2279_, v_rx_2278_);
return v_res_2280_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg(lean_object* v_inst_2281_, lean_object* v_f_2282_, lean_object* v_self_2283_, lean_object* v_other_2284_, lean_object* v_prio_2285_, uint8_t v_sync_2286_){
_start:
{
lean_object* v_task_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2300_; 
v_task_2287_ = lean_ctor_get(v_self_2283_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_self_2283_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; lean_object* v_unused_2302_; 
v_unused_2301_ = lean_ctor_get(v_self_2283_, 2);
lean_dec(v_unused_2301_);
v_unused_2302_ = lean_ctor_get(v_self_2283_, 1);
lean_dec(v_unused_2302_);
v___x_2289_ = v_self_2283_;
v_isShared_2290_ = v_isSharedCheck_2300_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_task_2287_);
lean_dec(v_self_2283_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2300_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2291_; lean_object* v___f_2292_; uint8_t v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; lean_object* v___x_2298_; 
v___x_2291_ = lean_box(v_sync_2286_);
lean_inc(v_prio_2285_);
v___f_2292_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2292_, 0, v_other_2284_);
lean_closure_set(v___f_2292_, 1, v_f_2282_);
lean_closure_set(v___f_2292_, 2, v_prio_2285_);
lean_closure_set(v___f_2292_, 3, v___x_2291_);
v___x_2293_ = 1;
v___x_2294_ = lean_task_bind(v_task_2287_, v___f_2292_, v_prio_2285_, v___x_2293_);
v___x_2295_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2296_ = 0;
if (v_isShared_2290_ == 0)
{
lean_ctor_set(v___x_2289_, 2, v___x_2295_);
lean_ctor_set(v___x_2289_, 1, v_inst_2281_);
lean_ctor_set(v___x_2289_, 0, v___x_2294_);
v___x_2298_ = v___x_2289_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v_inst_2281_);
lean_ctor_set(v_reuseFailAlloc_2299_, 2, v___x_2295_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
lean_ctor_set_uint8(v___x_2298_, sizeof(void*)*3, v___x_2296_);
return v___x_2298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object* v_inst_2303_, lean_object* v_f_2304_, lean_object* v_self_2305_, lean_object* v_other_2306_, lean_object* v_prio_2307_, lean_object* v_sync_2308_){
_start:
{
uint8_t v_sync_boxed_2309_; lean_object* v_res_2310_; 
v_sync_boxed_2309_ = lean_unbox(v_sync_2308_);
v_res_2310_ = l_Lake_Job_zipResultWith___redArg(v_inst_2303_, v_f_2304_, v_self_2305_, v_other_2306_, v_prio_2307_, v_sync_boxed_2309_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith(lean_object* v_00_u03b3_2311_, lean_object* v_00_u03b1_2312_, lean_object* v_00_u03b2_2313_, lean_object* v_inst_2314_, lean_object* v_f_2315_, lean_object* v_self_2316_, lean_object* v_other_2317_, lean_object* v_prio_2318_, uint8_t v_sync_2319_){
_start:
{
lean_object* v_task_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2333_; 
v_task_2320_ = lean_ctor_get(v_self_2316_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v_self_2316_);
if (v_isSharedCheck_2333_ == 0)
{
lean_object* v_unused_2334_; lean_object* v_unused_2335_; 
v_unused_2334_ = lean_ctor_get(v_self_2316_, 2);
lean_dec(v_unused_2334_);
v_unused_2335_ = lean_ctor_get(v_self_2316_, 1);
lean_dec(v_unused_2335_);
v___x_2322_ = v_self_2316_;
v_isShared_2323_ = v_isSharedCheck_2333_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_task_2320_);
lean_dec(v_self_2316_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2333_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v___f_2325_; uint8_t v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2331_; 
v___x_2324_ = lean_box(v_sync_2319_);
lean_inc(v_prio_2318_);
v___f_2325_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2325_, 0, v_other_2317_);
lean_closure_set(v___f_2325_, 1, v_f_2315_);
lean_closure_set(v___f_2325_, 2, v_prio_2318_);
lean_closure_set(v___f_2325_, 3, v___x_2324_);
v___x_2326_ = 1;
v___x_2327_ = lean_task_bind(v_task_2320_, v___f_2325_, v_prio_2318_, v___x_2326_);
v___x_2328_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2329_ = 0;
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 2, v___x_2328_);
lean_ctor_set(v___x_2322_, 1, v_inst_2314_);
lean_ctor_set(v___x_2322_, 0, v___x_2327_);
v___x_2331_ = v___x_2322_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_inst_2314_);
lean_ctor_set(v_reuseFailAlloc_2332_, 2, v___x_2328_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_ctor_set_uint8(v___x_2331_, sizeof(void*)*3, v___x_2329_);
return v___x_2331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object* v_00_u03b3_2336_, lean_object* v_00_u03b1_2337_, lean_object* v_00_u03b2_2338_, lean_object* v_inst_2339_, lean_object* v_f_2340_, lean_object* v_self_2341_, lean_object* v_other_2342_, lean_object* v_prio_2343_, lean_object* v_sync_2344_){
_start:
{
uint8_t v_sync_boxed_2345_; lean_object* v_res_2346_; 
v_sync_boxed_2345_ = lean_unbox(v_sync_2344_);
v_res_2346_ = l_Lake_Job_zipResultWith(v_00_u03b3_2336_, v_00_u03b1_2337_, v_00_u03b2_2338_, v_inst_2339_, v_f_2340_, v_self_2341_, v_other_2342_, v_prio_2343_, v_sync_boxed_2345_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object* v_rx_2347_, lean_object* v_f_2348_, lean_object* v_ry_2349_){
_start:
{
lean_object* v___y_2351_; lean_object* v___y_2352_; lean_object* v___y_2353_; lean_object* v___y_2357_; lean_object* v___y_2358_; lean_object* v___y_2359_; lean_object* v_a_2362_; 
if (lean_obj_tag(v_rx_2347_) == 0)
{
if (lean_obj_tag(v_ry_2349_) == 0)
{
lean_object* v_a_2364_; lean_object* v_a_2365_; lean_object* v_a_2366_; lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2376_; 
v_a_2364_ = lean_ctor_get(v_rx_2347_, 0);
lean_inc(v_a_2364_);
v_a_2365_ = lean_ctor_get(v_rx_2347_, 1);
lean_inc(v_a_2365_);
lean_dec_ref(v_rx_2347_);
v_a_2366_ = lean_ctor_get(v_ry_2349_, 0);
v_a_2367_ = lean_ctor_get(v_ry_2349_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_ry_2349_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2369_ = v_ry_2349_;
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_inc(v_a_2366_);
lean_dec(v_ry_2349_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2376_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2374_; 
v___x_2371_ = lean_apply_2(v_f_2348_, v_a_2364_, v_a_2366_);
v___x_2372_ = l_Lake_JobState_merge(v_a_2365_, v_a_2367_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 1, v___x_2372_);
lean_ctor_set(v___x_2369_, 0, v___x_2371_);
v___x_2374_ = v___x_2369_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2371_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v___x_2372_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
else
{
lean_object* v_a_2377_; 
lean_dec(v_f_2348_);
v_a_2377_ = lean_ctor_get(v_rx_2347_, 1);
lean_inc(v_a_2377_);
lean_dec_ref(v_rx_2347_);
v_a_2362_ = v_a_2377_;
goto v___jp_2361_;
}
}
else
{
lean_dec(v_f_2348_);
if (lean_obj_tag(v_rx_2347_) == 0)
{
lean_object* v_a_2378_; 
v_a_2378_ = lean_ctor_get(v_rx_2347_, 1);
lean_inc(v_a_2378_);
lean_dec_ref(v_rx_2347_);
v_a_2362_ = v_a_2378_;
goto v___jp_2361_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2380_; 
v_a_2379_ = lean_ctor_get(v_rx_2347_, 1);
lean_inc(v_a_2379_);
lean_dec_ref(v_rx_2347_);
v___x_2380_ = lean_unsigned_to_nat(0u);
v___y_2357_ = v_ry_2349_;
v___y_2358_ = v___x_2380_;
v___y_2359_ = v_a_2379_;
goto v___jp_2356_;
}
}
v___jp_2350_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = l_Lake_JobState_merge(v___y_2351_, v___y_2353_);
v___x_2355_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___y_2352_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
return v___x_2355_;
}
v___jp_2356_:
{
lean_object* v_a_2360_; 
v_a_2360_ = lean_ctor_get(v___y_2357_, 1);
lean_inc(v_a_2360_);
lean_dec_ref(v___y_2357_);
v___y_2351_ = v___y_2359_;
v___y_2352_ = v___y_2358_;
v___y_2353_ = v_a_2360_;
goto v___jp_2350_;
}
v___jp_2361_:
{
lean_object* v___x_2363_; 
v___x_2363_ = lean_unsigned_to_nat(0u);
v___y_2357_ = v_ry_2349_;
v___y_2358_ = v___x_2363_;
v___y_2359_ = v_a_2362_;
goto v___jp_2356_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object* v_other_2381_, lean_object* v_f_2382_, lean_object* v_prio_2383_, uint8_t v_sync_2384_, lean_object* v_rx_2385_){
_start:
{
lean_object* v_task_2386_; lean_object* v___f_2387_; lean_object* v___x_2388_; 
v_task_2386_ = lean_ctor_get(v_other_2381_, 0);
lean_inc_ref(v_task_2386_);
lean_dec_ref(v_other_2381_);
v___f_2387_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2387_, 0, v_rx_2385_);
lean_closure_set(v___f_2387_, 1, v_f_2382_);
v___x_2388_ = lean_task_map(v___f_2387_, v_task_2386_, v_prio_2383_, v_sync_2384_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object* v_other_2389_, lean_object* v_f_2390_, lean_object* v_prio_2391_, lean_object* v_sync_2392_, lean_object* v_rx_2393_){
_start:
{
uint8_t v_sync_boxed_2394_; lean_object* v_res_2395_; 
v_sync_boxed_2394_ = lean_unbox(v_sync_2392_);
v_res_2395_ = l_Lake_Job_zipWith___redArg___lam__1(v_other_2389_, v_f_2390_, v_prio_2391_, v_sync_boxed_2394_, v_rx_2393_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg(lean_object* v_inst_2396_, lean_object* v_f_2397_, lean_object* v_self_2398_, lean_object* v_other_2399_, lean_object* v_prio_2400_, uint8_t v_sync_2401_){
_start:
{
lean_object* v_task_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2415_; 
v_task_2402_ = lean_ctor_get(v_self_2398_, 0);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_self_2398_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; lean_object* v_unused_2417_; 
v_unused_2416_ = lean_ctor_get(v_self_2398_, 2);
lean_dec(v_unused_2416_);
v_unused_2417_ = lean_ctor_get(v_self_2398_, 1);
lean_dec(v_unused_2417_);
v___x_2404_ = v_self_2398_;
v_isShared_2405_ = v_isSharedCheck_2415_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_task_2402_);
lean_dec(v_self_2398_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2415_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___f_2407_; uint8_t v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v___x_2413_; 
v___x_2406_ = lean_box(v_sync_2401_);
lean_inc(v_prio_2400_);
v___f_2407_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2407_, 0, v_other_2399_);
lean_closure_set(v___f_2407_, 1, v_f_2397_);
lean_closure_set(v___f_2407_, 2, v_prio_2400_);
lean_closure_set(v___f_2407_, 3, v___x_2406_);
v___x_2408_ = 1;
v___x_2409_ = lean_task_bind(v_task_2402_, v___f_2407_, v_prio_2400_, v___x_2408_);
v___x_2410_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2411_ = 0;
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 2, v___x_2410_);
lean_ctor_set(v___x_2404_, 1, v_inst_2396_);
lean_ctor_set(v___x_2404_, 0, v___x_2409_);
v___x_2413_ = v___x_2404_;
goto v_reusejp_2412_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v___x_2409_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_inst_2396_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v___x_2410_);
v___x_2413_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2412_;
}
v_reusejp_2412_:
{
lean_ctor_set_uint8(v___x_2413_, sizeof(void*)*3, v___x_2411_);
return v___x_2413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object* v_inst_2418_, lean_object* v_f_2419_, lean_object* v_self_2420_, lean_object* v_other_2421_, lean_object* v_prio_2422_, lean_object* v_sync_2423_){
_start:
{
uint8_t v_sync_boxed_2424_; lean_object* v_res_2425_; 
v_sync_boxed_2424_ = lean_unbox(v_sync_2423_);
v_res_2425_ = l_Lake_Job_zipWith___redArg(v_inst_2418_, v_f_2419_, v_self_2420_, v_other_2421_, v_prio_2422_, v_sync_boxed_2424_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__0(lean_object* v_rx_2426_, lean_object* v_f_2427_, lean_object* v_ry_2428_){
_start:
{
lean_object* v___y_2430_; lean_object* v___y_2431_; lean_object* v___y_2432_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v_a_2441_; lean_object* v_rb_2442_; 
if (lean_obj_tag(v_rx_2426_) == 0)
{
if (lean_obj_tag(v_ry_2428_) == 0)
{
lean_object* v_a_2444_; lean_object* v_a_2445_; lean_object* v_a_2446_; lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2456_; 
v_a_2444_ = lean_ctor_get(v_rx_2426_, 0);
lean_inc(v_a_2444_);
v_a_2445_ = lean_ctor_get(v_rx_2426_, 1);
lean_inc(v_a_2445_);
lean_dec_ref(v_rx_2426_);
v_a_2446_ = lean_ctor_get(v_ry_2428_, 0);
v_a_2447_ = lean_ctor_get(v_ry_2428_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_ry_2428_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2449_ = v_ry_2428_;
v_isShared_2450_ = v_isSharedCheck_2456_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_inc(v_a_2446_);
lean_dec(v_ry_2428_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2456_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2451_ = lean_apply_2(v_f_2427_, v_a_2444_, v_a_2446_);
v___x_2452_ = l_Lake_JobState_merge(v_a_2445_, v_a_2447_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 1, v___x_2452_);
lean_ctor_set(v___x_2449_, 0, v___x_2451_);
v___x_2454_ = v___x_2449_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
else
{
lean_object* v_a_2457_; 
lean_dec(v_f_2427_);
v_a_2457_ = lean_ctor_get(v_rx_2426_, 1);
lean_inc(v_a_2457_);
lean_dec_ref(v_rx_2426_);
v_a_2441_ = v_a_2457_;
v_rb_2442_ = v_ry_2428_;
goto v___jp_2440_;
}
}
else
{
lean_dec(v_f_2427_);
if (lean_obj_tag(v_rx_2426_) == 0)
{
lean_object* v_a_2458_; 
v_a_2458_ = lean_ctor_get(v_rx_2426_, 1);
lean_inc(v_a_2458_);
lean_dec_ref(v_rx_2426_);
v_a_2441_ = v_a_2458_;
v_rb_2442_ = v_ry_2428_;
goto v___jp_2440_;
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2460_; 
v_a_2459_ = lean_ctor_get(v_rx_2426_, 1);
lean_inc(v_a_2459_);
lean_dec_ref(v_rx_2426_);
v___x_2460_ = lean_unsigned_to_nat(0u);
v___y_2436_ = v_ry_2428_;
v___y_2437_ = v___x_2460_;
v___y_2438_ = v_a_2459_;
goto v___jp_2435_;
}
}
v___jp_2429_:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = l_Lake_JobState_merge(v___y_2430_, v___y_2432_);
v___x_2434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___y_2431_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
return v___x_2434_;
}
v___jp_2435_:
{
lean_object* v_a_2439_; 
v_a_2439_ = lean_ctor_get(v___y_2436_, 1);
lean_inc(v_a_2439_);
lean_dec_ref(v___y_2436_);
v___y_2430_ = v___y_2438_;
v___y_2431_ = v___y_2437_;
v___y_2432_ = v_a_2439_;
goto v___jp_2429_;
}
v___jp_2440_:
{
lean_object* v___x_2443_; 
v___x_2443_ = lean_unsigned_to_nat(0u);
v___y_2436_ = v_rb_2442_;
v___y_2437_ = v___x_2443_;
v___y_2438_ = v_a_2441_;
goto v___jp_2435_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1(lean_object* v_other_2461_, lean_object* v_f_2462_, lean_object* v_prio_2463_, uint8_t v_sync_2464_, lean_object* v_rx_2465_){
_start:
{
lean_object* v_task_2466_; lean_object* v___f_2467_; lean_object* v___x_2468_; 
v_task_2466_ = lean_ctor_get(v_other_2461_, 0);
lean_inc_ref(v_task_2466_);
lean_dec_ref(v_other_2461_);
v___f_2467_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__0), 3, 2);
lean_closure_set(v___f_2467_, 0, v_rx_2465_);
lean_closure_set(v___f_2467_, 1, v_f_2462_);
v___x_2468_ = lean_task_map(v___f_2467_, v_task_2466_, v_prio_2463_, v_sync_2464_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1___boxed(lean_object* v_other_2469_, lean_object* v_f_2470_, lean_object* v_prio_2471_, lean_object* v_sync_2472_, lean_object* v_rx_2473_){
_start:
{
uint8_t v_sync_boxed_2474_; lean_object* v_res_2475_; 
v_sync_boxed_2474_ = lean_unbox(v_sync_2472_);
v_res_2475_ = l_Lake_Job_zipWith___lam__1(v_other_2469_, v_f_2470_, v_prio_2471_, v_sync_boxed_2474_, v_rx_2473_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith(lean_object* v_00_u03b3_2476_, lean_object* v_00_u03b1_2477_, lean_object* v_00_u03b2_2478_, lean_object* v_inst_2479_, lean_object* v_f_2480_, lean_object* v_self_2481_, lean_object* v_other_2482_, lean_object* v_prio_2483_, uint8_t v_sync_2484_){
_start:
{
lean_object* v_task_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2498_; 
v_task_2485_ = lean_ctor_get(v_self_2481_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v_self_2481_);
if (v_isSharedCheck_2498_ == 0)
{
lean_object* v_unused_2499_; lean_object* v_unused_2500_; 
v_unused_2499_ = lean_ctor_get(v_self_2481_, 2);
lean_dec(v_unused_2499_);
v_unused_2500_ = lean_ctor_get(v_self_2481_, 1);
lean_dec(v_unused_2500_);
v___x_2487_ = v_self_2481_;
v_isShared_2488_ = v_isSharedCheck_2498_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_task_2485_);
lean_dec(v_self_2481_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2498_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___f_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; lean_object* v___x_2496_; 
v___x_2489_ = lean_box(v_sync_2484_);
lean_inc(v_prio_2483_);
v___f_2490_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2490_, 0, v_other_2482_);
lean_closure_set(v___f_2490_, 1, v_f_2480_);
lean_closure_set(v___f_2490_, 2, v_prio_2483_);
lean_closure_set(v___f_2490_, 3, v___x_2489_);
v___x_2491_ = 1;
v___x_2492_ = lean_task_bind(v_task_2485_, v___f_2490_, v_prio_2483_, v___x_2491_);
v___x_2493_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2494_ = 0;
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 2, v___x_2493_);
lean_ctor_set(v___x_2487_, 1, v_inst_2479_);
lean_ctor_set(v___x_2487_, 0, v___x_2492_);
v___x_2496_ = v___x_2487_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v___x_2492_);
lean_ctor_set(v_reuseFailAlloc_2497_, 1, v_inst_2479_);
lean_ctor_set(v_reuseFailAlloc_2497_, 2, v___x_2493_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_ctor_set_uint8(v___x_2496_, sizeof(void*)*3, v___x_2494_);
return v___x_2496_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object* v_00_u03b3_2501_, lean_object* v_00_u03b1_2502_, lean_object* v_00_u03b2_2503_, lean_object* v_inst_2504_, lean_object* v_f_2505_, lean_object* v_self_2506_, lean_object* v_other_2507_, lean_object* v_prio_2508_, lean_object* v_sync_2509_){
_start:
{
uint8_t v_sync_boxed_2510_; lean_object* v_res_2511_; 
v_sync_boxed_2510_ = lean_unbox(v_sync_2509_);
v_res_2511_ = l_Lake_Job_zipWith(v_00_u03b3_2501_, v_00_u03b1_2502_, v_00_u03b2_2503_, v_inst_2504_, v_f_2505_, v_self_2506_, v_other_2507_, v_prio_2508_, v_sync_boxed_2510_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object* v___x_2512_, lean_object* v_rx_2513_, lean_object* v_ry_2514_){
_start:
{
lean_object* v___y_2516_; lean_object* v___y_2517_; lean_object* v___y_2535_; lean_object* v___y_2536_; 
if (lean_obj_tag(v_rx_2513_) == 0)
{
if (lean_obj_tag(v_ry_2514_) == 0)
{
lean_object* v_a_2538_; lean_object* v_a_2539_; lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2562_; 
lean_dec(v___x_2512_);
v_a_2538_ = lean_ctor_get(v_rx_2513_, 0);
lean_inc(v_a_2538_);
v_a_2539_ = lean_ctor_get(v_rx_2513_, 1);
lean_inc(v_a_2539_);
lean_dec_ref(v_rx_2513_);
v_a_2540_ = lean_ctor_get(v_ry_2514_, 1);
v_isSharedCheck_2562_ = !lean_is_exclusive(v_ry_2514_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v_ry_2514_, 0);
lean_dec(v_unused_2563_);
v___x_2542_ = v_ry_2514_;
v_isShared_2543_ = v_isSharedCheck_2562_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v_ry_2514_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2562_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v_log_2545_; uint8_t v_action_2546_; uint8_t v_wantsRebuild_2547_; lean_object* v_buildTime_2548_; lean_object* v_trace_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2559_; 
lean_inc(v_a_2539_);
v___x_2544_ = l_Lake_JobState_merge(v_a_2539_, v_a_2540_);
v_log_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc_ref(v_log_2545_);
v_action_2546_ = lean_ctor_get_uint8(v___x_2544_, sizeof(void*)*3);
v_wantsRebuild_2547_ = lean_ctor_get_uint8(v___x_2544_, sizeof(void*)*3 + 1);
v_buildTime_2548_ = lean_ctor_get(v___x_2544_, 2);
lean_inc(v_buildTime_2548_);
lean_dec_ref(v___x_2544_);
v_trace_2549_ = lean_ctor_get(v_a_2539_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_a_2539_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; lean_object* v_unused_2561_; 
v_unused_2560_ = lean_ctor_get(v_a_2539_, 2);
lean_dec(v_unused_2560_);
v_unused_2561_ = lean_ctor_get(v_a_2539_, 0);
lean_dec(v_unused_2561_);
v___x_2551_ = v_a_2539_;
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_trace_2549_);
lean_dec(v_a_2539_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 2, v_buildTime_2548_);
lean_ctor_set(v___x_2551_, 0, v_log_2545_);
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_log_2545_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_trace_2549_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v_buildTime_2548_);
v___x_2554_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
lean_object* v___x_2556_; 
lean_ctor_set_uint8(v___x_2554_, sizeof(void*)*3, v_action_2546_);
lean_ctor_set_uint8(v___x_2554_, sizeof(void*)*3 + 1, v_wantsRebuild_2547_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 1, v___x_2554_);
lean_ctor_set(v___x_2542_, 0, v_a_2538_);
v___x_2556_ = v___x_2542_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2538_);
lean_ctor_set(v_reuseFailAlloc_2557_, 1, v___x_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
else
{
lean_object* v_a_2564_; 
v_a_2564_ = lean_ctor_get(v_rx_2513_, 1);
lean_inc(v_a_2564_);
lean_dec_ref(v_rx_2513_);
v___y_2535_ = v_ry_2514_;
v___y_2536_ = v_a_2564_;
goto v___jp_2534_;
}
}
else
{
lean_object* v_a_2565_; 
v_a_2565_ = lean_ctor_get(v_rx_2513_, 1);
lean_inc(v_a_2565_);
lean_dec_ref(v_rx_2513_);
v___y_2535_ = v_ry_2514_;
v___y_2536_ = v_a_2565_;
goto v___jp_2534_;
}
v___jp_2515_:
{
lean_object* v___x_2518_; lean_object* v_log_2519_; uint8_t v_action_2520_; uint8_t v_wantsRebuild_2521_; lean_object* v_buildTime_2522_; lean_object* v_trace_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2531_; 
lean_inc_ref(v___y_2516_);
v___x_2518_ = l_Lake_JobState_merge(v___y_2516_, v___y_2517_);
v_log_2519_ = lean_ctor_get(v___x_2518_, 0);
lean_inc_ref(v_log_2519_);
v_action_2520_ = lean_ctor_get_uint8(v___x_2518_, sizeof(void*)*3);
v_wantsRebuild_2521_ = lean_ctor_get_uint8(v___x_2518_, sizeof(void*)*3 + 1);
v_buildTime_2522_ = lean_ctor_get(v___x_2518_, 2);
lean_inc(v_buildTime_2522_);
lean_dec_ref(v___x_2518_);
v_trace_2523_ = lean_ctor_get(v___y_2516_, 1);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___y_2516_);
if (v_isSharedCheck_2531_ == 0)
{
lean_object* v_unused_2532_; lean_object* v_unused_2533_; 
v_unused_2532_ = lean_ctor_get(v___y_2516_, 2);
lean_dec(v_unused_2532_);
v_unused_2533_ = lean_ctor_get(v___y_2516_, 0);
lean_dec(v_unused_2533_);
v___x_2525_ = v___y_2516_;
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_trace_2523_);
lean_dec(v___y_2516_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2531_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 2, v_buildTime_2522_);
lean_ctor_set(v___x_2525_, 0, v_log_2519_);
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_log_2519_);
lean_ctor_set(v_reuseFailAlloc_2530_, 1, v_trace_2523_);
lean_ctor_set(v_reuseFailAlloc_2530_, 2, v_buildTime_2522_);
v___x_2528_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
lean_object* v___x_2529_; 
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*3, v_action_2520_);
lean_ctor_set_uint8(v___x_2528_, sizeof(void*)*3 + 1, v_wantsRebuild_2521_);
v___x_2529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2529_, 0, v___x_2512_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
return v___x_2529_;
}
}
}
v___jp_2534_:
{
lean_object* v_a_2537_; 
v_a_2537_ = lean_ctor_get(v___y_2535_, 1);
lean_inc(v_a_2537_);
lean_dec_ref(v___y_2535_);
v___y_2516_ = v___y_2536_;
v___y_2517_ = v_a_2537_;
goto v___jp_2515_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1(lean_object* v_other_2566_, lean_object* v___x_2567_, uint8_t v___x_2568_, lean_object* v_rx_2569_){
_start:
{
lean_object* v_task_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; 
v_task_2570_ = lean_ctor_get(v_other_2566_, 0);
lean_inc_ref(v_task_2570_);
lean_dec_ref(v_other_2566_);
lean_inc(v___x_2567_);
v___f_2571_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2571_, 0, v___x_2567_);
lean_closure_set(v___f_2571_, 1, v_rx_2569_);
v___x_2572_ = lean_task_map(v___f_2571_, v_task_2570_, v___x_2567_, v___x_2568_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object* v_other_2573_, lean_object* v___x_2574_, lean_object* v___x_2575_, lean_object* v_rx_2576_){
_start:
{
uint8_t v___x_262__boxed_2577_; lean_object* v_res_2578_; 
v___x_262__boxed_2577_ = lean_unbox(v___x_2575_);
v_res_2578_ = l_Lake_Job_add___redArg___lam__1(v_other_2573_, v___x_2574_, v___x_262__boxed_2577_, v_rx_2576_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object* v_self_2579_, lean_object* v_other_2580_){
_start:
{
lean_object* v_task_2581_; lean_object* v_kind_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2596_; 
v_task_2581_ = lean_ctor_get(v_self_2579_, 0);
v_kind_2582_ = lean_ctor_get(v_self_2579_, 1);
v_isSharedCheck_2596_ = !lean_is_exclusive(v_self_2579_);
if (v_isSharedCheck_2596_ == 0)
{
lean_object* v_unused_2597_; 
v_unused_2597_ = lean_ctor_get(v_self_2579_, 2);
lean_dec(v_unused_2597_);
v___x_2584_ = v_self_2579_;
v_isShared_2585_ = v_isSharedCheck_2596_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_kind_2582_);
lean_inc(v_task_2581_);
lean_dec(v_self_2579_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2596_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; uint8_t v___x_2587_; lean_object* v___x_2588_; lean_object* v___f_2589_; uint8_t v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2594_; 
v___x_2586_ = lean_unsigned_to_nat(0u);
v___x_2587_ = 0;
v___x_2588_ = lean_box(v___x_2587_);
v___f_2589_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2589_, 0, v_other_2580_);
lean_closure_set(v___f_2589_, 1, v___x_2586_);
lean_closure_set(v___f_2589_, 2, v___x_2588_);
v___x_2590_ = 1;
v___x_2591_ = lean_task_bind(v_task_2581_, v___f_2589_, v___x_2586_, v___x_2590_);
v___x_2592_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 2, v___x_2592_);
lean_ctor_set(v___x_2584_, 0, v___x_2591_);
v___x_2594_ = v___x_2584_;
goto v_reusejp_2593_;
}
else
{
lean_object* v_reuseFailAlloc_2595_; 
v_reuseFailAlloc_2595_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2595_, 0, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2595_, 1, v_kind_2582_);
lean_ctor_set(v_reuseFailAlloc_2595_, 2, v___x_2592_);
v___x_2594_ = v_reuseFailAlloc_2595_;
goto v_reusejp_2593_;
}
v_reusejp_2593_:
{
lean_ctor_set_uint8(v___x_2594_, sizeof(void*)*3, v___x_2587_);
return v___x_2594_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object* v_00_u03b1_2598_, lean_object* v_00_u03b2_2599_, lean_object* v_self_2600_, lean_object* v_other_2601_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lake_Job_add___redArg(v_self_2600_, v_other_2601_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object* v___x_2603_, lean_object* v_rx_2604_, lean_object* v_ry_2605_){
_start:
{
lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2612_; lean_object* v___y_2613_; 
if (lean_obj_tag(v_rx_2604_) == 0)
{
if (lean_obj_tag(v_ry_2605_) == 0)
{
lean_object* v_a_2615_; lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2625_; 
lean_dec(v___x_2603_);
v_a_2615_ = lean_ctor_get(v_rx_2604_, 1);
lean_inc(v_a_2615_);
lean_dec_ref(v_rx_2604_);
v_a_2616_ = lean_ctor_get(v_ry_2605_, 1);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_ry_2605_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; 
v_unused_2626_ = lean_ctor_get(v_ry_2605_, 0);
lean_dec(v_unused_2626_);
v___x_2618_ = v_ry_2605_;
v_isShared_2619_ = v_isSharedCheck_2625_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v_ry_2605_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2625_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2620_ = lean_box(0);
v___x_2621_ = l_Lake_JobState_merge(v_a_2615_, v_a_2616_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 1, v___x_2621_);
lean_ctor_set(v___x_2618_, 0, v___x_2620_);
v___x_2623_ = v___x_2618_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2620_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
else
{
lean_object* v_a_2627_; 
v_a_2627_ = lean_ctor_get(v_rx_2604_, 1);
lean_inc(v_a_2627_);
lean_dec_ref(v_rx_2604_);
v___y_2612_ = v_ry_2605_;
v___y_2613_ = v_a_2627_;
goto v___jp_2611_;
}
}
else
{
lean_object* v_a_2628_; 
v_a_2628_ = lean_ctor_get(v_rx_2604_, 1);
lean_inc(v_a_2628_);
lean_dec_ref(v_rx_2604_);
v___y_2612_ = v_ry_2605_;
v___y_2613_ = v_a_2628_;
goto v___jp_2611_;
}
v___jp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2609_ = l_Lake_JobState_merge(v___y_2607_, v___y_2608_);
v___x_2610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2603_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
return v___x_2610_;
}
v___jp_2611_:
{
lean_object* v_a_2614_; 
v_a_2614_ = lean_ctor_get(v___y_2612_, 1);
lean_inc(v_a_2614_);
lean_dec_ref(v___y_2612_);
v___y_2607_ = v___y_2613_;
v___y_2608_ = v_a_2614_;
goto v___jp_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object* v_other_2629_, lean_object* v___x_2630_, uint8_t v___x_2631_, lean_object* v_rx_2632_){
_start:
{
lean_object* v_task_2633_; lean_object* v___f_2634_; lean_object* v___x_2635_; 
v_task_2633_ = lean_ctor_get(v_other_2629_, 0);
lean_inc_ref(v_task_2633_);
lean_dec_ref(v_other_2629_);
lean_inc(v___x_2630_);
v___f_2634_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2634_, 0, v___x_2630_);
lean_closure_set(v___f_2634_, 1, v_rx_2632_);
v___x_2635_ = lean_task_map(v___f_2634_, v_task_2633_, v___x_2630_, v___x_2631_);
return v___x_2635_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object* v_other_2636_, lean_object* v___x_2637_, lean_object* v___x_2638_, lean_object* v_rx_2639_){
_start:
{
uint8_t v___x_142__boxed_2640_; lean_object* v_res_2641_; 
v___x_142__boxed_2640_ = lean_unbox(v___x_2638_);
v_res_2641_ = l_Lake_Job_mix___redArg___lam__1(v_other_2636_, v___x_2637_, v___x_142__boxed_2640_, v_rx_2639_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object* v_self_2642_, lean_object* v_other_2643_){
_start:
{
lean_object* v_task_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2659_; 
v_task_2644_ = lean_ctor_get(v_self_2642_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v_self_2642_);
if (v_isSharedCheck_2659_ == 0)
{
lean_object* v_unused_2660_; lean_object* v_unused_2661_; 
v_unused_2660_ = lean_ctor_get(v_self_2642_, 2);
lean_dec(v_unused_2660_);
v_unused_2661_ = lean_ctor_get(v_self_2642_, 1);
lean_dec(v_unused_2661_);
v___x_2646_ = v_self_2642_;
v_isShared_2647_ = v_isSharedCheck_2659_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_task_2644_);
lean_dec(v_self_2642_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2659_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; uint8_t v___x_2650_; lean_object* v___x_2651_; lean_object* v___f_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; lean_object* v___x_2657_; 
v___x_2648_ = l_Lake_instDataKindUnit;
v___x_2649_ = lean_unsigned_to_nat(0u);
v___x_2650_ = 1;
v___x_2651_ = lean_box(v___x_2650_);
v___f_2652_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2652_, 0, v_other_2643_);
lean_closure_set(v___f_2652_, 1, v___x_2649_);
lean_closure_set(v___f_2652_, 2, v___x_2651_);
v___x_2653_ = lean_task_bind(v_task_2644_, v___f_2652_, v___x_2649_, v___x_2650_);
v___x_2654_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2655_ = 0;
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 2, v___x_2654_);
lean_ctor_set(v___x_2646_, 1, v___x_2648_);
lean_ctor_set(v___x_2646_, 0, v___x_2653_);
v___x_2657_ = v___x_2646_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v___x_2653_);
lean_ctor_set(v_reuseFailAlloc_2658_, 1, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2658_, 2, v___x_2654_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
lean_ctor_set_uint8(v___x_2657_, sizeof(void*)*3, v___x_2655_);
return v___x_2657_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object* v_00_u03b1_2662_, lean_object* v_00_u03b2_2663_, lean_object* v_self_2664_, lean_object* v_other_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lake_Job_mix___redArg(v_self_2664_, v_other_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(lean_object* v_as_2667_, size_t v_i_2668_, size_t v_stop_2669_, lean_object* v_b_2670_){
_start:
{
uint8_t v___x_2671_; 
v___x_2671_ = lean_usize_dec_eq(v_i_2668_, v_stop_2669_);
if (v___x_2671_ == 0)
{
size_t v___x_2672_; size_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2672_ = ((size_t)1ULL);
v___x_2673_ = lean_usize_sub(v_i_2668_, v___x_2672_);
v___x_2674_ = lean_array_uget_borrowed(v_as_2667_, v___x_2673_);
lean_inc(v___x_2674_);
v___x_2675_ = l_Lake_Job_mix___redArg(v___x_2674_, v_b_2670_);
v_i_2668_ = v___x_2673_;
v_b_2670_ = v___x_2675_;
goto _start;
}
else
{
return v_b_2670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2677_, lean_object* v_i_2678_, lean_object* v_stop_2679_, lean_object* v_b_2680_){
_start:
{
size_t v_i_boxed_2681_; size_t v_stop_boxed_2682_; lean_object* v_res_2683_; 
v_i_boxed_2681_ = lean_unbox_usize(v_i_2678_);
lean_dec(v_i_2678_);
v_stop_boxed_2682_ = lean_unbox_usize(v_stop_2679_);
lean_dec(v_stop_2679_);
v_res_2683_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2677_, v_i_boxed_2681_, v_stop_boxed_2682_, v_b_2680_);
lean_dec_ref(v_as_2677_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(lean_object* v_init_2684_, lean_object* v_l_2685_){
_start:
{
lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; uint8_t v___x_2689_; 
v___x_2686_ = lean_array_mk(v_l_2685_);
v___x_2687_ = lean_array_get_size(v___x_2686_);
v___x_2688_ = lean_unsigned_to_nat(0u);
v___x_2689_ = lean_nat_dec_lt(v___x_2688_, v___x_2687_);
if (v___x_2689_ == 0)
{
lean_dec_ref(v___x_2686_);
return v_init_2684_;
}
else
{
size_t v___x_2690_; size_t v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = lean_usize_of_nat(v___x_2687_);
v___x_2691_ = ((size_t)0ULL);
v___x_2692_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v___x_2686_, v___x_2690_, v___x_2691_, v_init_2684_);
lean_dec_ref(v___x_2686_);
return v___x_2692_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object* v_jobs_2693_, lean_object* v_traceCaption_2694_){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2695_ = lean_box(0);
v___x_2696_ = lean_box(0);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2699_ = 0;
v___x_2700_ = 0;
v___x_2701_ = l_Lake_BuildTrace_nil(v_traceCaption_2694_);
v___x_2702_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2702_, 0, v___x_2698_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
lean_ctor_set(v___x_2702_, 2, v___x_2697_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*3, v___x_2699_);
lean_ctor_set_uint8(v___x_2702_, sizeof(void*)*3 + 1, v___x_2700_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___x_2695_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_task_pure(v___x_2703_);
v___x_2705_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2706_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2696_);
lean_ctor_set(v___x_2706_, 2, v___x_2705_);
lean_ctor_set_uint8(v___x_2706_, sizeof(void*)*3, v___x_2700_);
v___x_2707_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v___x_2706_, v_jobs_2693_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object* v_00_u03b1_2708_, lean_object* v_jobs_2709_, lean_object* v_traceCaption_2710_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lake_Job_mixList___redArg(v_jobs_2709_, v_traceCaption_2710_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0(lean_object* v_00_u03b1_2712_, lean_object* v_init_2713_, lean_object* v_l_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v_init_2713_, v_l_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(lean_object* v_00_u03b1_2716_, lean_object* v_as_2717_, size_t v_i_2718_, size_t v_stop_2719_, lean_object* v_b_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2717_, v_i_2718_, v_stop_2719_, v_b_2720_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_as_2723_, lean_object* v_i_2724_, lean_object* v_stop_2725_, lean_object* v_b_2726_){
_start:
{
size_t v_i_boxed_2727_; size_t v_stop_boxed_2728_; lean_object* v_res_2729_; 
v_i_boxed_2727_ = lean_unbox_usize(v_i_2724_);
lean_dec(v_i_2724_);
v_stop_boxed_2728_ = lean_unbox_usize(v_stop_2725_);
lean_dec(v_stop_2725_);
v_res_2729_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(v_00_u03b1_2722_, v_as_2723_, v_i_boxed_2727_, v_stop_boxed_2728_, v_b_2726_);
lean_dec_ref(v_as_2723_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(lean_object* v_as_2730_, size_t v_i_2731_, size_t v_stop_2732_, lean_object* v_b_2733_){
_start:
{
uint8_t v___x_2734_; 
v___x_2734_ = lean_usize_dec_eq(v_i_2731_, v_stop_2732_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; lean_object* v___x_2736_; size_t v___x_2737_; size_t v___x_2738_; 
v___x_2735_ = lean_array_uget_borrowed(v_as_2730_, v_i_2731_);
lean_inc(v___x_2735_);
v___x_2736_ = l_Lake_Job_mix___redArg(v_b_2733_, v___x_2735_);
v___x_2737_ = ((size_t)1ULL);
v___x_2738_ = lean_usize_add(v_i_2731_, v___x_2737_);
v_i_2731_ = v___x_2738_;
v_b_2733_ = v___x_2736_;
goto _start;
}
else
{
return v_b_2733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg___boxed(lean_object* v_as_2740_, lean_object* v_i_2741_, lean_object* v_stop_2742_, lean_object* v_b_2743_){
_start:
{
size_t v_i_boxed_2744_; size_t v_stop_boxed_2745_; lean_object* v_res_2746_; 
v_i_boxed_2744_ = lean_unbox_usize(v_i_2741_);
lean_dec(v_i_2741_);
v_stop_boxed_2745_ = lean_unbox_usize(v_stop_2742_);
lean_dec(v_stop_2742_);
v_res_2746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2740_, v_i_boxed_2744_, v_stop_boxed_2745_, v_b_2743_);
lean_dec_ref(v_as_2740_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object* v_jobs_2747_, lean_object* v_traceCaption_2748_){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; uint8_t v___x_2753_; uint8_t v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2749_ = lean_box(0);
v___x_2750_ = lean_box(0);
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2753_ = 0;
v___x_2754_ = 0;
v___x_2755_ = l_Lake_BuildTrace_nil(v_traceCaption_2748_);
v___x_2756_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2756_, 0, v___x_2752_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
lean_ctor_set(v___x_2756_, 2, v___x_2751_);
lean_ctor_set_uint8(v___x_2756_, sizeof(void*)*3, v___x_2753_);
lean_ctor_set_uint8(v___x_2756_, sizeof(void*)*3 + 1, v___x_2754_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2749_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
v___x_2758_ = lean_task_pure(v___x_2757_);
v___x_2759_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2760_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2760_, 0, v___x_2758_);
lean_ctor_set(v___x_2760_, 1, v___x_2750_);
lean_ctor_set(v___x_2760_, 2, v___x_2759_);
lean_ctor_set_uint8(v___x_2760_, sizeof(void*)*3, v___x_2754_);
v___x_2761_ = lean_array_get_size(v_jobs_2747_);
v___x_2762_ = lean_nat_dec_lt(v___x_2751_, v___x_2761_);
if (v___x_2762_ == 0)
{
return v___x_2760_;
}
else
{
uint8_t v___x_2763_; 
v___x_2763_ = lean_nat_dec_le(v___x_2761_, v___x_2761_);
if (v___x_2763_ == 0)
{
if (v___x_2762_ == 0)
{
return v___x_2760_;
}
else
{
size_t v___x_2764_; size_t v___x_2765_; lean_object* v___x_2766_; 
v___x_2764_ = ((size_t)0ULL);
v___x_2765_ = lean_usize_of_nat(v___x_2761_);
v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2747_, v___x_2764_, v___x_2765_, v___x_2760_);
return v___x_2766_;
}
}
else
{
size_t v___x_2767_; size_t v___x_2768_; lean_object* v___x_2769_; 
v___x_2767_ = ((size_t)0ULL);
v___x_2768_ = lean_usize_of_nat(v___x_2761_);
v___x_2769_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2747_, v___x_2767_, v___x_2768_, v___x_2760_);
return v___x_2769_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object* v_jobs_2770_, lean_object* v_traceCaption_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_Lake_Job_mixArray___redArg(v_jobs_2770_, v_traceCaption_2771_);
lean_dec_ref(v_jobs_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object* v_00_u03b1_2773_, lean_object* v_jobs_2774_, lean_object* v_traceCaption_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Lake_Job_mixArray___redArg(v_jobs_2774_, v_traceCaption_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object* v_00_u03b1_2777_, lean_object* v_jobs_2778_, lean_object* v_traceCaption_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lake_Job_mixArray(v_00_u03b1_2777_, v_jobs_2778_, v_traceCaption_2779_);
lean_dec_ref(v_jobs_2778_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_object* v_00_u03b1_2781_, lean_object* v_as_2782_, size_t v_i_2783_, size_t v_stop_2784_, lean_object* v_b_2785_){
_start:
{
lean_object* v___x_2786_; 
v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2782_, v_i_2783_, v_stop_2784_, v_b_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(lean_object* v_00_u03b1_2787_, lean_object* v_as_2788_, lean_object* v_i_2789_, lean_object* v_stop_2790_, lean_object* v_b_2791_){
_start:
{
size_t v_i_boxed_2792_; size_t v_stop_boxed_2793_; lean_object* v_res_2794_; 
v_i_boxed_2792_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_stop_boxed_2793_ = lean_unbox_usize(v_stop_2790_);
lean_dec(v_stop_2790_);
v_res_2794_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(v_00_u03b1_2787_, v_as_2788_, v_i_boxed_2792_, v_stop_boxed_2793_, v_b_2791_);
lean_dec_ref(v_as_2788_);
return v_res_2794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object* v___x_2795_, lean_object* v_rx_2796_, lean_object* v_ry_2797_){
_start:
{
lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2804_; lean_object* v___y_2805_; 
if (lean_obj_tag(v_rx_2796_) == 0)
{
if (lean_obj_tag(v_ry_2797_) == 0)
{
lean_object* v_a_2807_; lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v___x_2795_);
v_a_2807_ = lean_ctor_get(v_rx_2796_, 0);
v_a_2808_ = lean_ctor_get(v_rx_2796_, 1);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_rx_2796_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2810_ = v_rx_2796_;
v_isShared_2811_ = v_isSharedCheck_2825_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_inc(v_a_2807_);
lean_dec(v_rx_2796_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2825_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v_a_2812_; lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2824_; 
v_a_2812_ = lean_ctor_get(v_ry_2797_, 0);
v_a_2813_ = lean_ctor_get(v_ry_2797_, 1);
v_isSharedCheck_2824_ = !lean_is_exclusive(v_ry_2797_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2815_ = v_ry_2797_;
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_inc(v_a_2812_);
lean_dec(v_ry_2797_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2824_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2811_ == 0)
{
lean_ctor_set_tag(v___x_2810_, 1);
lean_ctor_set(v___x_2810_, 1, v_a_2812_);
v___x_2818_ = v___x_2810_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2807_);
lean_ctor_set(v_reuseFailAlloc_2823_, 1, v_a_2812_);
v___x_2818_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = l_Lake_JobState_merge(v_a_2808_, v_a_2813_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 1, v___x_2819_);
lean_ctor_set(v___x_2815_, 0, v___x_2818_);
v___x_2821_ = v___x_2815_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2818_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
else
{
lean_object* v_a_2826_; 
v_a_2826_ = lean_ctor_get(v_rx_2796_, 1);
lean_inc(v_a_2826_);
lean_dec_ref(v_rx_2796_);
v___y_2804_ = v_ry_2797_;
v___y_2805_ = v_a_2826_;
goto v___jp_2803_;
}
}
else
{
lean_object* v_a_2827_; 
v_a_2827_ = lean_ctor_get(v_rx_2796_, 1);
lean_inc(v_a_2827_);
lean_dec_ref(v_rx_2796_);
v___y_2804_ = v_ry_2797_;
v___y_2805_ = v_a_2827_;
goto v___jp_2803_;
}
v___jp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
v___x_2801_ = l_Lake_JobState_merge(v___y_2799_, v___y_2800_);
v___x_2802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2795_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
return v___x_2802_;
}
v___jp_2803_:
{
lean_object* v_a_2806_; 
v_a_2806_ = lean_ctor_get(v___y_2804_, 1);
lean_inc(v_a_2806_);
lean_dec_ref(v___y_2804_);
v___y_2799_ = v___y_2805_;
v___y_2800_ = v_a_2806_;
goto v___jp_2798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object* v_b_2828_, lean_object* v___x_2829_, uint8_t v___x_2830_, lean_object* v_rx_2831_){
_start:
{
lean_object* v_task_2832_; lean_object* v___f_2833_; lean_object* v___x_2834_; 
v_task_2832_ = lean_ctor_get(v_b_2828_, 0);
lean_inc_ref(v_task_2832_);
lean_dec_ref(v_b_2828_);
lean_inc(v___x_2829_);
v___f_2833_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2833_, 0, v___x_2829_);
lean_closure_set(v___f_2833_, 1, v_rx_2831_);
v___x_2834_ = lean_task_map(v___f_2833_, v_task_2832_, v___x_2829_, v___x_2830_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_b_2835_, lean_object* v___x_2836_, lean_object* v___x_2837_, lean_object* v_rx_2838_){
_start:
{
uint8_t v___x_480__boxed_2839_; lean_object* v_res_2840_; 
v___x_480__boxed_2839_ = lean_unbox(v___x_2837_);
v_res_2840_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_2835_, v___x_2836_, v___x_480__boxed_2839_, v_rx_2838_);
return v_res_2840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(lean_object* v_as_2841_, size_t v_i_2842_, size_t v_stop_2843_, lean_object* v_b_2844_){
_start:
{
uint8_t v___x_2845_; 
v___x_2845_ = lean_usize_dec_eq(v_i_2842_, v_stop_2843_);
if (v___x_2845_ == 0)
{
size_t v___x_2846_; size_t v___x_2847_; lean_object* v___x_2848_; lean_object* v_task_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2864_; 
v___x_2846_ = ((size_t)1ULL);
v___x_2847_ = lean_usize_sub(v_i_2842_, v___x_2846_);
v___x_2848_ = lean_array_uget(v_as_2841_, v___x_2847_);
v_task_2849_ = lean_ctor_get(v___x_2848_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2848_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; lean_object* v_unused_2866_; 
v_unused_2865_ = lean_ctor_get(v___x_2848_, 2);
lean_dec(v_unused_2865_);
v_unused_2866_ = lean_ctor_get(v___x_2848_, 1);
lean_dec(v_unused_2866_);
v___x_2851_ = v___x_2848_;
v_isShared_2852_ = v_isSharedCheck_2864_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_task_2849_);
lean_dec(v___x_2848_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2864_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; uint8_t v___x_2855_; lean_object* v___x_2856_; lean_object* v___f_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
v___x_2853_ = lean_box(0);
v___x_2854_ = lean_unsigned_to_nat(0u);
v___x_2855_ = 1;
v___x_2856_ = lean_box(v___x_2855_);
v___f_2857_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2857_, 0, v_b_2844_);
lean_closure_set(v___f_2857_, 1, v___x_2854_);
lean_closure_set(v___f_2857_, 2, v___x_2856_);
v___x_2858_ = lean_task_bind(v_task_2849_, v___f_2857_, v___x_2854_, v___x_2855_);
v___x_2859_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 2, v___x_2859_);
lean_ctor_set(v___x_2851_, 1, v___x_2853_);
lean_ctor_set(v___x_2851_, 0, v___x_2858_);
v___x_2861_ = v___x_2851_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2863_; 
v_reuseFailAlloc_2863_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2863_, 0, v___x_2858_);
lean_ctor_set(v_reuseFailAlloc_2863_, 1, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2863_, 2, v___x_2859_);
v___x_2861_ = v_reuseFailAlloc_2863_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*3, v___x_2845_);
v_i_2842_ = v___x_2847_;
v_b_2844_ = v___x_2861_;
goto _start;
}
}
}
else
{
return v_b_2844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2867_, lean_object* v_i_2868_, lean_object* v_stop_2869_, lean_object* v_b_2870_){
_start:
{
size_t v_i_boxed_2871_; size_t v_stop_boxed_2872_; lean_object* v_res_2873_; 
v_i_boxed_2871_ = lean_unbox_usize(v_i_2868_);
lean_dec(v_i_2868_);
v_stop_boxed_2872_ = lean_unbox_usize(v_stop_2869_);
lean_dec(v_stop_2869_);
v_res_2873_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_2867_, v_i_boxed_2871_, v_stop_boxed_2872_, v_b_2870_);
lean_dec_ref(v_as_2867_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(lean_object* v_init_2874_, lean_object* v_l_2875_){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2876_ = lean_array_mk(v_l_2875_);
v___x_2877_ = lean_array_get_size(v___x_2876_);
v___x_2878_ = lean_unsigned_to_nat(0u);
v___x_2879_ = lean_nat_dec_lt(v___x_2878_, v___x_2877_);
if (v___x_2879_ == 0)
{
lean_dec_ref(v___x_2876_);
return v_init_2874_;
}
else
{
size_t v___x_2880_; size_t v___x_2881_; lean_object* v___x_2882_; 
v___x_2880_ = lean_usize_of_nat(v___x_2877_);
v___x_2881_ = ((size_t)0ULL);
v___x_2882_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v___x_2876_, v___x_2880_, v___x_2881_, v_init_2874_);
lean_dec_ref(v___x_2876_);
return v___x_2882_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object* v_jobs_2883_, lean_object* v_traceCaption_2884_){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; uint8_t v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2885_ = lean_box(0);
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_unsigned_to_nat(0u);
v___x_2888_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2889_ = 0;
v___x_2890_ = 0;
v___x_2891_ = l_Lake_BuildTrace_nil(v_traceCaption_2884_);
v___x_2892_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2892_, 0, v___x_2888_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
lean_ctor_set(v___x_2892_, 2, v___x_2887_);
lean_ctor_set_uint8(v___x_2892_, sizeof(void*)*3, v___x_2889_);
lean_ctor_set_uint8(v___x_2892_, sizeof(void*)*3 + 1, v___x_2890_);
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2885_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = lean_task_pure(v___x_2893_);
v___x_2895_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2896_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2896_, 0, v___x_2894_);
lean_ctor_set(v___x_2896_, 1, v___x_2886_);
lean_ctor_set(v___x_2896_, 2, v___x_2895_);
lean_ctor_set_uint8(v___x_2896_, sizeof(void*)*3, v___x_2890_);
v___x_2897_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v___x_2896_, v_jobs_2883_);
return v___x_2897_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object* v_00_u03b1_2898_, lean_object* v_jobs_2899_, lean_object* v_traceCaption_2900_){
_start:
{
lean_object* v___x_2901_; 
v___x_2901_ = l_Lake_Job_collectList___redArg(v_jobs_2899_, v_traceCaption_2900_);
return v___x_2901_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0(lean_object* v_00_u03b1_2902_, lean_object* v_init_2903_, lean_object* v_l_2904_){
_start:
{
lean_object* v___x_2905_; 
v___x_2905_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v_init_2903_, v_l_2904_);
return v___x_2905_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_object* v_00_u03b1_2906_, lean_object* v_as_2907_, size_t v_i_2908_, size_t v_stop_2909_, lean_object* v_b_2910_){
_start:
{
lean_object* v___x_2911_; 
v___x_2911_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_2907_, v_i_2908_, v_stop_2909_, v_b_2910_);
return v___x_2911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2912_, lean_object* v_as_2913_, lean_object* v_i_2914_, lean_object* v_stop_2915_, lean_object* v_b_2916_){
_start:
{
size_t v_i_boxed_2917_; size_t v_stop_boxed_2918_; lean_object* v_res_2919_; 
v_i_boxed_2917_ = lean_unbox_usize(v_i_2914_);
lean_dec(v_i_2914_);
v_stop_boxed_2918_ = lean_unbox_usize(v_stop_2915_);
lean_dec(v_stop_2915_);
v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(v_00_u03b1_2912_, v_as_2913_, v_i_boxed_2917_, v_stop_boxed_2918_, v_b_2916_);
lean_dec_ref(v_as_2913_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object* v___x_2920_, lean_object* v_rx_2921_, lean_object* v_ry_2922_){
_start:
{
lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2929_; lean_object* v___y_2930_; 
if (lean_obj_tag(v_rx_2921_) == 0)
{
if (lean_obj_tag(v_ry_2922_) == 0)
{
lean_object* v_a_2932_; lean_object* v_a_2933_; lean_object* v_a_2934_; lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v___x_2920_);
v_a_2932_ = lean_ctor_get(v_rx_2921_, 0);
lean_inc(v_a_2932_);
v_a_2933_ = lean_ctor_get(v_rx_2921_, 1);
lean_inc(v_a_2933_);
lean_dec_ref(v_rx_2921_);
v_a_2934_ = lean_ctor_get(v_ry_2922_, 0);
v_a_2935_ = lean_ctor_get(v_ry_2922_, 1);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_ry_2922_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2937_ = v_ry_2922_;
v_isShared_2938_ = v_isSharedCheck_2944_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_inc(v_a_2934_);
lean_dec(v_ry_2922_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2944_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
v___x_2939_ = lean_array_push(v_a_2932_, v_a_2934_);
v___x_2940_ = l_Lake_JobState_merge(v_a_2933_, v_a_2935_);
if (v_isShared_2938_ == 0)
{
lean_ctor_set(v___x_2937_, 1, v___x_2940_);
lean_ctor_set(v___x_2937_, 0, v___x_2939_);
v___x_2942_ = v___x_2937_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2939_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v___x_2940_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
lean_object* v_a_2945_; 
v_a_2945_ = lean_ctor_get(v_rx_2921_, 1);
lean_inc(v_a_2945_);
lean_dec_ref(v_rx_2921_);
v___y_2929_ = v_ry_2922_;
v___y_2930_ = v_a_2945_;
goto v___jp_2928_;
}
}
else
{
lean_object* v_a_2946_; 
v_a_2946_ = lean_ctor_get(v_rx_2921_, 1);
lean_inc(v_a_2946_);
lean_dec_ref(v_rx_2921_);
v___y_2929_ = v_ry_2922_;
v___y_2930_ = v_a_2946_;
goto v___jp_2928_;
}
v___jp_2923_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = l_Lake_JobState_merge(v___y_2924_, v___y_2925_);
v___x_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2920_);
lean_ctor_set(v___x_2927_, 1, v___x_2926_);
return v___x_2927_;
}
v___jp_2928_:
{
lean_object* v_a_2931_; 
v_a_2931_ = lean_ctor_get(v___y_2929_, 1);
lean_inc(v_a_2931_);
lean_dec_ref(v___y_2929_);
v___y_2924_ = v___y_2930_;
v___y_2925_ = v_a_2931_;
goto v___jp_2923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object* v___x_2947_, lean_object* v___x_2948_, uint8_t v___x_2949_, lean_object* v_rx_2950_){
_start:
{
lean_object* v_task_2951_; lean_object* v___f_2952_; lean_object* v___x_2953_; 
v_task_2951_ = lean_ctor_get(v___x_2947_, 0);
lean_inc_ref(v_task_2951_);
lean_dec_ref(v___x_2947_);
lean_inc(v___x_2948_);
v___f_2952_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2952_, 0, v___x_2948_);
lean_closure_set(v___f_2952_, 1, v_rx_2950_);
v___x_2953_ = lean_task_map(v___f_2952_, v_task_2951_, v___x_2948_, v___x_2949_);
return v___x_2953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object* v___x_2954_, lean_object* v___x_2955_, lean_object* v___x_2956_, lean_object* v_rx_2957_){
_start:
{
uint8_t v___x_411__boxed_2958_; lean_object* v_res_2959_; 
v___x_411__boxed_2958_ = lean_unbox(v___x_2956_);
v_res_2959_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_2954_, v___x_2955_, v___x_411__boxed_2958_, v_rx_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(lean_object* v_as_2960_, size_t v_i_2961_, size_t v_stop_2962_, lean_object* v_b_2963_){
_start:
{
uint8_t v___x_2964_; 
v___x_2964_ = lean_usize_dec_eq(v_i_2961_, v_stop_2962_);
if (v___x_2964_ == 0)
{
lean_object* v_task_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2983_; 
v_task_2965_ = lean_ctor_get(v_b_2963_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v_b_2963_);
if (v_isSharedCheck_2983_ == 0)
{
lean_object* v_unused_2984_; lean_object* v_unused_2985_; 
v_unused_2984_ = lean_ctor_get(v_b_2963_, 2);
lean_dec(v_unused_2984_);
v_unused_2985_ = lean_ctor_get(v_b_2963_, 1);
lean_dec(v_unused_2985_);
v___x_2967_ = v_b_2963_;
v_isShared_2968_ = v_isSharedCheck_2983_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_task_2965_);
lean_dec(v_b_2963_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2983_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; lean_object* v___x_2973_; lean_object* v___f_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2978_; 
v___x_2969_ = lean_box(0);
v___x_2970_ = lean_array_uget_borrowed(v_as_2960_, v_i_2961_);
v___x_2971_ = lean_unsigned_to_nat(0u);
v___x_2972_ = 1;
v___x_2973_ = lean_box(v___x_2972_);
lean_inc(v___x_2970_);
v___f_2974_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2974_, 0, v___x_2970_);
lean_closure_set(v___f_2974_, 1, v___x_2971_);
lean_closure_set(v___f_2974_, 2, v___x_2973_);
v___x_2975_ = lean_task_bind(v_task_2965_, v___f_2974_, v___x_2971_, v___x_2972_);
v___x_2976_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 2, v___x_2976_);
lean_ctor_set(v___x_2967_, 1, v___x_2969_);
lean_ctor_set(v___x_2967_, 0, v___x_2975_);
v___x_2978_ = v___x_2967_;
goto v_reusejp_2977_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v___x_2975_);
lean_ctor_set(v_reuseFailAlloc_2982_, 1, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2982_, 2, v___x_2976_);
v___x_2978_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2977_;
}
v_reusejp_2977_:
{
size_t v___x_2979_; size_t v___x_2980_; 
lean_ctor_set_uint8(v___x_2978_, sizeof(void*)*3, v___x_2964_);
v___x_2979_ = ((size_t)1ULL);
v___x_2980_ = lean_usize_add(v_i_2961_, v___x_2979_);
v_i_2961_ = v___x_2980_;
v_b_2963_ = v___x_2978_;
goto _start;
}
}
}
else
{
return v_b_2963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(lean_object* v_as_2986_, lean_object* v_i_2987_, lean_object* v_stop_2988_, lean_object* v_b_2989_){
_start:
{
size_t v_i_boxed_2990_; size_t v_stop_boxed_2991_; lean_object* v_res_2992_; 
v_i_boxed_2990_ = lean_unbox_usize(v_i_2987_);
lean_dec(v_i_2987_);
v_stop_boxed_2991_ = lean_unbox_usize(v_stop_2988_);
lean_dec(v_stop_2988_);
v_res_2992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_2986_, v_i_boxed_2990_, v_stop_boxed_2991_, v_b_2989_);
lean_dec_ref(v_as_2986_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object* v_jobs_2993_, lean_object* v_traceCaption_2994_){
_start:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v___x_2995_ = lean_array_get_size(v_jobs_2993_);
v___x_2996_ = lean_mk_empty_array_with_capacity(v___x_2995_);
v___x_2997_ = lean_box(0);
v___x_2998_ = lean_unsigned_to_nat(0u);
v___x_2999_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3000_ = 0;
v___x_3001_ = 0;
v___x_3002_ = l_Lake_BuildTrace_nil(v_traceCaption_2994_);
v___x_3003_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3003_, 0, v___x_2999_);
lean_ctor_set(v___x_3003_, 1, v___x_3002_);
lean_ctor_set(v___x_3003_, 2, v___x_2998_);
lean_ctor_set_uint8(v___x_3003_, sizeof(void*)*3, v___x_3000_);
lean_ctor_set_uint8(v___x_3003_, sizeof(void*)*3 + 1, v___x_3001_);
v___x_3004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3004_, 0, v___x_2996_);
lean_ctor_set(v___x_3004_, 1, v___x_3003_);
v___x_3005_ = lean_task_pure(v___x_3004_);
v___x_3006_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3007_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_2997_);
lean_ctor_set(v___x_3007_, 2, v___x_3006_);
lean_ctor_set_uint8(v___x_3007_, sizeof(void*)*3, v___x_3001_);
v___x_3008_ = lean_nat_dec_lt(v___x_2998_, v___x_2995_);
if (v___x_3008_ == 0)
{
return v___x_3007_;
}
else
{
uint8_t v___x_3009_; 
v___x_3009_ = lean_nat_dec_le(v___x_2995_, v___x_2995_);
if (v___x_3009_ == 0)
{
if (v___x_3008_ == 0)
{
return v___x_3007_;
}
else
{
size_t v___x_3010_; size_t v___x_3011_; lean_object* v___x_3012_; 
v___x_3010_ = ((size_t)0ULL);
v___x_3011_ = lean_usize_of_nat(v___x_2995_);
v___x_3012_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_2993_, v___x_3010_, v___x_3011_, v___x_3007_);
return v___x_3012_;
}
}
else
{
size_t v___x_3013_; size_t v___x_3014_; lean_object* v___x_3015_; 
v___x_3013_ = ((size_t)0ULL);
v___x_3014_ = lean_usize_of_nat(v___x_2995_);
v___x_3015_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_2993_, v___x_3013_, v___x_3014_, v___x_3007_);
return v___x_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object* v_jobs_3016_, lean_object* v_traceCaption_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lake_Job_collectArray___redArg(v_jobs_3016_, v_traceCaption_3017_);
lean_dec_ref(v_jobs_3016_);
return v_res_3018_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object* v_00_u03b1_3019_, lean_object* v_jobs_3020_, lean_object* v_traceCaption_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = l_Lake_Job_collectArray___redArg(v_jobs_3020_, v_traceCaption_3021_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object* v_00_u03b1_3023_, lean_object* v_jobs_3024_, lean_object* v_traceCaption_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lake_Job_collectArray(v_00_u03b1_3023_, v_jobs_3024_, v_traceCaption_3025_);
lean_dec_ref(v_jobs_3024_);
return v_res_3026_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_object* v_00_u03b1_3027_, lean_object* v_as_3028_, size_t v_i_3029_, size_t v_stop_3030_, lean_object* v_b_3031_){
_start:
{
lean_object* v___x_3032_; 
v___x_3032_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3028_, v_i_3029_, v_stop_3030_, v_b_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(lean_object* v_00_u03b1_3033_, lean_object* v_as_3034_, lean_object* v_i_3035_, lean_object* v_stop_3036_, lean_object* v_b_3037_){
_start:
{
size_t v_i_boxed_3038_; size_t v_stop_boxed_3039_; lean_object* v_res_3040_; 
v_i_boxed_3038_ = lean_unbox_usize(v_i_3035_);
lean_dec(v_i_3035_);
v_stop_boxed_3039_ = lean_unbox_usize(v_stop_3036_);
lean_dec(v_stop_3036_);
v_res_3040_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(v_00_u03b1_3033_, v_as_3034_, v_i_boxed_3038_, v_stop_boxed_3039_, v_b_3037_);
lean_dec_ref(v_as_3034_);
return v_res_3040_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(lean_object* v_00_u03b1_3041_, lean_object* v_inst_3042_){
_start:
{
lean_object* v___x_3043_; 
v___x_3043_ = lean_box(0);
return v___x_3043_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0(lean_object* v___x_3044_, lean_object* v_rx_3045_, lean_object* v_i_3046_, lean_object* v_ry_3047_){
_start:
{
lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3054_; lean_object* v___y_3055_; 
if (lean_obj_tag(v_rx_3045_) == 0)
{
if (lean_obj_tag(v_ry_3047_) == 0)
{
lean_object* v_a_3057_; lean_object* v_a_3058_; lean_object* v_a_3059_; lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v___x_3044_);
v_a_3057_ = lean_ctor_get(v_rx_3045_, 0);
lean_inc(v_a_3057_);
v_a_3058_ = lean_ctor_get(v_rx_3045_, 1);
lean_inc(v_a_3058_);
lean_dec_ref(v_rx_3045_);
v_a_3059_ = lean_ctor_get(v_ry_3047_, 0);
v_a_3060_ = lean_ctor_get(v_ry_3047_, 1);
v_isSharedCheck_3069_ = !lean_is_exclusive(v_ry_3047_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3062_ = v_ry_3047_;
v_isShared_3063_ = v_isSharedCheck_3069_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_inc(v_a_3059_);
lean_dec(v_ry_3047_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3069_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3067_; 
v___x_3064_ = lean_array_fset(v_a_3057_, v_i_3046_, v_a_3059_);
v___x_3065_ = l_Lake_JobState_merge(v_a_3058_, v_a_3060_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 1, v___x_3065_);
lean_ctor_set(v___x_3062_, 0, v___x_3064_);
v___x_3067_ = v___x_3062_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v___x_3064_);
lean_ctor_set(v_reuseFailAlloc_3068_, 1, v___x_3065_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
else
{
lean_object* v_a_3070_; 
v_a_3070_ = lean_ctor_get(v_rx_3045_, 1);
lean_inc(v_a_3070_);
lean_dec_ref(v_rx_3045_);
v___y_3054_ = v_ry_3047_;
v___y_3055_ = v_a_3070_;
goto v___jp_3053_;
}
}
else
{
lean_object* v_a_3071_; 
v_a_3071_ = lean_ctor_get(v_rx_3045_, 1);
lean_inc(v_a_3071_);
lean_dec_ref(v_rx_3045_);
v___y_3054_ = v_ry_3047_;
v___y_3055_ = v_a_3071_;
goto v___jp_3053_;
}
v___jp_3048_:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = l_Lake_JobState_merge(v___y_3049_, v___y_3050_);
v___x_3052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3044_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
return v___x_3052_;
}
v___jp_3053_:
{
lean_object* v_a_3056_; 
v_a_3056_ = lean_ctor_get(v___y_3054_, 1);
lean_inc(v_a_3056_);
lean_dec_ref(v___y_3054_);
v___y_3049_ = v___y_3055_;
v___y_3050_ = v_a_3056_;
goto v___jp_3048_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0___boxed(lean_object* v___x_3072_, lean_object* v_rx_3073_, lean_object* v_i_3074_, lean_object* v_ry_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_Lake_Job_collectVector___redArg___lam__0(v___x_3072_, v_rx_3073_, v_i_3074_, v_ry_3075_);
lean_dec(v_i_3074_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1(lean_object* v___x_3077_, lean_object* v___x_3078_, lean_object* v_i_3079_, uint8_t v___x_3080_, lean_object* v_rx_3081_){
_start:
{
lean_object* v_task_3082_; lean_object* v___f_3083_; lean_object* v___x_3084_; 
v_task_3082_ = lean_ctor_get(v___x_3077_, 0);
lean_inc_ref(v_task_3082_);
lean_dec_ref(v___x_3077_);
lean_inc(v___x_3078_);
v___f_3083_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3083_, 0, v___x_3078_);
lean_closure_set(v___f_3083_, 1, v_rx_3081_);
lean_closure_set(v___f_3083_, 2, v_i_3079_);
v___x_3084_ = lean_task_map(v___f_3083_, v_task_3082_, v___x_3078_, v___x_3080_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1___boxed(lean_object* v___x_3085_, lean_object* v___x_3086_, lean_object* v_i_3087_, lean_object* v___x_3088_, lean_object* v_rx_3089_){
_start:
{
uint8_t v___x_191__boxed_3090_; lean_object* v_res_3091_; 
v___x_191__boxed_3090_ = lean_unbox(v___x_3088_);
v_res_3091_ = l_Lake_Job_collectVector___redArg___lam__1(v___x_3085_, v___x_3086_, v_i_3087_, v___x_191__boxed_3090_, v_rx_3089_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2(lean_object* v_jobs_3092_, lean_object* v___x_3093_, lean_object* v_i_3094_, lean_object* v_h_3095_, lean_object* v_job_3096_){
_start:
{
lean_object* v_task_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3112_; 
v_task_3097_ = lean_ctor_get(v_job_3096_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v_job_3096_);
if (v_isSharedCheck_3112_ == 0)
{
lean_object* v_unused_3113_; lean_object* v_unused_3114_; 
v_unused_3113_ = lean_ctor_get(v_job_3096_, 2);
lean_dec(v_unused_3113_);
v_unused_3114_ = lean_ctor_get(v_job_3096_, 1);
lean_dec(v_unused_3114_);
v___x_3099_ = v_job_3096_;
v_isShared_3100_ = v_isSharedCheck_3112_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_task_3097_);
lean_dec(v_job_3096_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3112_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; uint8_t v___x_3103_; lean_object* v___x_3104_; lean_object* v___f_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; uint8_t v___x_3108_; lean_object* v___x_3110_; 
v___x_3101_ = lean_array_fget_borrowed(v_jobs_3092_, v_i_3094_);
v___x_3102_ = lean_unsigned_to_nat(0u);
v___x_3103_ = 1;
v___x_3104_ = lean_box(v___x_3103_);
lean_inc(v___x_3101_);
v___f_3105_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3105_, 0, v___x_3101_);
lean_closure_set(v___f_3105_, 1, v___x_3102_);
lean_closure_set(v___f_3105_, 2, v_i_3094_);
lean_closure_set(v___f_3105_, 3, v___x_3104_);
v___x_3106_ = lean_task_bind(v_task_3097_, v___f_3105_, v___x_3102_, v___x_3103_);
v___x_3107_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3108_ = 0;
if (v_isShared_3100_ == 0)
{
lean_ctor_set(v___x_3099_, 2, v___x_3107_);
lean_ctor_set(v___x_3099_, 1, v___x_3093_);
lean_ctor_set(v___x_3099_, 0, v___x_3106_);
v___x_3110_ = v___x_3099_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3106_);
lean_ctor_set(v_reuseFailAlloc_3111_, 1, v___x_3093_);
lean_ctor_set(v_reuseFailAlloc_3111_, 2, v___x_3107_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
lean_ctor_set_uint8(v___x_3110_, sizeof(void*)*3, v___x_3108_);
return v___x_3110_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2___boxed(lean_object* v_jobs_3115_, lean_object* v___x_3116_, lean_object* v_i_3117_, lean_object* v_h_3118_, lean_object* v_job_3119_){
_start:
{
lean_object* v_res_3120_; 
v_res_3120_ = l_Lake_Job_collectVector___redArg___lam__2(v_jobs_3115_, v___x_3116_, v_i_3117_, v_h_3118_, v_job_3119_);
lean_dec_ref(v_jobs_3115_);
return v_res_3120_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg(lean_object* v_n_3121_, lean_object* v_jobs_3122_, lean_object* v_traceCaption_3123_){
_start:
{
lean_object* v_placeholder_3124_; lean_object* v___x_3125_; lean_object* v___f_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; uint8_t v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v_placeholder_3124_ = lean_box(0);
v___x_3125_ = lean_box(0);
v___f_3126_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3126_, 0, v_jobs_3122_);
lean_closure_set(v___f_3126_, 1, v___x_3125_);
lean_inc(v_n_3121_);
v___x_3127_ = lean_mk_array(v_n_3121_, v_placeholder_3124_);
v___x_3128_ = lean_unsigned_to_nat(0u);
v___x_3129_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3130_ = 0;
v___x_3131_ = 0;
v___x_3132_ = l_Lake_BuildTrace_nil(v_traceCaption_3123_);
v___x_3133_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3133_, 0, v___x_3129_);
lean_ctor_set(v___x_3133_, 1, v___x_3132_);
lean_ctor_set(v___x_3133_, 2, v___x_3128_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*3, v___x_3130_);
lean_ctor_set_uint8(v___x_3133_, sizeof(void*)*3 + 1, v___x_3131_);
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3127_);
lean_ctor_set(v___x_3134_, 1, v___x_3133_);
v___x_3135_ = lean_task_pure(v___x_3134_);
v___x_3136_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3137_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3137_, 0, v___x_3135_);
lean_ctor_set(v___x_3137_, 1, v___x_3125_);
lean_ctor_set(v___x_3137_, 2, v___x_3136_);
lean_ctor_set_uint8(v___x_3137_, sizeof(void*)*3, v___x_3131_);
lean_inc(v_n_3121_);
v___x_3138_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3121_, v___f_3126_, v_n_3121_, lean_box(0), v___x_3137_);
lean_dec(v_n_3121_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector(lean_object* v_n_3139_, lean_object* v_00_u03b1_3140_, lean_object* v_inst_3141_, lean_object* v_jobs_3142_, lean_object* v_traceCaption_3143_){
_start:
{
lean_object* v___x_3144_; 
v___x_3144_ = l_Lake_Job_collectVector___redArg(v_n_3139_, v_jobs_3142_, v_traceCaption_3143_);
return v___x_3144_;
}
}
lean_object* runtime_initialize_Lake_Build_Fetch(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Build_Job_Monad(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
