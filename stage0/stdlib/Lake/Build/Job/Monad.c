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
lean_dec_ref(v___x_274_);
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
lean_dec_ref(v___x_1411_);
v___x_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_a_1412_);
v___x_1415_ = l_Lake_Job_sync___redArg___lam__0(v___x_1408_, v___x_1409_, v___x_1414_, v_a_1413_);
lean_dec_ref(v___x_1414_);
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
lean_dec_ref(v___x_1411_);
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
lean_dec_ref(v___x_1526_);
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
lean_dec_ref(v___x_1515_);
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
uint8_t v___x_22647__boxed_1581_; uint8_t v___x_22648__boxed_1582_; lean_object* v_res_1583_; 
v___x_22647__boxed_1581_ = lean_unbox(v___x_1570_);
v___x_22648__boxed_1582_ = lean_unbox(v___x_1571_);
v_res_1583_ = l_Lake_Job_async___redArg___lam__1(v___x_1568_, v___x_1569_, v___x_22647__boxed_1581_, v___x_22648__boxed_1582_, v___x_1572_, v___x_1573_, v_act_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_);
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
lean_dec_ref(v___x_1661_);
v___x_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1663_, 0, v_a_1662_);
return v___x_1663_;
}
else
{
lean_object* v___x_1664_; 
lean_dec_ref(v___x_1661_);
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
lean_dec_ref(v___x_1672_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_a_1673_);
return v___x_1674_;
}
else
{
lean_object* v___x_1675_; 
lean_dec_ref(v___x_1672_);
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
lean_object* v_a_1708_; lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1742_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_a_1709_ = lean_ctor_get(v___x_1707_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1711_ = v___x_1707_;
v_isShared_1712_ = v_isSharedCheck_1742_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1742_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v_a_1714_; lean_object* v___y_1719_; lean_object* v_log_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_log_1730_ = lean_ctor_get(v_a_1709_, 0);
lean_inc_ref(v_log_1730_);
lean_dec(v_a_1709_);
v___x_1731_ = lean_unsigned_to_nat(0u);
v___x_1732_ = lean_array_get_size(v_log_1730_);
v___x_1733_ = lean_nat_dec_lt(v___x_1731_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_dec_ref(v_log_1730_);
v_a_1714_ = v_a_1704_;
goto v___jp_1713_;
}
else
{
lean_object* v___x_1734_; uint8_t v___x_1735_; 
v___x_1734_ = lean_box(0);
v___x_1735_ = lean_nat_dec_le(v___x_1732_, v___x_1732_);
if (v___x_1735_ == 0)
{
if (v___x_1733_ == 0)
{
lean_dec_ref(v_log_1730_);
v_a_1714_ = v_a_1704_;
goto v___jp_1713_;
}
else
{
size_t v___x_1736_; size_t v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = ((size_t)0ULL);
v___x_1737_ = lean_usize_of_nat(v___x_1732_);
v___x_1738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1730_, v___x_1736_, v___x_1737_, v___x_1734_, v_a_1704_);
lean_dec_ref(v_log_1730_);
v___y_1719_ = v___x_1738_;
goto v___jp_1718_;
}
}
else
{
size_t v___x_1739_; size_t v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = ((size_t)0ULL);
v___x_1740_ = lean_usize_of_nat(v___x_1732_);
v___x_1741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1730_, v___x_1739_, v___x_1740_, v___x_1734_, v_a_1704_);
lean_dec_ref(v_log_1730_);
v___y_1719_ = v___x_1741_;
goto v___jp_1718_;
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
v___jp_1718_:
{
if (lean_obj_tag(v___y_1719_) == 0)
{
lean_object* v_a_1720_; 
v_a_1720_ = lean_ctor_get(v___y_1719_, 1);
lean_inc(v_a_1720_);
lean_dec_ref(v___y_1719_);
v_a_1714_ = v_a_1720_;
goto v___jp_1713_;
}
else
{
lean_object* v_a_1721_; lean_object* v_a_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1729_; 
lean_del_object(v___x_1711_);
lean_dec(v_a_1708_);
v_a_1721_ = lean_ctor_get(v___y_1719_, 0);
v_a_1722_ = lean_ctor_get(v___y_1719_, 1);
v_isSharedCheck_1729_ = !lean_is_exclusive(v___y_1719_);
if (v_isSharedCheck_1729_ == 0)
{
v___x_1724_ = v___y_1719_;
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_a_1722_);
lean_inc(v_a_1721_);
lean_dec(v___y_1719_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1729_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v___x_1727_; 
if (v_isShared_1725_ == 0)
{
v___x_1727_ = v___x_1724_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_a_1721_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_a_1722_);
v___x_1727_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
return v___x_1727_;
}
}
}
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v_a_1744_; lean_object* v___x_1746_; uint8_t v_isShared_1747_; uint8_t v_isSharedCheck_1777_; 
v_a_1743_ = lean_ctor_get(v___x_1707_, 0);
v_a_1744_ = lean_ctor_get(v___x_1707_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1746_ = v___x_1707_;
v_isShared_1747_ = v_isSharedCheck_1777_;
goto v_resetjp_1745_;
}
else
{
lean_inc(v_a_1744_);
lean_inc(v_a_1743_);
lean_dec(v___x_1707_);
v___x_1746_ = lean_box(0);
v_isShared_1747_ = v_isSharedCheck_1777_;
goto v_resetjp_1745_;
}
v_resetjp_1745_:
{
lean_object* v_a_1749_; lean_object* v___y_1754_; lean_object* v_log_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v_log_1765_ = lean_ctor_get(v_a_1744_, 0);
lean_inc_ref(v_log_1765_);
lean_dec(v_a_1744_);
v___x_1766_ = lean_unsigned_to_nat(0u);
v___x_1767_ = lean_array_get_size(v_log_1765_);
v___x_1768_ = lean_nat_dec_lt(v___x_1766_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_dec_ref(v_log_1765_);
v_a_1749_ = v_a_1704_;
goto v___jp_1748_;
}
else
{
lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1769_ = lean_box(0);
v___x_1770_ = lean_nat_dec_le(v___x_1767_, v___x_1767_);
if (v___x_1770_ == 0)
{
if (v___x_1768_ == 0)
{
lean_dec_ref(v_log_1765_);
v_a_1749_ = v_a_1704_;
goto v___jp_1748_;
}
else
{
size_t v___x_1771_; size_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = lean_usize_of_nat(v___x_1767_);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1765_, v___x_1771_, v___x_1772_, v___x_1769_, v_a_1704_);
lean_dec_ref(v_log_1765_);
v___y_1754_ = v___x_1773_;
goto v___jp_1753_;
}
}
else
{
size_t v___x_1774_; size_t v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = ((size_t)0ULL);
v___x_1775_ = lean_usize_of_nat(v___x_1767_);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_await_spec__0(v_log_1765_, v___x_1774_, v___x_1775_, v___x_1769_, v_a_1704_);
lean_dec_ref(v_log_1765_);
v___y_1754_ = v___x_1776_;
goto v___jp_1753_;
}
}
v___jp_1748_:
{
lean_object* v___x_1751_; 
if (v_isShared_1747_ == 0)
{
lean_ctor_set(v___x_1746_, 1, v_a_1749_);
v___x_1751_ = v___x_1746_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1743_);
lean_ctor_set(v_reuseFailAlloc_1752_, 1, v_a_1749_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
v___jp_1753_:
{
if (lean_obj_tag(v___y_1754_) == 0)
{
lean_object* v_a_1755_; 
v_a_1755_ = lean_ctor_get(v___y_1754_, 1);
lean_inc(v_a_1755_);
lean_dec_ref(v___y_1754_);
v_a_1749_ = v_a_1755_;
goto v___jp_1748_;
}
else
{
lean_object* v_a_1756_; lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_del_object(v___x_1746_);
lean_dec(v_a_1743_);
v_a_1756_ = lean_ctor_get(v___y_1754_, 0);
v_a_1757_ = lean_ctor_get(v___y_1754_, 1);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___y_1754_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___y_1754_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_inc(v_a_1756_);
lean_dec(v___y_1754_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___redArg___boxed(lean_object* v_self_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_Lake_Job_await___redArg(v_self_1778_, v_a_1779_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await(lean_object* v_00_u03b1_1782_, lean_object* v_self_1783_, lean_object* v_a_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lake_Job_await___redArg(v_self_1783_, v_a_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_await___boxed(lean_object* v_00_u03b1_1787_, lean_object* v_self_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lake_Job_await(v_00_u03b1_1787_, v_self_1788_, v_a_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1(lean_object* v_a_1792_, lean_object* v_f_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v_a_1802_; lean_object* v_a_1803_; 
if (lean_obj_tag(v_x_1799_) == 0)
{
lean_object* v_a_1805_; lean_object* v_a_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v_log_1813_; uint8_t v_action_1814_; uint8_t v_wantsRebuild_1815_; lean_object* v_trace_1816_; lean_object* v_buildTime_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1878_; 
v_a_1805_ = lean_ctor_get(v_x_1799_, 0);
lean_inc(v_a_1805_);
v_a_1806_ = lean_ctor_get(v_x_1799_, 1);
lean_inc(v_a_1806_);
lean_dec_ref(v_x_1799_);
v___x_1807_ = lean_unsigned_to_nat(0u);
v___x_1808_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_1809_ = lean_st_mk_ref(v___x_1808_);
lean_inc(v___x_1809_);
v___x_1810_ = l_IO_FS_Stream_ofBuffer(v___x_1809_);
lean_inc_ref(v___x_1810_);
v___x_1811_ = lean_get_set_stdout(v___x_1810_);
v___x_1812_ = lean_get_set_stderr(v___x_1810_);
v_log_1813_ = lean_ctor_get(v_a_1806_, 0);
v_action_1814_ = lean_ctor_get_uint8(v_a_1806_, sizeof(void*)*3);
v_wantsRebuild_1815_ = lean_ctor_get_uint8(v_a_1806_, sizeof(void*)*3 + 1);
v_trace_1816_ = lean_ctor_get(v_a_1806_, 1);
v_buildTime_1817_ = lean_ctor_get(v_a_1806_, 2);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_a_1806_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1819_ = v_a_1806_;
v_isShared_1820_ = v_isSharedCheck_1878_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_buildTime_1817_);
lean_inc(v_trace_1816_);
lean_inc(v_log_1813_);
lean_dec(v_a_1806_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1878_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_trace_1821_; lean_object* v___x_1823_; 
lean_inc_ref(v_a_1792_);
v_trace_1821_ = l_Lake_BuildTrace_mix(v_a_1792_, v_trace_1816_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 1, v_trace_1821_);
v___x_1823_ = v___x_1819_;
goto v_reusejp_1822_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_log_1813_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v_trace_1821_);
lean_ctor_set(v_reuseFailAlloc_1877_, 2, v_buildTime_1817_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, sizeof(void*)*3, v_action_1814_);
lean_ctor_set_uint8(v_reuseFailAlloc_1877_, sizeof(void*)*3 + 1, v_wantsRebuild_1815_);
v___x_1823_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1822_;
}
v_reusejp_1822_:
{
lean_object* v___x_1824_; 
lean_inc_ref(v_a_1798_);
lean_inc(v_a_1797_);
lean_inc(v_a_1796_);
lean_inc(v_a_1795_);
v___x_1824_ = lean_apply_8(v_f_1793_, v_a_1805_, v_a_1794_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v___x_1823_, lean_box(0));
if (lean_obj_tag(v___x_1824_) == 0)
{
lean_object* v_a_1825_; lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1871_; 
v_a_1825_ = lean_ctor_get(v___x_1824_, 0);
v_a_1826_ = lean_ctor_get(v___x_1824_, 1);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1828_ = v___x_1824_;
v_isShared_1829_ = v_isSharedCheck_1871_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_inc(v_a_1825_);
lean_dec(v___x_1824_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1871_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___y_1831_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_a_1837_; lean_object* v___x_1838_; lean_object* v_log_1839_; uint8_t v_action_1840_; uint8_t v_wantsRebuild_1841_; lean_object* v_trace_1842_; lean_object* v_buildTime_1843_; lean_object* v___y_1845_; lean_object* v_data_1866_; uint8_t v___x_1867_; 
lean_inc(v_a_1825_);
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_a_1825_);
v___x_1836_ = l_Lake_Job_sync___redArg___lam__0(v___x_1811_, v___x_1812_, v___x_1835_, v_a_1826_);
lean_dec_ref(v___x_1835_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 1);
lean_inc(v_a_1837_);
lean_dec_ref(v___x_1836_);
v___x_1838_ = lean_st_ref_get(v___x_1809_);
lean_dec(v___x_1809_);
v_log_1839_ = lean_ctor_get(v_a_1837_, 0);
v_action_1840_ = lean_ctor_get_uint8(v_a_1837_, sizeof(void*)*3);
v_wantsRebuild_1841_ = lean_ctor_get_uint8(v_a_1837_, sizeof(void*)*3 + 1);
v_trace_1842_ = lean_ctor_get(v_a_1837_, 1);
v_buildTime_1843_ = lean_ctor_get(v_a_1837_, 2);
v_data_1866_ = lean_ctor_get(v___x_1838_, 0);
lean_inc_ref(v_data_1866_);
lean_dec(v___x_1838_);
v___x_1867_ = lean_string_validate_utf8(v_data_1866_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
lean_dec_ref(v_data_1866_);
v___x_1868_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_1869_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_1868_);
v___y_1845_ = v___x_1869_;
goto v___jp_1844_;
}
else
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_string_from_utf8_unchecked(v_data_1866_);
v___y_1845_ = v___x_1870_;
goto v___jp_1844_;
}
v___jp_1830_:
{
lean_object* v___x_1833_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v___y_1831_);
v___x_1833_ = v___x_1828_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1825_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___y_1831_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
}
}
v___jp_1844_:
{
lean_object* v___x_1846_; uint8_t v___x_1847_; 
v___x_1846_ = lean_string_utf8_byte_size(v___y_1845_);
v___x_1847_ = lean_nat_dec_eq(v___x_1846_, v___x_1807_);
if (v___x_1847_ == 0)
{
lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1862_; 
lean_inc(v_buildTime_1843_);
lean_inc_ref(v_trace_1842_);
lean_inc_ref(v_log_1839_);
v_isSharedCheck_1862_ = !lean_is_exclusive(v_a_1837_);
if (v_isSharedCheck_1862_ == 0)
{
lean_object* v_unused_1863_; lean_object* v_unused_1864_; lean_object* v_unused_1865_; 
v_unused_1863_ = lean_ctor_get(v_a_1837_, 2);
lean_dec(v_unused_1863_);
v_unused_1864_ = lean_ctor_get(v_a_1837_, 1);
lean_dec(v_unused_1864_);
v_unused_1865_ = lean_ctor_get(v_a_1837_, 0);
lean_dec(v_unused_1865_);
v___x_1849_ = v_a_1837_;
v_isShared_1850_ = v_isSharedCheck_1862_;
goto v_resetjp_1848_;
}
else
{
lean_dec(v_a_1837_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1862_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1860_; 
v___x_1851_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_1852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1852_, 0, v___y_1845_);
lean_ctor_set(v___x_1852_, 1, v___x_1807_);
lean_ctor_set(v___x_1852_, 2, v___x_1846_);
v___x_1853_ = l_String_Slice_trimAscii(v___x_1852_);
v___x_1854_ = l_String_Slice_toString(v___x_1853_);
lean_dec_ref(v___x_1853_);
v___x_1855_ = lean_string_append(v___x_1851_, v___x_1854_);
lean_dec_ref(v___x_1854_);
v___x_1856_ = 1;
v___x_1857_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set_uint8(v___x_1857_, sizeof(void*)*1, v___x_1856_);
v___x_1858_ = lean_array_push(v_log_1839_, v___x_1857_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v___x_1858_);
v___x_1860_ = v___x_1849_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1861_, 1, v_trace_1842_);
lean_ctor_set(v_reuseFailAlloc_1861_, 2, v_buildTime_1843_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*3, v_action_1840_);
lean_ctor_set_uint8(v_reuseFailAlloc_1861_, sizeof(void*)*3 + 1, v_wantsRebuild_1841_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
v___y_1831_ = v___x_1860_;
goto v___jp_1830_;
}
}
}
else
{
lean_dec_ref(v___y_1845_);
v___y_1831_ = v_a_1837_;
goto v___jp_1830_;
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v_a_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v_a_1876_; 
lean_dec(v___x_1809_);
v_a_1872_ = lean_ctor_get(v___x_1824_, 0);
lean_inc(v_a_1872_);
v_a_1873_ = lean_ctor_get(v___x_1824_, 1);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1824_);
v___x_1874_ = lean_box(0);
v___x_1875_ = l_Lake_Job_sync___redArg___lam__0(v___x_1811_, v___x_1812_, v___x_1874_, v_a_1873_);
v_a_1876_ = lean_ctor_get(v___x_1875_, 1);
lean_inc(v_a_1876_);
lean_dec_ref(v___x_1875_);
v_a_1802_ = v_a_1872_;
v_a_1803_ = v_a_1876_;
goto v___jp_1801_;
}
}
}
}
else
{
lean_object* v_a_1879_; lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec_ref(v_a_1794_);
lean_dec_ref(v_f_1793_);
v_a_1879_ = lean_ctor_get(v_x_1799_, 0);
v_a_1880_ = lean_ctor_get(v_x_1799_, 1);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_x_1799_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v_x_1799_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_inc(v_a_1879_);
lean_dec(v_x_1799_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1879_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
v___jp_1801_:
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1804_, 0, v_a_1802_);
lean_ctor_set(v___x_1804_, 1, v_a_1803_);
return v___x_1804_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___lam__1___boxed(lean_object* v_a_1888_, lean_object* v_f_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_x_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lake_Job_mapM___redArg___lam__1(v_a_1888_, v_f_1889_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_, v_x_1895_);
lean_dec_ref(v_a_1894_);
lean_dec(v_a_1893_);
lean_dec(v_a_1892_);
lean_dec(v_a_1891_);
lean_dec_ref(v_a_1888_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg(lean_object* v_kind_1898_, lean_object* v_self_1899_, lean_object* v_f_1900_, lean_object* v_prio_1901_, uint8_t v_sync_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_, lean_object* v_a_1907_, lean_object* v_a_1908_){
_start:
{
lean_object* v_task_1910_; lean_object* v_caption_1911_; uint8_t v_optional_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1921_; 
v_task_1910_ = lean_ctor_get(v_self_1899_, 0);
v_caption_1911_ = lean_ctor_get(v_self_1899_, 2);
v_optional_1912_ = lean_ctor_get_uint8(v_self_1899_, sizeof(void*)*3);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_self_1899_);
if (v_isSharedCheck_1921_ == 0)
{
lean_object* v_unused_1922_; 
v_unused_1922_ = lean_ctor_get(v_self_1899_, 1);
lean_dec(v_unused_1922_);
v___x_1914_ = v_self_1899_;
v_isShared_1915_ = v_isSharedCheck_1921_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_caption_1911_);
lean_inc(v_task_1910_);
lean_dec(v_self_1899_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1921_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1919_; 
lean_inc_ref(v_a_1907_);
lean_inc(v_a_1906_);
lean_inc(v_a_1905_);
lean_inc(v_a_1904_);
lean_inc_ref(v_a_1908_);
v___f_1916_ = lean_alloc_closure((void*)(l_Lake_Job_mapM___redArg___lam__1___boxed), 9, 7);
lean_closure_set(v___f_1916_, 0, v_a_1908_);
lean_closure_set(v___f_1916_, 1, v_f_1900_);
lean_closure_set(v___f_1916_, 2, v_a_1903_);
lean_closure_set(v___f_1916_, 3, v_a_1904_);
lean_closure_set(v___f_1916_, 4, v_a_1905_);
lean_closure_set(v___f_1916_, 5, v_a_1906_);
lean_closure_set(v___f_1916_, 6, v_a_1907_);
v___x_1917_ = lean_io_map_task(v___f_1916_, v_task_1910_, v_prio_1901_, v_sync_1902_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 1, v_kind_1898_);
lean_ctor_set(v___x_1914_, 0, v___x_1917_);
v___x_1919_ = v___x_1914_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v___x_1917_);
lean_ctor_set(v_reuseFailAlloc_1920_, 1, v_kind_1898_);
lean_ctor_set(v_reuseFailAlloc_1920_, 2, v_caption_1911_);
lean_ctor_set_uint8(v_reuseFailAlloc_1920_, sizeof(void*)*3, v_optional_1912_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___redArg___boxed(lean_object* v_kind_1923_, lean_object* v_self_1924_, lean_object* v_f_1925_, lean_object* v_prio_1926_, lean_object* v_sync_1927_, lean_object* v_a_1928_, lean_object* v_a_1929_, lean_object* v_a_1930_, lean_object* v_a_1931_, lean_object* v_a_1932_, lean_object* v_a_1933_, lean_object* v_a_1934_){
_start:
{
uint8_t v_sync_boxed_1935_; lean_object* v_res_1936_; 
v_sync_boxed_1935_ = lean_unbox(v_sync_1927_);
v_res_1936_ = l_Lake_Job_mapM___redArg(v_kind_1923_, v_self_1924_, v_f_1925_, v_prio_1926_, v_sync_boxed_1935_, v_a_1928_, v_a_1929_, v_a_1930_, v_a_1931_, v_a_1932_, v_a_1933_);
lean_dec_ref(v_a_1933_);
lean_dec_ref(v_a_1932_);
lean_dec(v_a_1931_);
lean_dec(v_a_1930_);
lean_dec(v_a_1929_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM(lean_object* v_00_u03b2_1937_, lean_object* v_00_u03b1_1938_, lean_object* v_kind_1939_, lean_object* v_self_1940_, lean_object* v_f_1941_, lean_object* v_prio_1942_, uint8_t v_sync_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lake_Job_mapM___redArg(v_kind_1939_, v_self_1940_, v_f_1941_, v_prio_1942_, v_sync_1943_, v_a_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_, v_a_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mapM___boxed(lean_object* v_00_u03b2_1952_, lean_object* v_00_u03b1_1953_, lean_object* v_kind_1954_, lean_object* v_self_1955_, lean_object* v_f_1956_, lean_object* v_prio_1957_, lean_object* v_sync_1958_, lean_object* v_a_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_){
_start:
{
uint8_t v_sync_boxed_1966_; lean_object* v_res_1967_; 
v_sync_boxed_1966_ = lean_unbox(v_sync_1958_);
v_res_1967_ = l_Lake_Job_mapM(v_00_u03b2_1952_, v_00_u03b1_1953_, v_kind_1954_, v_self_1955_, v_f_1956_, v_prio_1957_, v_sync_boxed_1966_, v_a_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_, v_a_1964_);
lean_dec_ref(v_a_1964_);
lean_dec_ref(v_a_1963_);
lean_dec(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec(v_a_1960_);
return v_res_1967_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0(lean_object* v_val_1968_, lean_object* v_val_1969_, lean_object* v_a_x3f_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1973_ = lean_get_set_stdout(v_val_1968_);
lean_dec_ref(v___x_1973_);
v___x_1974_ = lean_get_set_stderr(v_val_1969_);
lean_dec_ref(v___x_1974_);
v___x_1975_ = lean_box(0);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v___y_1971_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__0___boxed(lean_object* v_val_1977_, lean_object* v_val_1978_, lean_object* v_a_x3f_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Lake_Job_bindM___redArg___lam__0(v_val_1977_, v_val_1978_, v_a_x3f_1979_, v___y_1980_);
lean_dec(v_a_x3f_1979_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__1(lean_object* v_a_1983_, lean_object* v_x_1984_){
_start:
{
if (lean_obj_tag(v_x_1984_) == 0)
{
lean_object* v_a_1985_; lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2008_; 
v_a_1985_ = lean_ctor_get(v_x_1984_, 0);
v_a_1986_ = lean_ctor_get(v_x_1984_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_x_1984_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1988_ = v_x_1984_;
v_isShared_1989_ = v_isSharedCheck_2008_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_inc(v_a_1985_);
lean_dec(v_x_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2008_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1990_; lean_object* v_log_1991_; uint8_t v_action_1992_; uint8_t v_wantsRebuild_1993_; lean_object* v_buildTime_1994_; lean_object* v_trace_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2005_; 
lean_inc(v_a_1986_);
v___x_1990_ = l_Lake_JobState_merge(v_a_1983_, v_a_1986_);
v_log_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_ref(v_log_1991_);
v_action_1992_ = lean_ctor_get_uint8(v___x_1990_, sizeof(void*)*3);
v_wantsRebuild_1993_ = lean_ctor_get_uint8(v___x_1990_, sizeof(void*)*3 + 1);
v_buildTime_1994_ = lean_ctor_get(v___x_1990_, 2);
lean_inc(v_buildTime_1994_);
lean_dec_ref(v___x_1990_);
v_trace_1995_ = lean_ctor_get(v_a_1986_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_a_1986_);
if (v_isSharedCheck_2005_ == 0)
{
lean_object* v_unused_2006_; lean_object* v_unused_2007_; 
v_unused_2006_ = lean_ctor_get(v_a_1986_, 2);
lean_dec(v_unused_2006_);
v_unused_2007_ = lean_ctor_get(v_a_1986_, 0);
lean_dec(v_unused_2007_);
v___x_1997_ = v_a_1986_;
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_trace_1995_);
lean_dec(v_a_1986_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2005_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 2, v_buildTime_1994_);
lean_ctor_set(v___x_1997_, 0, v_log_1991_);
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_log_1991_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v_trace_1995_);
lean_ctor_set(v_reuseFailAlloc_2004_, 2, v_buildTime_1994_);
v___x_2000_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
lean_object* v___x_2002_; 
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*3, v_action_1992_);
lean_ctor_set_uint8(v___x_2000_, sizeof(void*)*3 + 1, v_wantsRebuild_1993_);
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 1, v___x_2000_);
v___x_2002_ = v___x_1988_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1985_);
lean_ctor_set(v_reuseFailAlloc_2003_, 1, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2035_; 
v_a_2009_ = lean_ctor_get(v_x_1984_, 0);
v_a_2010_ = lean_ctor_get(v_x_1984_, 1);
v_isSharedCheck_2035_ = !lean_is_exclusive(v_x_1984_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2012_ = v_x_1984_;
v_isShared_2013_ = v_isSharedCheck_2035_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_inc(v_a_2009_);
lean_dec(v_x_1984_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2035_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_log_2014_; lean_object* v___x_2015_; lean_object* v_log_2016_; uint8_t v_action_2017_; uint8_t v_wantsRebuild_2018_; lean_object* v_buildTime_2019_; lean_object* v_trace_2020_; lean_object* v___x_2022_; uint8_t v_isShared_2023_; uint8_t v_isSharedCheck_2032_; 
v_log_2014_ = lean_ctor_get(v_a_1983_, 0);
lean_inc_ref(v_log_2014_);
lean_inc(v_a_2010_);
v___x_2015_ = l_Lake_JobState_merge(v_a_1983_, v_a_2010_);
v_log_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc_ref(v_log_2016_);
v_action_2017_ = lean_ctor_get_uint8(v___x_2015_, sizeof(void*)*3);
v_wantsRebuild_2018_ = lean_ctor_get_uint8(v___x_2015_, sizeof(void*)*3 + 1);
v_buildTime_2019_ = lean_ctor_get(v___x_2015_, 2);
lean_inc(v_buildTime_2019_);
lean_dec_ref(v___x_2015_);
v_trace_2020_ = lean_ctor_get(v_a_2010_, 1);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_a_2010_);
if (v_isSharedCheck_2032_ == 0)
{
lean_object* v_unused_2033_; lean_object* v_unused_2034_; 
v_unused_2033_ = lean_ctor_get(v_a_2010_, 2);
lean_dec(v_unused_2033_);
v_unused_2034_ = lean_ctor_get(v_a_2010_, 0);
lean_dec(v_unused_2034_);
v___x_2022_ = v_a_2010_;
v_isShared_2023_ = v_isSharedCheck_2032_;
goto v_resetjp_2021_;
}
else
{
lean_inc(v_trace_2020_);
lean_dec(v_a_2010_);
v___x_2022_ = lean_box(0);
v_isShared_2023_ = v_isSharedCheck_2032_;
goto v_resetjp_2021_;
}
v_resetjp_2021_:
{
lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
v___x_2024_ = lean_array_get_size(v_log_2014_);
lean_dec_ref(v_log_2014_);
v___x_2025_ = lean_nat_add(v___x_2024_, v_a_2009_);
lean_dec(v_a_2009_);
if (v_isShared_2023_ == 0)
{
lean_ctor_set(v___x_2022_, 2, v_buildTime_2019_);
lean_ctor_set(v___x_2022_, 0, v_log_2016_);
v___x_2027_ = v___x_2022_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_log_2016_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_trace_2020_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_buildTime_2019_);
v___x_2027_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2029_; 
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*3, v_action_2017_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*3 + 1, v_wantsRebuild_2018_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v___x_2027_);
lean_ctor_set(v___x_2012_, 0, v___x_2025_);
v___x_2029_ = v___x_2012_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2027_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2(lean_object* v_a_2036_, lean_object* v_____r_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v___x_2045_; 
v___x_2045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2045_, 0, v_a_2036_);
lean_ctor_set(v___x_2045_, 1, v___y_2043_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__2___boxed(lean_object* v_a_2046_, lean_object* v_____r_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2046_, v_____r_2047_, v___y_2048_, v___y_2049_, v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
lean_dec_ref(v___y_2052_);
lean_dec(v___y_2051_);
lean_dec(v___y_2050_);
lean_dec(v___y_2049_);
lean_dec_ref(v___y_2048_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3(lean_object* v_a_2056_, lean_object* v_f_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_prio_2063_, lean_object* v_x_2064_){
_start:
{
lean_object* v_a_2067_; lean_object* v_a_2068_; lean_object* v___y_2072_; 
if (lean_obj_tag(v_x_2064_) == 0)
{
lean_object* v_a_2081_; lean_object* v_a_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v_log_2089_; uint8_t v_action_2090_; uint8_t v_wantsRebuild_2091_; lean_object* v_trace_2092_; lean_object* v_buildTime_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2149_; 
v_a_2081_ = lean_ctor_get(v_x_2064_, 0);
lean_inc(v_a_2081_);
v_a_2082_ = lean_ctor_get(v_x_2064_, 1);
lean_inc(v_a_2082_);
lean_dec_ref(v_x_2064_);
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__0, &l_Lake_Job_sync___redArg___closed__0_once, _init_l_Lake_Job_sync___redArg___closed__0);
v___x_2085_ = lean_st_mk_ref(v___x_2084_);
lean_inc(v___x_2085_);
v___x_2086_ = l_IO_FS_Stream_ofBuffer(v___x_2085_);
lean_inc_ref(v___x_2086_);
v___x_2087_ = lean_get_set_stdout(v___x_2086_);
v___x_2088_ = lean_get_set_stderr(v___x_2086_);
v_log_2089_ = lean_ctor_get(v_a_2082_, 0);
v_action_2090_ = lean_ctor_get_uint8(v_a_2082_, sizeof(void*)*3);
v_wantsRebuild_2091_ = lean_ctor_get_uint8(v_a_2082_, sizeof(void*)*3 + 1);
v_trace_2092_ = lean_ctor_get(v_a_2082_, 1);
v_buildTime_2093_ = lean_ctor_get(v_a_2082_, 2);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_a_2082_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2095_ = v_a_2082_;
v_isShared_2096_ = v_isSharedCheck_2149_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_buildTime_2093_);
lean_inc(v_trace_2092_);
lean_inc(v_log_2089_);
lean_dec(v_a_2082_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2149_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v_trace_2097_; lean_object* v___x_2099_; 
lean_inc_ref(v_a_2056_);
v_trace_2097_ = l_Lake_BuildTrace_mix(v_a_2056_, v_trace_2092_);
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 1, v_trace_2097_);
v___x_2099_ = v___x_2095_;
goto v_reusejp_2098_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_log_2089_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v_trace_2097_);
lean_ctor_set(v_reuseFailAlloc_2148_, 2, v_buildTime_2093_);
lean_ctor_set_uint8(v_reuseFailAlloc_2148_, sizeof(void*)*3, v_action_2090_);
lean_ctor_set_uint8(v_reuseFailAlloc_2148_, sizeof(void*)*3 + 1, v_wantsRebuild_2091_);
v___x_2099_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2098_;
}
v_reusejp_2098_:
{
lean_object* v___x_2100_; 
lean_inc_ref(v_a_2062_);
lean_inc(v_a_2061_);
lean_inc(v_a_2060_);
lean_inc(v_a_2059_);
lean_inc_ref(v_a_2058_);
v___x_2100_ = lean_apply_8(v_f_2057_, v_a_2081_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v___x_2099_, lean_box(0));
if (lean_obj_tag(v___x_2100_) == 0)
{
lean_object* v_a_2101_; lean_object* v_a_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v_a_2105_; lean_object* v___x_2106_; lean_object* v_log_2107_; uint8_t v_action_2108_; uint8_t v_wantsRebuild_2109_; lean_object* v_trace_2110_; lean_object* v_buildTime_2111_; lean_object* v_data_2112_; lean_object* v___y_2114_; uint8_t v___x_2139_; 
v_a_2101_ = lean_ctor_get(v___x_2100_, 0);
lean_inc_n(v_a_2101_, 2);
v_a_2102_ = lean_ctor_get(v___x_2100_, 1);
lean_inc(v_a_2102_);
lean_dec_ref(v___x_2100_);
v___x_2103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2103_, 0, v_a_2101_);
v___x_2104_ = l_Lake_Job_bindM___redArg___lam__0(v___x_2087_, v___x_2088_, v___x_2103_, v_a_2102_);
lean_dec_ref(v___x_2103_);
v_a_2105_ = lean_ctor_get(v___x_2104_, 1);
lean_inc(v_a_2105_);
lean_dec_ref(v___x_2104_);
v___x_2106_ = lean_st_ref_get(v___x_2085_);
lean_dec(v___x_2085_);
v_log_2107_ = lean_ctor_get(v_a_2105_, 0);
v_action_2108_ = lean_ctor_get_uint8(v_a_2105_, sizeof(void*)*3);
v_wantsRebuild_2109_ = lean_ctor_get_uint8(v_a_2105_, sizeof(void*)*3 + 1);
v_trace_2110_ = lean_ctor_get(v_a_2105_, 1);
v_buildTime_2111_ = lean_ctor_get(v_a_2105_, 2);
v_data_2112_ = lean_ctor_get(v___x_2106_, 0);
lean_inc_ref(v_data_2112_);
lean_dec(v___x_2106_);
v___x_2139_ = lean_string_validate_utf8(v_data_2112_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; lean_object* v___x_2141_; 
lean_dec_ref(v_data_2112_);
v___x_2140_ = lean_obj_once(&l_Lake_Job_sync___redArg___closed__7, &l_Lake_Job_sync___redArg___closed__7_once, _init_l_Lake_Job_sync___redArg___closed__7);
v___x_2141_ = l_panic___at___00Lake_Job_sync_spec__0(v___x_2140_);
v___y_2114_ = v___x_2141_;
goto v___jp_2113_;
}
else
{
lean_object* v___x_2142_; 
v___x_2142_ = lean_string_from_utf8_unchecked(v_data_2112_);
v___y_2114_ = v___x_2142_;
goto v___jp_2113_;
}
v___jp_2113_:
{
lean_object* v___x_2115_; uint8_t v___x_2116_; 
v___x_2115_ = lean_string_utf8_byte_size(v___y_2114_);
v___x_2116_ = lean_nat_dec_eq(v___x_2115_, v___x_2083_);
if (v___x_2116_ == 0)
{
lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2133_; 
lean_inc(v_buildTime_2111_);
lean_inc_ref(v_trace_2110_);
lean_inc_ref(v_log_2107_);
v_isSharedCheck_2133_ = !lean_is_exclusive(v_a_2105_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; lean_object* v_unused_2135_; lean_object* v_unused_2136_; 
v_unused_2134_ = lean_ctor_get(v_a_2105_, 2);
lean_dec(v_unused_2134_);
v_unused_2135_ = lean_ctor_get(v_a_2105_, 1);
lean_dec(v_unused_2135_);
v_unused_2136_ = lean_ctor_get(v_a_2105_, 0);
lean_dec(v_unused_2136_);
v___x_2118_ = v_a_2105_;
v_isShared_2119_ = v_isSharedCheck_2133_;
goto v_resetjp_2117_;
}
else
{
lean_dec(v_a_2105_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2133_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; uint8_t v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2120_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__3));
v___x_2121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2121_, 0, v___y_2114_);
lean_ctor_set(v___x_2121_, 1, v___x_2083_);
lean_ctor_set(v___x_2121_, 2, v___x_2115_);
v___x_2122_ = l_String_Slice_trimAscii(v___x_2121_);
v___x_2123_ = l_String_Slice_toString(v___x_2122_);
lean_dec_ref(v___x_2122_);
v___x_2124_ = lean_string_append(v___x_2120_, v___x_2123_);
lean_dec_ref(v___x_2123_);
v___x_2125_ = 1;
v___x_2126_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set_uint8(v___x_2126_, sizeof(void*)*1, v___x_2125_);
v___x_2127_ = lean_box(0);
v___x_2128_ = lean_array_push(v_log_2107_, v___x_2126_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 0, v___x_2128_);
v___x_2130_ = v___x_2118_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_trace_2110_);
lean_ctor_set(v_reuseFailAlloc_2132_, 2, v_buildTime_2111_);
lean_ctor_set_uint8(v_reuseFailAlloc_2132_, sizeof(void*)*3, v_action_2108_);
lean_ctor_set_uint8(v_reuseFailAlloc_2132_, sizeof(void*)*3 + 1, v_wantsRebuild_2109_);
v___x_2130_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2101_, v___x_2127_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v___x_2130_);
lean_dec_ref(v_a_2058_);
v___y_2072_ = v___x_2131_;
goto v___jp_2071_;
}
}
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec_ref(v___y_2114_);
v___x_2137_ = lean_box(0);
v___x_2138_ = l_Lake_Job_bindM___redArg___lam__2(v_a_2101_, v___x_2137_, v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_, v_a_2062_, v_a_2105_);
lean_dec_ref(v_a_2058_);
v___y_2072_ = v___x_2138_;
goto v___jp_2071_;
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v_a_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v_a_2147_; 
lean_dec(v___x_2085_);
lean_dec(v_prio_2063_);
lean_dec_ref(v_a_2058_);
v_a_2143_ = lean_ctor_get(v___x_2100_, 0);
lean_inc(v_a_2143_);
v_a_2144_ = lean_ctor_get(v___x_2100_, 1);
lean_inc(v_a_2144_);
lean_dec_ref(v___x_2100_);
v___x_2145_ = lean_box(0);
v___x_2146_ = l_Lake_Job_bindM___redArg___lam__0(v___x_2087_, v___x_2088_, v___x_2145_, v_a_2144_);
v_a_2147_ = lean_ctor_get(v___x_2146_, 1);
lean_inc(v_a_2147_);
lean_dec_ref(v___x_2146_);
v_a_2067_ = v_a_2143_;
v_a_2068_ = v_a_2147_;
goto v___jp_2066_;
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2159_; 
lean_dec(v_prio_2063_);
lean_dec_ref(v_a_2058_);
lean_dec_ref(v_f_2057_);
v_a_2150_ = lean_ctor_get(v_x_2064_, 0);
v_a_2151_ = lean_ctor_get(v_x_2064_, 1);
v_isSharedCheck_2159_ = !lean_is_exclusive(v_x_2064_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2153_ = v_x_2064_;
v_isShared_2154_ = v_isSharedCheck_2159_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_inc(v_a_2150_);
lean_dec(v_x_2064_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2159_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2150_);
lean_ctor_set(v_reuseFailAlloc_2158_, 1, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_task_pure(v___x_2156_);
return v___x_2157_;
}
}
}
v___jp_2066_:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_a_2067_);
lean_ctor_set(v___x_2069_, 1, v_a_2068_);
v___x_2070_ = lean_task_pure(v___x_2069_);
return v___x_2070_;
}
v___jp_2071_:
{
if (lean_obj_tag(v___y_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v_a_2074_; lean_object* v_task_2075_; lean_object* v___f_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; 
v_a_2073_ = lean_ctor_get(v___y_2072_, 0);
lean_inc(v_a_2073_);
v_a_2074_ = lean_ctor_get(v___y_2072_, 1);
lean_inc(v_a_2074_);
lean_dec_ref(v___y_2072_);
v_task_2075_ = lean_ctor_get(v_a_2073_, 0);
lean_inc_ref(v_task_2075_);
lean_dec(v_a_2073_);
v___f_2076_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_2076_, 0, v_a_2074_);
v___x_2077_ = 1;
v___x_2078_ = lean_task_map(v___f_2076_, v_task_2075_, v_prio_2063_, v___x_2077_);
return v___x_2078_;
}
else
{
lean_object* v_a_2079_; lean_object* v_a_2080_; 
lean_dec(v_prio_2063_);
v_a_2079_ = lean_ctor_get(v___y_2072_, 0);
lean_inc(v_a_2079_);
v_a_2080_ = lean_ctor_get(v___y_2072_, 1);
lean_inc(v_a_2080_);
lean_dec_ref(v___y_2072_);
v_a_2067_ = v_a_2079_;
v_a_2068_ = v_a_2080_;
goto v___jp_2066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___lam__3___boxed(lean_object* v_a_2160_, lean_object* v_f_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_prio_2167_, lean_object* v_x_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l_Lake_Job_bindM___redArg___lam__3(v_a_2160_, v_f_2161_, v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_, v_a_2166_, v_prio_2167_, v_x_2168_);
lean_dec_ref(v_a_2166_);
lean_dec(v_a_2165_);
lean_dec(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2160_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg(lean_object* v_kind_2171_, lean_object* v_self_2172_, lean_object* v_f_2173_, lean_object* v_prio_2174_, uint8_t v_sync_2175_, lean_object* v_a_2176_, lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_task_2183_; lean_object* v_caption_2184_; uint8_t v_optional_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2194_; 
v_task_2183_ = lean_ctor_get(v_self_2172_, 0);
v_caption_2184_ = lean_ctor_get(v_self_2172_, 2);
v_optional_2185_ = lean_ctor_get_uint8(v_self_2172_, sizeof(void*)*3);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_self_2172_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; 
v_unused_2195_ = lean_ctor_get(v_self_2172_, 1);
lean_dec(v_unused_2195_);
v___x_2187_ = v_self_2172_;
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_caption_2184_);
lean_inc(v_task_2183_);
lean_dec(v_self_2172_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2194_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___f_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
lean_inc(v_prio_2174_);
lean_inc_ref(v_a_2180_);
lean_inc(v_a_2179_);
lean_inc(v_a_2178_);
lean_inc(v_a_2177_);
lean_inc_ref(v_a_2181_);
v___f_2189_ = lean_alloc_closure((void*)(l_Lake_Job_bindM___redArg___lam__3___boxed), 10, 8);
lean_closure_set(v___f_2189_, 0, v_a_2181_);
lean_closure_set(v___f_2189_, 1, v_f_2173_);
lean_closure_set(v___f_2189_, 2, v_a_2176_);
lean_closure_set(v___f_2189_, 3, v_a_2177_);
lean_closure_set(v___f_2189_, 4, v_a_2178_);
lean_closure_set(v___f_2189_, 5, v_a_2179_);
lean_closure_set(v___f_2189_, 6, v_a_2180_);
lean_closure_set(v___f_2189_, 7, v_prio_2174_);
v___x_2190_ = lean_io_bind_task(v_task_2183_, v___f_2189_, v_prio_2174_, v_sync_2175_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 1, v_kind_2171_);
lean_ctor_set(v___x_2187_, 0, v___x_2190_);
v___x_2192_ = v___x_2187_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_kind_2171_);
lean_ctor_set(v_reuseFailAlloc_2193_, 2, v_caption_2184_);
lean_ctor_set_uint8(v_reuseFailAlloc_2193_, sizeof(void*)*3, v_optional_2185_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___redArg___boxed(lean_object* v_kind_2196_, lean_object* v_self_2197_, lean_object* v_f_2198_, lean_object* v_prio_2199_, lean_object* v_sync_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_, lean_object* v_a_2204_, lean_object* v_a_2205_, lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
uint8_t v_sync_boxed_2208_; lean_object* v_res_2209_; 
v_sync_boxed_2208_ = lean_unbox(v_sync_2200_);
v_res_2209_ = l_Lake_Job_bindM___redArg(v_kind_2196_, v_self_2197_, v_f_2198_, v_prio_2199_, v_sync_boxed_2208_, v_a_2201_, v_a_2202_, v_a_2203_, v_a_2204_, v_a_2205_, v_a_2206_);
lean_dec_ref(v_a_2206_);
lean_dec_ref(v_a_2205_);
lean_dec(v_a_2204_);
lean_dec(v_a_2203_);
lean_dec(v_a_2202_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM(lean_object* v_00_u03b2_2210_, lean_object* v_00_u03b1_2211_, lean_object* v_kind_2212_, lean_object* v_self_2213_, lean_object* v_f_2214_, lean_object* v_prio_2215_, uint8_t v_sync_2216_, lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lake_Job_bindM___redArg(v_kind_2212_, v_self_2213_, v_f_2214_, v_prio_2215_, v_sync_2216_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_, v_a_2221_, v_a_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_bindM___boxed(lean_object* v_00_u03b2_2225_, lean_object* v_00_u03b1_2226_, lean_object* v_kind_2227_, lean_object* v_self_2228_, lean_object* v_f_2229_, lean_object* v_prio_2230_, lean_object* v_sync_2231_, lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_, lean_object* v_a_2237_, lean_object* v_a_2238_){
_start:
{
uint8_t v_sync_boxed_2239_; lean_object* v_res_2240_; 
v_sync_boxed_2239_ = lean_unbox(v_sync_2231_);
v_res_2240_ = l_Lake_Job_bindM(v_00_u03b2_2225_, v_00_u03b1_2226_, v_kind_2227_, v_self_2228_, v_f_2229_, v_prio_2230_, v_sync_boxed_2239_, v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_, v_a_2237_);
lean_dec_ref(v_a_2237_);
lean_dec_ref(v_a_2236_);
lean_dec(v_a_2235_);
lean_dec(v_a_2234_);
lean_dec(v_a_2233_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__0(lean_object* v_f_2241_, lean_object* v_rx_2242_, lean_object* v_ry_2243_){
_start:
{
lean_object* v___x_2244_; 
v___x_2244_ = lean_apply_2(v_f_2241_, v_rx_2242_, v_ry_2243_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1(lean_object* v_other_2245_, lean_object* v_f_2246_, lean_object* v_prio_2247_, uint8_t v_sync_2248_, lean_object* v_rx_2249_){
_start:
{
lean_object* v_task_2250_; lean_object* v___f_2251_; lean_object* v___x_2252_; 
v_task_2250_ = lean_ctor_get(v_other_2245_, 0);
lean_inc_ref(v_task_2250_);
lean_dec_ref(v_other_2245_);
v___f_2251_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2251_, 0, v_f_2246_);
lean_closure_set(v___f_2251_, 1, v_rx_2249_);
v___x_2252_ = lean_task_map(v___f_2251_, v_task_2250_, v_prio_2247_, v_sync_2248_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___lam__1___boxed(lean_object* v_other_2253_, lean_object* v_f_2254_, lean_object* v_prio_2255_, lean_object* v_sync_2256_, lean_object* v_rx_2257_){
_start:
{
uint8_t v_sync_boxed_2258_; lean_object* v_res_2259_; 
v_sync_boxed_2258_ = lean_unbox(v_sync_2256_);
v_res_2259_ = l_Lake_Job_zipResultWith___redArg___lam__1(v_other_2253_, v_f_2254_, v_prio_2255_, v_sync_boxed_2258_, v_rx_2257_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg(lean_object* v_inst_2260_, lean_object* v_f_2261_, lean_object* v_self_2262_, lean_object* v_other_2263_, lean_object* v_prio_2264_, uint8_t v_sync_2265_){
_start:
{
lean_object* v_task_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2279_; 
v_task_2266_ = lean_ctor_get(v_self_2262_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v_self_2262_);
if (v_isSharedCheck_2279_ == 0)
{
lean_object* v_unused_2280_; lean_object* v_unused_2281_; 
v_unused_2280_ = lean_ctor_get(v_self_2262_, 2);
lean_dec(v_unused_2280_);
v_unused_2281_ = lean_ctor_get(v_self_2262_, 1);
lean_dec(v_unused_2281_);
v___x_2268_ = v_self_2262_;
v_isShared_2269_ = v_isSharedCheck_2279_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_task_2266_);
lean_dec(v_self_2262_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2279_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; lean_object* v___f_2271_; uint8_t v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; uint8_t v___x_2275_; lean_object* v___x_2277_; 
v___x_2270_ = lean_box(v_sync_2265_);
lean_inc(v_prio_2264_);
v___f_2271_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2271_, 0, v_other_2263_);
lean_closure_set(v___f_2271_, 1, v_f_2261_);
lean_closure_set(v___f_2271_, 2, v_prio_2264_);
lean_closure_set(v___f_2271_, 3, v___x_2270_);
v___x_2272_ = 1;
v___x_2273_ = lean_task_bind(v_task_2266_, v___f_2271_, v_prio_2264_, v___x_2272_);
v___x_2274_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2275_ = 0;
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 2, v___x_2274_);
lean_ctor_set(v___x_2268_, 1, v_inst_2260_);
lean_ctor_set(v___x_2268_, 0, v___x_2273_);
v___x_2277_ = v___x_2268_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2273_);
lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_inst_2260_);
lean_ctor_set(v_reuseFailAlloc_2278_, 2, v___x_2274_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
lean_ctor_set_uint8(v___x_2277_, sizeof(void*)*3, v___x_2275_);
return v___x_2277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___redArg___boxed(lean_object* v_inst_2282_, lean_object* v_f_2283_, lean_object* v_self_2284_, lean_object* v_other_2285_, lean_object* v_prio_2286_, lean_object* v_sync_2287_){
_start:
{
uint8_t v_sync_boxed_2288_; lean_object* v_res_2289_; 
v_sync_boxed_2288_ = lean_unbox(v_sync_2287_);
v_res_2289_ = l_Lake_Job_zipResultWith___redArg(v_inst_2282_, v_f_2283_, v_self_2284_, v_other_2285_, v_prio_2286_, v_sync_boxed_2288_);
return v_res_2289_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith(lean_object* v_00_u03b3_2290_, lean_object* v_00_u03b1_2291_, lean_object* v_00_u03b2_2292_, lean_object* v_inst_2293_, lean_object* v_f_2294_, lean_object* v_self_2295_, lean_object* v_other_2296_, lean_object* v_prio_2297_, uint8_t v_sync_2298_){
_start:
{
lean_object* v_task_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2312_; 
v_task_2299_ = lean_ctor_get(v_self_2295_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_self_2295_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; lean_object* v_unused_2314_; 
v_unused_2313_ = lean_ctor_get(v_self_2295_, 2);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_self_2295_, 1);
lean_dec(v_unused_2314_);
v___x_2301_ = v_self_2295_;
v_isShared_2302_ = v_isSharedCheck_2312_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_task_2299_);
lean_dec(v_self_2295_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2312_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2303_; lean_object* v___f_2304_; uint8_t v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; uint8_t v___x_2308_; lean_object* v___x_2310_; 
v___x_2303_ = lean_box(v_sync_2298_);
lean_inc(v_prio_2297_);
v___f_2304_ = lean_alloc_closure((void*)(l_Lake_Job_zipResultWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2304_, 0, v_other_2296_);
lean_closure_set(v___f_2304_, 1, v_f_2294_);
lean_closure_set(v___f_2304_, 2, v_prio_2297_);
lean_closure_set(v___f_2304_, 3, v___x_2303_);
v___x_2305_ = 1;
v___x_2306_ = lean_task_bind(v_task_2299_, v___f_2304_, v_prio_2297_, v___x_2305_);
v___x_2307_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2308_ = 0;
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 2, v___x_2307_);
lean_ctor_set(v___x_2301_, 1, v_inst_2293_);
lean_ctor_set(v___x_2301_, 0, v___x_2306_);
v___x_2310_ = v___x_2301_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_inst_2293_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v___x_2307_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*3, v___x_2308_);
return v___x_2310_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipResultWith___boxed(lean_object* v_00_u03b3_2315_, lean_object* v_00_u03b1_2316_, lean_object* v_00_u03b2_2317_, lean_object* v_inst_2318_, lean_object* v_f_2319_, lean_object* v_self_2320_, lean_object* v_other_2321_, lean_object* v_prio_2322_, lean_object* v_sync_2323_){
_start:
{
uint8_t v_sync_boxed_2324_; lean_object* v_res_2325_; 
v_sync_boxed_2324_ = lean_unbox(v_sync_2323_);
v_res_2325_ = l_Lake_Job_zipResultWith(v_00_u03b3_2315_, v_00_u03b1_2316_, v_00_u03b2_2317_, v_inst_2318_, v_f_2319_, v_self_2320_, v_other_2321_, v_prio_2322_, v_sync_boxed_2324_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__0(lean_object* v_rx_2326_, lean_object* v_f_2327_, lean_object* v_ry_2328_){
_start:
{
lean_object* v___y_2330_; lean_object* v___y_2331_; lean_object* v___y_2332_; lean_object* v___y_2336_; lean_object* v___y_2337_; lean_object* v___y_2338_; lean_object* v_a_2341_; 
if (lean_obj_tag(v_rx_2326_) == 0)
{
if (lean_obj_tag(v_ry_2328_) == 0)
{
lean_object* v_a_2343_; lean_object* v_a_2344_; lean_object* v_a_2345_; lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2355_; 
v_a_2343_ = lean_ctor_get(v_rx_2326_, 0);
lean_inc(v_a_2343_);
v_a_2344_ = lean_ctor_get(v_rx_2326_, 1);
lean_inc(v_a_2344_);
lean_dec_ref(v_rx_2326_);
v_a_2345_ = lean_ctor_get(v_ry_2328_, 0);
v_a_2346_ = lean_ctor_get(v_ry_2328_, 1);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_ry_2328_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2348_ = v_ry_2328_;
v_isShared_2349_ = v_isSharedCheck_2355_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_inc(v_a_2345_);
lean_dec(v_ry_2328_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2355_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2350_ = lean_apply_2(v_f_2327_, v_a_2343_, v_a_2345_);
v___x_2351_ = l_Lake_JobState_merge(v_a_2344_, v_a_2346_);
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 1, v___x_2351_);
lean_ctor_set(v___x_2348_, 0, v___x_2350_);
v___x_2353_ = v___x_2348_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2354_, 1, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
else
{
lean_object* v_a_2356_; 
lean_dec(v_f_2327_);
v_a_2356_ = lean_ctor_get(v_rx_2326_, 1);
lean_inc(v_a_2356_);
lean_dec_ref(v_rx_2326_);
v_a_2341_ = v_a_2356_;
goto v___jp_2340_;
}
}
else
{
lean_dec(v_f_2327_);
if (lean_obj_tag(v_rx_2326_) == 0)
{
lean_object* v_a_2357_; 
v_a_2357_ = lean_ctor_get(v_rx_2326_, 1);
lean_inc(v_a_2357_);
lean_dec_ref(v_rx_2326_);
v_a_2341_ = v_a_2357_;
goto v___jp_2340_;
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2359_; 
v_a_2358_ = lean_ctor_get(v_rx_2326_, 1);
lean_inc(v_a_2358_);
lean_dec_ref(v_rx_2326_);
v___x_2359_ = lean_unsigned_to_nat(0u);
v___y_2336_ = v_ry_2328_;
v___y_2337_ = v___x_2359_;
v___y_2338_ = v_a_2358_;
goto v___jp_2335_;
}
}
v___jp_2329_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = l_Lake_JobState_merge(v___y_2330_, v___y_2332_);
v___x_2334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___y_2331_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
return v___x_2334_;
}
v___jp_2335_:
{
lean_object* v_a_2339_; 
v_a_2339_ = lean_ctor_get(v___y_2336_, 1);
lean_inc(v_a_2339_);
lean_dec_ref(v___y_2336_);
v___y_2330_ = v___y_2338_;
v___y_2331_ = v___y_2337_;
v___y_2332_ = v_a_2339_;
goto v___jp_2329_;
}
v___jp_2340_:
{
lean_object* v___x_2342_; 
v___x_2342_ = lean_unsigned_to_nat(0u);
v___y_2336_ = v_ry_2328_;
v___y_2337_ = v___x_2342_;
v___y_2338_ = v_a_2341_;
goto v___jp_2335_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1(lean_object* v_other_2360_, lean_object* v_f_2361_, lean_object* v_prio_2362_, uint8_t v_sync_2363_, lean_object* v_rx_2364_){
_start:
{
lean_object* v_task_2365_; lean_object* v___f_2366_; lean_object* v___x_2367_; 
v_task_2365_ = lean_ctor_get(v_other_2360_, 0);
lean_inc_ref(v_task_2365_);
lean_dec_ref(v_other_2360_);
v___f_2366_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2366_, 0, v_rx_2364_);
lean_closure_set(v___f_2366_, 1, v_f_2361_);
v___x_2367_ = lean_task_map(v___f_2366_, v_task_2365_, v_prio_2362_, v_sync_2363_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___lam__1___boxed(lean_object* v_other_2368_, lean_object* v_f_2369_, lean_object* v_prio_2370_, lean_object* v_sync_2371_, lean_object* v_rx_2372_){
_start:
{
uint8_t v_sync_boxed_2373_; lean_object* v_res_2374_; 
v_sync_boxed_2373_ = lean_unbox(v_sync_2371_);
v_res_2374_ = l_Lake_Job_zipWith___redArg___lam__1(v_other_2368_, v_f_2369_, v_prio_2370_, v_sync_boxed_2373_, v_rx_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg(lean_object* v_inst_2375_, lean_object* v_f_2376_, lean_object* v_self_2377_, lean_object* v_other_2378_, lean_object* v_prio_2379_, uint8_t v_sync_2380_){
_start:
{
lean_object* v_task_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2394_; 
v_task_2381_ = lean_ctor_get(v_self_2377_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_self_2377_);
if (v_isSharedCheck_2394_ == 0)
{
lean_object* v_unused_2395_; lean_object* v_unused_2396_; 
v_unused_2395_ = lean_ctor_get(v_self_2377_, 2);
lean_dec(v_unused_2395_);
v_unused_2396_ = lean_ctor_get(v_self_2377_, 1);
lean_dec(v_unused_2396_);
v___x_2383_ = v_self_2377_;
v_isShared_2384_ = v_isSharedCheck_2394_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_task_2381_);
lean_dec(v_self_2377_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2394_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2385_; lean_object* v___f_2386_; uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; uint8_t v___x_2390_; lean_object* v___x_2392_; 
v___x_2385_ = lean_box(v_sync_2380_);
lean_inc(v_prio_2379_);
v___f_2386_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2386_, 0, v_other_2378_);
lean_closure_set(v___f_2386_, 1, v_f_2376_);
lean_closure_set(v___f_2386_, 2, v_prio_2379_);
lean_closure_set(v___f_2386_, 3, v___x_2385_);
v___x_2387_ = 1;
v___x_2388_ = lean_task_bind(v_task_2381_, v___f_2386_, v_prio_2379_, v___x_2387_);
v___x_2389_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2390_ = 0;
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 2, v___x_2389_);
lean_ctor_set(v___x_2383_, 1, v_inst_2375_);
lean_ctor_set(v___x_2383_, 0, v___x_2388_);
v___x_2392_ = v___x_2383_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v___x_2388_);
lean_ctor_set(v_reuseFailAlloc_2393_, 1, v_inst_2375_);
lean_ctor_set(v_reuseFailAlloc_2393_, 2, v___x_2389_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
lean_ctor_set_uint8(v___x_2392_, sizeof(void*)*3, v___x_2390_);
return v___x_2392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___redArg___boxed(lean_object* v_inst_2397_, lean_object* v_f_2398_, lean_object* v_self_2399_, lean_object* v_other_2400_, lean_object* v_prio_2401_, lean_object* v_sync_2402_){
_start:
{
uint8_t v_sync_boxed_2403_; lean_object* v_res_2404_; 
v_sync_boxed_2403_ = lean_unbox(v_sync_2402_);
v_res_2404_ = l_Lake_Job_zipWith___redArg(v_inst_2397_, v_f_2398_, v_self_2399_, v_other_2400_, v_prio_2401_, v_sync_boxed_2403_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__0(lean_object* v_rx_2405_, lean_object* v_f_2406_, lean_object* v_ry_2407_){
_start:
{
lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___y_2417_; lean_object* v_a_2420_; lean_object* v_rb_2421_; 
if (lean_obj_tag(v_rx_2405_) == 0)
{
if (lean_obj_tag(v_ry_2407_) == 0)
{
lean_object* v_a_2423_; lean_object* v_a_2424_; lean_object* v_a_2425_; lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2435_; 
v_a_2423_ = lean_ctor_get(v_rx_2405_, 0);
lean_inc(v_a_2423_);
v_a_2424_ = lean_ctor_get(v_rx_2405_, 1);
lean_inc(v_a_2424_);
lean_dec_ref(v_rx_2405_);
v_a_2425_ = lean_ctor_get(v_ry_2407_, 0);
v_a_2426_ = lean_ctor_get(v_ry_2407_, 1);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_ry_2407_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2428_ = v_ry_2407_;
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_inc(v_a_2425_);
lean_dec(v_ry_2407_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2435_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2430_ = lean_apply_2(v_f_2406_, v_a_2423_, v_a_2425_);
v___x_2431_ = l_Lake_JobState_merge(v_a_2424_, v_a_2426_);
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 1, v___x_2431_);
lean_ctor_set(v___x_2428_, 0, v___x_2430_);
v___x_2433_ = v___x_2428_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2434_, 1, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2436_; 
lean_dec(v_f_2406_);
v_a_2436_ = lean_ctor_get(v_rx_2405_, 1);
lean_inc(v_a_2436_);
lean_dec_ref(v_rx_2405_);
v_a_2420_ = v_a_2436_;
v_rb_2421_ = v_ry_2407_;
goto v___jp_2419_;
}
}
else
{
lean_dec(v_f_2406_);
if (lean_obj_tag(v_rx_2405_) == 0)
{
lean_object* v_a_2437_; 
v_a_2437_ = lean_ctor_get(v_rx_2405_, 1);
lean_inc(v_a_2437_);
lean_dec_ref(v_rx_2405_);
v_a_2420_ = v_a_2437_;
v_rb_2421_ = v_ry_2407_;
goto v___jp_2419_;
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2439_; 
v_a_2438_ = lean_ctor_get(v_rx_2405_, 1);
lean_inc(v_a_2438_);
lean_dec_ref(v_rx_2405_);
v___x_2439_ = lean_unsigned_to_nat(0u);
v___y_2415_ = v_ry_2407_;
v___y_2416_ = v___x_2439_;
v___y_2417_ = v_a_2438_;
goto v___jp_2414_;
}
}
v___jp_2408_:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = l_Lake_JobState_merge(v___y_2409_, v___y_2411_);
v___x_2413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___y_2410_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
return v___x_2413_;
}
v___jp_2414_:
{
lean_object* v_a_2418_; 
v_a_2418_ = lean_ctor_get(v___y_2415_, 1);
lean_inc(v_a_2418_);
lean_dec_ref(v___y_2415_);
v___y_2409_ = v___y_2417_;
v___y_2410_ = v___y_2416_;
v___y_2411_ = v_a_2418_;
goto v___jp_2408_;
}
v___jp_2419_:
{
lean_object* v___x_2422_; 
v___x_2422_ = lean_unsigned_to_nat(0u);
v___y_2415_ = v_rb_2421_;
v___y_2416_ = v___x_2422_;
v___y_2417_ = v_a_2420_;
goto v___jp_2414_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1(lean_object* v_other_2440_, lean_object* v_f_2441_, lean_object* v_prio_2442_, uint8_t v_sync_2443_, lean_object* v_rx_2444_){
_start:
{
lean_object* v_task_2445_; lean_object* v___f_2446_; lean_object* v___x_2447_; 
v_task_2445_ = lean_ctor_get(v_other_2440_, 0);
lean_inc_ref(v_task_2445_);
lean_dec_ref(v_other_2440_);
v___f_2446_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__0), 3, 2);
lean_closure_set(v___f_2446_, 0, v_rx_2444_);
lean_closure_set(v___f_2446_, 1, v_f_2441_);
v___x_2447_ = lean_task_map(v___f_2446_, v_task_2445_, v_prio_2442_, v_sync_2443_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___lam__1___boxed(lean_object* v_other_2448_, lean_object* v_f_2449_, lean_object* v_prio_2450_, lean_object* v_sync_2451_, lean_object* v_rx_2452_){
_start:
{
uint8_t v_sync_boxed_2453_; lean_object* v_res_2454_; 
v_sync_boxed_2453_ = lean_unbox(v_sync_2451_);
v_res_2454_ = l_Lake_Job_zipWith___lam__1(v_other_2448_, v_f_2449_, v_prio_2450_, v_sync_boxed_2453_, v_rx_2452_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith(lean_object* v_00_u03b3_2455_, lean_object* v_00_u03b1_2456_, lean_object* v_00_u03b2_2457_, lean_object* v_inst_2458_, lean_object* v_f_2459_, lean_object* v_self_2460_, lean_object* v_other_2461_, lean_object* v_prio_2462_, uint8_t v_sync_2463_){
_start:
{
lean_object* v_task_2464_; lean_object* v___x_2466_; uint8_t v_isShared_2467_; uint8_t v_isSharedCheck_2477_; 
v_task_2464_ = lean_ctor_get(v_self_2460_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_self_2460_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; lean_object* v_unused_2479_; 
v_unused_2478_ = lean_ctor_get(v_self_2460_, 2);
lean_dec(v_unused_2478_);
v_unused_2479_ = lean_ctor_get(v_self_2460_, 1);
lean_dec(v_unused_2479_);
v___x_2466_ = v_self_2460_;
v_isShared_2467_ = v_isSharedCheck_2477_;
goto v_resetjp_2465_;
}
else
{
lean_inc(v_task_2464_);
lean_dec(v_self_2460_);
v___x_2466_ = lean_box(0);
v_isShared_2467_ = v_isSharedCheck_2477_;
goto v_resetjp_2465_;
}
v_resetjp_2465_:
{
lean_object* v___x_2468_; lean_object* v___f_2469_; uint8_t v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; lean_object* v___x_2475_; 
v___x_2468_ = lean_box(v_sync_2463_);
lean_inc(v_prio_2462_);
v___f_2469_ = lean_alloc_closure((void*)(l_Lake_Job_zipWith___lam__1___boxed), 5, 4);
lean_closure_set(v___f_2469_, 0, v_other_2461_);
lean_closure_set(v___f_2469_, 1, v_f_2459_);
lean_closure_set(v___f_2469_, 2, v_prio_2462_);
lean_closure_set(v___f_2469_, 3, v___x_2468_);
v___x_2470_ = 1;
v___x_2471_ = lean_task_bind(v_task_2464_, v___f_2469_, v_prio_2462_, v___x_2470_);
v___x_2472_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2473_ = 0;
if (v_isShared_2467_ == 0)
{
lean_ctor_set(v___x_2466_, 2, v___x_2472_);
lean_ctor_set(v___x_2466_, 1, v_inst_2458_);
lean_ctor_set(v___x_2466_, 0, v___x_2471_);
v___x_2475_ = v___x_2466_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_inst_2458_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v___x_2472_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_ctor_set_uint8(v___x_2475_, sizeof(void*)*3, v___x_2473_);
return v___x_2475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_zipWith___boxed(lean_object* v_00_u03b3_2480_, lean_object* v_00_u03b1_2481_, lean_object* v_00_u03b2_2482_, lean_object* v_inst_2483_, lean_object* v_f_2484_, lean_object* v_self_2485_, lean_object* v_other_2486_, lean_object* v_prio_2487_, lean_object* v_sync_2488_){
_start:
{
uint8_t v_sync_boxed_2489_; lean_object* v_res_2490_; 
v_sync_boxed_2489_ = lean_unbox(v_sync_2488_);
v_res_2490_ = l_Lake_Job_zipWith(v_00_u03b3_2480_, v_00_u03b1_2481_, v_00_u03b2_2482_, v_inst_2483_, v_f_2484_, v_self_2485_, v_other_2486_, v_prio_2487_, v_sync_boxed_2489_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__0(lean_object* v___x_2491_, lean_object* v_rx_2492_, lean_object* v_ry_2493_){
_start:
{
lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2514_; lean_object* v___y_2515_; 
if (lean_obj_tag(v_rx_2492_) == 0)
{
if (lean_obj_tag(v_ry_2493_) == 0)
{
lean_object* v_a_2517_; lean_object* v_a_2518_; lean_object* v_a_2519_; lean_object* v___x_2521_; uint8_t v_isShared_2522_; uint8_t v_isSharedCheck_2541_; 
lean_dec(v___x_2491_);
v_a_2517_ = lean_ctor_get(v_rx_2492_, 0);
lean_inc(v_a_2517_);
v_a_2518_ = lean_ctor_get(v_rx_2492_, 1);
lean_inc(v_a_2518_);
lean_dec_ref(v_rx_2492_);
v_a_2519_ = lean_ctor_get(v_ry_2493_, 1);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_ry_2493_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v_ry_2493_, 0);
lean_dec(v_unused_2542_);
v___x_2521_ = v_ry_2493_;
v_isShared_2522_ = v_isSharedCheck_2541_;
goto v_resetjp_2520_;
}
else
{
lean_inc(v_a_2519_);
lean_dec(v_ry_2493_);
v___x_2521_ = lean_box(0);
v_isShared_2522_ = v_isSharedCheck_2541_;
goto v_resetjp_2520_;
}
v_resetjp_2520_:
{
lean_object* v___x_2523_; lean_object* v_log_2524_; uint8_t v_action_2525_; uint8_t v_wantsRebuild_2526_; lean_object* v_buildTime_2527_; lean_object* v_trace_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2538_; 
lean_inc(v_a_2518_);
v___x_2523_ = l_Lake_JobState_merge(v_a_2518_, v_a_2519_);
v_log_2524_ = lean_ctor_get(v___x_2523_, 0);
lean_inc_ref(v_log_2524_);
v_action_2525_ = lean_ctor_get_uint8(v___x_2523_, sizeof(void*)*3);
v_wantsRebuild_2526_ = lean_ctor_get_uint8(v___x_2523_, sizeof(void*)*3 + 1);
v_buildTime_2527_ = lean_ctor_get(v___x_2523_, 2);
lean_inc(v_buildTime_2527_);
lean_dec_ref(v___x_2523_);
v_trace_2528_ = lean_ctor_get(v_a_2518_, 1);
v_isSharedCheck_2538_ = !lean_is_exclusive(v_a_2518_);
if (v_isSharedCheck_2538_ == 0)
{
lean_object* v_unused_2539_; lean_object* v_unused_2540_; 
v_unused_2539_ = lean_ctor_get(v_a_2518_, 2);
lean_dec(v_unused_2539_);
v_unused_2540_ = lean_ctor_get(v_a_2518_, 0);
lean_dec(v_unused_2540_);
v___x_2530_ = v_a_2518_;
v_isShared_2531_ = v_isSharedCheck_2538_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_trace_2528_);
lean_dec(v_a_2518_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2538_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 2, v_buildTime_2527_);
lean_ctor_set(v___x_2530_, 0, v_log_2524_);
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_log_2524_);
lean_ctor_set(v_reuseFailAlloc_2537_, 1, v_trace_2528_);
lean_ctor_set(v_reuseFailAlloc_2537_, 2, v_buildTime_2527_);
v___x_2533_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
lean_object* v___x_2535_; 
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*3, v_action_2525_);
lean_ctor_set_uint8(v___x_2533_, sizeof(void*)*3 + 1, v_wantsRebuild_2526_);
if (v_isShared_2522_ == 0)
{
lean_ctor_set(v___x_2521_, 1, v___x_2533_);
lean_ctor_set(v___x_2521_, 0, v_a_2517_);
v___x_2535_ = v___x_2521_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2517_);
lean_ctor_set(v_reuseFailAlloc_2536_, 1, v___x_2533_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
}
else
{
lean_object* v_a_2543_; 
v_a_2543_ = lean_ctor_get(v_rx_2492_, 1);
lean_inc(v_a_2543_);
lean_dec_ref(v_rx_2492_);
v___y_2514_ = v_ry_2493_;
v___y_2515_ = v_a_2543_;
goto v___jp_2513_;
}
}
else
{
lean_object* v_a_2544_; 
v_a_2544_ = lean_ctor_get(v_rx_2492_, 1);
lean_inc(v_a_2544_);
lean_dec_ref(v_rx_2492_);
v___y_2514_ = v_ry_2493_;
v___y_2515_ = v_a_2544_;
goto v___jp_2513_;
}
v___jp_2494_:
{
lean_object* v___x_2497_; lean_object* v_log_2498_; uint8_t v_action_2499_; uint8_t v_wantsRebuild_2500_; lean_object* v_buildTime_2501_; lean_object* v_trace_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2510_; 
lean_inc_ref(v___y_2495_);
v___x_2497_ = l_Lake_JobState_merge(v___y_2495_, v___y_2496_);
v_log_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc_ref(v_log_2498_);
v_action_2499_ = lean_ctor_get_uint8(v___x_2497_, sizeof(void*)*3);
v_wantsRebuild_2500_ = lean_ctor_get_uint8(v___x_2497_, sizeof(void*)*3 + 1);
v_buildTime_2501_ = lean_ctor_get(v___x_2497_, 2);
lean_inc(v_buildTime_2501_);
lean_dec_ref(v___x_2497_);
v_trace_2502_ = lean_ctor_get(v___y_2495_, 1);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___y_2495_);
if (v_isSharedCheck_2510_ == 0)
{
lean_object* v_unused_2511_; lean_object* v_unused_2512_; 
v_unused_2511_ = lean_ctor_get(v___y_2495_, 2);
lean_dec(v_unused_2511_);
v_unused_2512_ = lean_ctor_get(v___y_2495_, 0);
lean_dec(v_unused_2512_);
v___x_2504_ = v___y_2495_;
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_trace_2502_);
lean_dec(v___y_2495_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2510_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 2, v_buildTime_2501_);
lean_ctor_set(v___x_2504_, 0, v_log_2498_);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_log_2498_);
lean_ctor_set(v_reuseFailAlloc_2509_, 1, v_trace_2502_);
lean_ctor_set(v_reuseFailAlloc_2509_, 2, v_buildTime_2501_);
v___x_2507_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
lean_object* v___x_2508_; 
lean_ctor_set_uint8(v___x_2507_, sizeof(void*)*3, v_action_2499_);
lean_ctor_set_uint8(v___x_2507_, sizeof(void*)*3 + 1, v_wantsRebuild_2500_);
v___x_2508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2491_);
lean_ctor_set(v___x_2508_, 1, v___x_2507_);
return v___x_2508_;
}
}
}
v___jp_2513_:
{
lean_object* v_a_2516_; 
v_a_2516_ = lean_ctor_get(v___y_2514_, 1);
lean_inc(v_a_2516_);
lean_dec_ref(v___y_2514_);
v___y_2495_ = v___y_2515_;
v___y_2496_ = v_a_2516_;
goto v___jp_2494_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1(lean_object* v_other_2545_, lean_object* v___x_2546_, uint8_t v___x_2547_, lean_object* v_rx_2548_){
_start:
{
lean_object* v_task_2549_; lean_object* v___f_2550_; lean_object* v___x_2551_; 
v_task_2549_ = lean_ctor_get(v_other_2545_, 0);
lean_inc_ref(v_task_2549_);
lean_dec_ref(v_other_2545_);
lean_inc(v___x_2546_);
v___f_2550_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2550_, 0, v___x_2546_);
lean_closure_set(v___f_2550_, 1, v_rx_2548_);
v___x_2551_ = lean_task_map(v___f_2550_, v_task_2549_, v___x_2546_, v___x_2547_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg___lam__1___boxed(lean_object* v_other_2552_, lean_object* v___x_2553_, lean_object* v___x_2554_, lean_object* v_rx_2555_){
_start:
{
uint8_t v___x_262__boxed_2556_; lean_object* v_res_2557_; 
v___x_262__boxed_2556_ = lean_unbox(v___x_2554_);
v_res_2557_ = l_Lake_Job_add___redArg___lam__1(v_other_2552_, v___x_2553_, v___x_262__boxed_2556_, v_rx_2555_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add___redArg(lean_object* v_self_2558_, lean_object* v_other_2559_){
_start:
{
lean_object* v_task_2560_; lean_object* v_kind_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2575_; 
v_task_2560_ = lean_ctor_get(v_self_2558_, 0);
v_kind_2561_ = lean_ctor_get(v_self_2558_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_self_2558_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v_self_2558_, 2);
lean_dec(v_unused_2576_);
v___x_2563_ = v_self_2558_;
v_isShared_2564_ = v_isSharedCheck_2575_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_kind_2561_);
lean_inc(v_task_2560_);
lean_dec(v_self_2558_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2575_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2565_; uint8_t v___x_2566_; lean_object* v___x_2567_; lean_object* v___f_2568_; uint8_t v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2573_; 
v___x_2565_ = lean_unsigned_to_nat(0u);
v___x_2566_ = 0;
v___x_2567_ = lean_box(v___x_2566_);
v___f_2568_ = lean_alloc_closure((void*)(l_Lake_Job_add___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2568_, 0, v_other_2559_);
lean_closure_set(v___f_2568_, 1, v___x_2565_);
lean_closure_set(v___f_2568_, 2, v___x_2567_);
v___x_2569_ = 1;
v___x_2570_ = lean_task_bind(v_task_2560_, v___f_2568_, v___x_2565_, v___x_2569_);
v___x_2571_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 2, v___x_2571_);
lean_ctor_set(v___x_2563_, 0, v___x_2570_);
v___x_2573_ = v___x_2563_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2570_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_kind_2561_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v___x_2571_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
lean_ctor_set_uint8(v___x_2573_, sizeof(void*)*3, v___x_2566_);
return v___x_2573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_add(lean_object* v_00_u03b1_2577_, lean_object* v_00_u03b2_2578_, lean_object* v_self_2579_, lean_object* v_other_2580_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lake_Job_add___redArg(v_self_2579_, v_other_2580_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__0(lean_object* v___x_2582_, lean_object* v_rx_2583_, lean_object* v_ry_2584_){
_start:
{
lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2591_; lean_object* v___y_2592_; 
if (lean_obj_tag(v_rx_2583_) == 0)
{
if (lean_obj_tag(v_ry_2584_) == 0)
{
lean_object* v_a_2594_; lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v___x_2582_);
v_a_2594_ = lean_ctor_get(v_rx_2583_, 1);
lean_inc(v_a_2594_);
lean_dec_ref(v_rx_2583_);
v_a_2595_ = lean_ctor_get(v_ry_2584_, 1);
v_isSharedCheck_2604_ = !lean_is_exclusive(v_ry_2584_);
if (v_isSharedCheck_2604_ == 0)
{
lean_object* v_unused_2605_; 
v_unused_2605_ = lean_ctor_get(v_ry_2584_, 0);
lean_dec(v_unused_2605_);
v___x_2597_ = v_ry_2584_;
v_isShared_2598_ = v_isSharedCheck_2604_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v_ry_2584_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2604_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2599_ = lean_box(0);
v___x_2600_ = l_Lake_JobState_merge(v_a_2594_, v_a_2595_);
if (v_isShared_2598_ == 0)
{
lean_ctor_set(v___x_2597_, 1, v___x_2600_);
lean_ctor_set(v___x_2597_, 0, v___x_2599_);
v___x_2602_ = v___x_2597_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2599_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v___x_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v_a_2606_; 
v_a_2606_ = lean_ctor_get(v_rx_2583_, 1);
lean_inc(v_a_2606_);
lean_dec_ref(v_rx_2583_);
v___y_2591_ = v_ry_2584_;
v___y_2592_ = v_a_2606_;
goto v___jp_2590_;
}
}
else
{
lean_object* v_a_2607_; 
v_a_2607_ = lean_ctor_get(v_rx_2583_, 1);
lean_inc(v_a_2607_);
lean_dec_ref(v_rx_2583_);
v___y_2591_ = v_ry_2584_;
v___y_2592_ = v_a_2607_;
goto v___jp_2590_;
}
v___jp_2585_:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = l_Lake_JobState_merge(v___y_2586_, v___y_2587_);
v___x_2589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2582_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
return v___x_2589_;
}
v___jp_2590_:
{
lean_object* v_a_2593_; 
v_a_2593_ = lean_ctor_get(v___y_2591_, 1);
lean_inc(v_a_2593_);
lean_dec_ref(v___y_2591_);
v___y_2586_ = v___y_2592_;
v___y_2587_ = v_a_2593_;
goto v___jp_2585_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1(lean_object* v_other_2608_, lean_object* v___x_2609_, uint8_t v___x_2610_, lean_object* v_rx_2611_){
_start:
{
lean_object* v_task_2612_; lean_object* v___f_2613_; lean_object* v___x_2614_; 
v_task_2612_ = lean_ctor_get(v_other_2608_, 0);
lean_inc_ref(v_task_2612_);
lean_dec_ref(v_other_2608_);
lean_inc(v___x_2609_);
v___f_2613_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2613_, 0, v___x_2609_);
lean_closure_set(v___f_2613_, 1, v_rx_2611_);
v___x_2614_ = lean_task_map(v___f_2613_, v_task_2612_, v___x_2609_, v___x_2610_);
return v___x_2614_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg___lam__1___boxed(lean_object* v_other_2615_, lean_object* v___x_2616_, lean_object* v___x_2617_, lean_object* v_rx_2618_){
_start:
{
uint8_t v___x_142__boxed_2619_; lean_object* v_res_2620_; 
v___x_142__boxed_2619_ = lean_unbox(v___x_2617_);
v_res_2620_ = l_Lake_Job_mix___redArg___lam__1(v_other_2615_, v___x_2616_, v___x_142__boxed_2619_, v_rx_2618_);
return v_res_2620_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix___redArg(lean_object* v_self_2621_, lean_object* v_other_2622_){
_start:
{
lean_object* v_task_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2638_; 
v_task_2623_ = lean_ctor_get(v_self_2621_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_self_2621_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; lean_object* v_unused_2640_; 
v_unused_2639_ = lean_ctor_get(v_self_2621_, 2);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v_self_2621_, 1);
lean_dec(v_unused_2640_);
v___x_2625_ = v_self_2621_;
v_isShared_2626_ = v_isSharedCheck_2638_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_task_2623_);
lean_dec(v_self_2621_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2638_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2627_; lean_object* v___x_2628_; uint8_t v___x_2629_; lean_object* v___x_2630_; lean_object* v___f_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; uint8_t v___x_2634_; lean_object* v___x_2636_; 
v___x_2627_ = l_Lake_instDataKindUnit;
v___x_2628_ = lean_unsigned_to_nat(0u);
v___x_2629_ = 1;
v___x_2630_ = lean_box(v___x_2629_);
v___f_2631_ = lean_alloc_closure((void*)(l_Lake_Job_mix___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2631_, 0, v_other_2622_);
lean_closure_set(v___f_2631_, 1, v___x_2628_);
lean_closure_set(v___f_2631_, 2, v___x_2630_);
v___x_2632_ = lean_task_bind(v_task_2623_, v___f_2631_, v___x_2628_, v___x_2629_);
v___x_2633_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2634_ = 0;
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 2, v___x_2633_);
lean_ctor_set(v___x_2625_, 1, v___x_2627_);
lean_ctor_set(v___x_2625_, 0, v___x_2632_);
v___x_2636_ = v___x_2625_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v___x_2633_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
lean_ctor_set_uint8(v___x_2636_, sizeof(void*)*3, v___x_2634_);
return v___x_2636_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mix(lean_object* v_00_u03b1_2641_, lean_object* v_00_u03b2_2642_, lean_object* v_self_2643_, lean_object* v_other_2644_){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lake_Job_mix___redArg(v_self_2643_, v_other_2644_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(lean_object* v_as_2646_, size_t v_i_2647_, size_t v_stop_2648_, lean_object* v_b_2649_){
_start:
{
uint8_t v___x_2650_; 
v___x_2650_ = lean_usize_dec_eq(v_i_2647_, v_stop_2648_);
if (v___x_2650_ == 0)
{
size_t v___x_2651_; size_t v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2651_ = ((size_t)1ULL);
v___x_2652_ = lean_usize_sub(v_i_2647_, v___x_2651_);
v___x_2653_ = lean_array_uget_borrowed(v_as_2646_, v___x_2652_);
lean_inc(v___x_2653_);
v___x_2654_ = l_Lake_Job_mix___redArg(v___x_2653_, v_b_2649_);
v_i_2647_ = v___x_2652_;
v_b_2649_ = v___x_2654_;
goto _start;
}
else
{
return v_b_2649_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2656_, lean_object* v_i_2657_, lean_object* v_stop_2658_, lean_object* v_b_2659_){
_start:
{
size_t v_i_boxed_2660_; size_t v_stop_boxed_2661_; lean_object* v_res_2662_; 
v_i_boxed_2660_ = lean_unbox_usize(v_i_2657_);
lean_dec(v_i_2657_);
v_stop_boxed_2661_ = lean_unbox_usize(v_stop_2658_);
lean_dec(v_stop_2658_);
v_res_2662_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2656_, v_i_boxed_2660_, v_stop_boxed_2661_, v_b_2659_);
lean_dec_ref(v_as_2656_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(lean_object* v_init_2663_, lean_object* v_l_2664_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2665_ = lean_array_mk(v_l_2664_);
v___x_2666_ = lean_array_get_size(v___x_2665_);
v___x_2667_ = lean_unsigned_to_nat(0u);
v___x_2668_ = lean_nat_dec_lt(v___x_2667_, v___x_2666_);
if (v___x_2668_ == 0)
{
lean_dec_ref(v___x_2665_);
return v_init_2663_;
}
else
{
size_t v___x_2669_; size_t v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = lean_usize_of_nat(v___x_2666_);
v___x_2670_ = ((size_t)0ULL);
v___x_2671_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v___x_2665_, v___x_2669_, v___x_2670_, v_init_2663_);
lean_dec_ref(v___x_2665_);
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList___redArg(lean_object* v_jobs_2672_, lean_object* v_traceCaption_2673_){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; uint8_t v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; 
v___x_2674_ = lean_box(0);
v___x_2675_ = lean_box(0);
v___x_2676_ = lean_unsigned_to_nat(0u);
v___x_2677_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2678_ = 0;
v___x_2679_ = 0;
v___x_2680_ = l_Lake_BuildTrace_nil(v_traceCaption_2673_);
v___x_2681_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2681_, 0, v___x_2677_);
lean_ctor_set(v___x_2681_, 1, v___x_2680_);
lean_ctor_set(v___x_2681_, 2, v___x_2676_);
lean_ctor_set_uint8(v___x_2681_, sizeof(void*)*3, v___x_2678_);
lean_ctor_set_uint8(v___x_2681_, sizeof(void*)*3 + 1, v___x_2679_);
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2674_);
lean_ctor_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = lean_task_pure(v___x_2682_);
v___x_2684_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2685_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2685_, 0, v___x_2683_);
lean_ctor_set(v___x_2685_, 1, v___x_2675_);
lean_ctor_set(v___x_2685_, 2, v___x_2684_);
lean_ctor_set_uint8(v___x_2685_, sizeof(void*)*3, v___x_2679_);
v___x_2686_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v___x_2685_, v_jobs_2672_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixList(lean_object* v_00_u03b1_2687_, lean_object* v_jobs_2688_, lean_object* v_traceCaption_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_Lake_Job_mixList___redArg(v_jobs_2688_, v_traceCaption_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_mixList_spec__0(lean_object* v_00_u03b1_2691_, lean_object* v_init_2692_, lean_object* v_l_2693_){
_start:
{
lean_object* v___x_2694_; 
v___x_2694_ = l_List_foldrTR___at___00Lake_Job_mixList_spec__0___redArg(v_init_2692_, v_l_2693_);
return v___x_2694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(lean_object* v_00_u03b1_2695_, lean_object* v_as_2696_, size_t v_i_2697_, size_t v_stop_2698_, lean_object* v_b_2699_){
_start:
{
lean_object* v___x_2700_; 
v___x_2700_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___redArg(v_as_2696_, v_i_2697_, v_stop_2698_, v_b_2699_);
return v___x_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2701_, lean_object* v_as_2702_, lean_object* v_i_2703_, lean_object* v_stop_2704_, lean_object* v_b_2705_){
_start:
{
size_t v_i_boxed_2706_; size_t v_stop_boxed_2707_; lean_object* v_res_2708_; 
v_i_boxed_2706_ = lean_unbox_usize(v_i_2703_);
lean_dec(v_i_2703_);
v_stop_boxed_2707_ = lean_unbox_usize(v_stop_2704_);
lean_dec(v_stop_2704_);
v_res_2708_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_mixList_spec__0_spec__0(v_00_u03b1_2701_, v_as_2702_, v_i_boxed_2706_, v_stop_boxed_2707_, v_b_2705_);
lean_dec_ref(v_as_2702_);
return v_res_2708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(lean_object* v_as_2709_, size_t v_i_2710_, size_t v_stop_2711_, lean_object* v_b_2712_){
_start:
{
uint8_t v___x_2713_; 
v___x_2713_ = lean_usize_dec_eq(v_i_2710_, v_stop_2711_);
if (v___x_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; size_t v___x_2716_; size_t v___x_2717_; 
v___x_2714_ = lean_array_uget_borrowed(v_as_2709_, v_i_2710_);
lean_inc(v___x_2714_);
v___x_2715_ = l_Lake_Job_mix___redArg(v_b_2712_, v___x_2714_);
v___x_2716_ = ((size_t)1ULL);
v___x_2717_ = lean_usize_add(v_i_2710_, v___x_2716_);
v_i_2710_ = v___x_2717_;
v_b_2712_ = v___x_2715_;
goto _start;
}
else
{
return v_b_2712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg___boxed(lean_object* v_as_2719_, lean_object* v_i_2720_, lean_object* v_stop_2721_, lean_object* v_b_2722_){
_start:
{
size_t v_i_boxed_2723_; size_t v_stop_boxed_2724_; lean_object* v_res_2725_; 
v_i_boxed_2723_ = lean_unbox_usize(v_i_2720_);
lean_dec(v_i_2720_);
v_stop_boxed_2724_ = lean_unbox_usize(v_stop_2721_);
lean_dec(v_stop_2721_);
v_res_2725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2719_, v_i_boxed_2723_, v_stop_boxed_2724_, v_b_2722_);
lean_dec_ref(v_as_2719_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg(lean_object* v_jobs_2726_, lean_object* v_traceCaption_2727_){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; uint8_t v___x_2732_; uint8_t v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; uint8_t v___x_2741_; 
v___x_2728_ = lean_box(0);
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_unsigned_to_nat(0u);
v___x_2731_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2732_ = 0;
v___x_2733_ = 0;
v___x_2734_ = l_Lake_BuildTrace_nil(v_traceCaption_2727_);
v___x_2735_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2735_, 0, v___x_2731_);
lean_ctor_set(v___x_2735_, 1, v___x_2734_);
lean_ctor_set(v___x_2735_, 2, v___x_2730_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*3, v___x_2732_);
lean_ctor_set_uint8(v___x_2735_, sizeof(void*)*3 + 1, v___x_2733_);
v___x_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2728_);
lean_ctor_set(v___x_2736_, 1, v___x_2735_);
v___x_2737_ = lean_task_pure(v___x_2736_);
v___x_2738_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2739_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2739_, 0, v___x_2737_);
lean_ctor_set(v___x_2739_, 1, v___x_2729_);
lean_ctor_set(v___x_2739_, 2, v___x_2738_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*3, v___x_2733_);
v___x_2740_ = lean_array_get_size(v_jobs_2726_);
v___x_2741_ = lean_nat_dec_lt(v___x_2730_, v___x_2740_);
if (v___x_2741_ == 0)
{
return v___x_2739_;
}
else
{
uint8_t v___x_2742_; 
v___x_2742_ = lean_nat_dec_le(v___x_2740_, v___x_2740_);
if (v___x_2742_ == 0)
{
if (v___x_2741_ == 0)
{
return v___x_2739_;
}
else
{
size_t v___x_2743_; size_t v___x_2744_; lean_object* v___x_2745_; 
v___x_2743_ = ((size_t)0ULL);
v___x_2744_ = lean_usize_of_nat(v___x_2740_);
v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2726_, v___x_2743_, v___x_2744_, v___x_2739_);
return v___x_2745_;
}
}
else
{
size_t v___x_2746_; size_t v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = ((size_t)0ULL);
v___x_2747_ = lean_usize_of_nat(v___x_2740_);
v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_jobs_2726_, v___x_2746_, v___x_2747_, v___x_2739_);
return v___x_2748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___redArg___boxed(lean_object* v_jobs_2749_, lean_object* v_traceCaption_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lake_Job_mixArray___redArg(v_jobs_2749_, v_traceCaption_2750_);
lean_dec_ref(v_jobs_2749_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray(lean_object* v_00_u03b1_2752_, lean_object* v_jobs_2753_, lean_object* v_traceCaption_2754_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lake_Job_mixArray___redArg(v_jobs_2753_, v_traceCaption_2754_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_mixArray___boxed(lean_object* v_00_u03b1_2756_, lean_object* v_jobs_2757_, lean_object* v_traceCaption_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l_Lake_Job_mixArray(v_00_u03b1_2756_, v_jobs_2757_, v_traceCaption_2758_);
lean_dec_ref(v_jobs_2757_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(lean_object* v_00_u03b1_2760_, lean_object* v_as_2761_, size_t v_i_2762_, size_t v_stop_2763_, lean_object* v_b_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___redArg(v_as_2761_, v_i_2762_, v_stop_2763_, v_b_2764_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0___boxed(lean_object* v_00_u03b1_2766_, lean_object* v_as_2767_, lean_object* v_i_2768_, lean_object* v_stop_2769_, lean_object* v_b_2770_){
_start:
{
size_t v_i_boxed_2771_; size_t v_stop_boxed_2772_; lean_object* v_res_2773_; 
v_i_boxed_2771_ = lean_unbox_usize(v_i_2768_);
lean_dec(v_i_2768_);
v_stop_boxed_2772_ = lean_unbox_usize(v_stop_2769_);
lean_dec(v_stop_2769_);
v_res_2773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_mixArray_spec__0(v_00_u03b1_2766_, v_as_2767_, v_i_boxed_2771_, v_stop_boxed_2772_, v_b_2770_);
lean_dec_ref(v_as_2767_);
return v_res_2773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0(lean_object* v___x_2774_, lean_object* v_rx_2775_, lean_object* v_ry_2776_){
_start:
{
lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2783_; lean_object* v___y_2784_; 
if (lean_obj_tag(v_rx_2775_) == 0)
{
if (lean_obj_tag(v_ry_2776_) == 0)
{
lean_object* v_a_2786_; lean_object* v_a_2787_; lean_object* v___x_2789_; uint8_t v_isShared_2790_; uint8_t v_isSharedCheck_2804_; 
lean_dec(v___x_2774_);
v_a_2786_ = lean_ctor_get(v_rx_2775_, 0);
v_a_2787_ = lean_ctor_get(v_rx_2775_, 1);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_rx_2775_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2789_ = v_rx_2775_;
v_isShared_2790_ = v_isSharedCheck_2804_;
goto v_resetjp_2788_;
}
else
{
lean_inc(v_a_2787_);
lean_inc(v_a_2786_);
lean_dec(v_rx_2775_);
v___x_2789_ = lean_box(0);
v_isShared_2790_ = v_isSharedCheck_2804_;
goto v_resetjp_2788_;
}
v_resetjp_2788_:
{
lean_object* v_a_2791_; lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2803_; 
v_a_2791_ = lean_ctor_get(v_ry_2776_, 0);
v_a_2792_ = lean_ctor_get(v_ry_2776_, 1);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_ry_2776_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2794_ = v_ry_2776_;
v_isShared_2795_ = v_isSharedCheck_2803_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_inc(v_a_2791_);
lean_dec(v_ry_2776_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2803_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2790_ == 0)
{
lean_ctor_set_tag(v___x_2789_, 1);
lean_ctor_set(v___x_2789_, 1, v_a_2791_);
v___x_2797_ = v___x_2789_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2786_);
lean_ctor_set(v_reuseFailAlloc_2802_, 1, v_a_2791_);
v___x_2797_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
lean_object* v___x_2798_; lean_object* v___x_2800_; 
v___x_2798_ = l_Lake_JobState_merge(v_a_2787_, v_a_2792_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 1, v___x_2798_);
lean_ctor_set(v___x_2794_, 0, v___x_2797_);
v___x_2800_ = v___x_2794_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2797_);
lean_ctor_set(v_reuseFailAlloc_2801_, 1, v___x_2798_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
else
{
lean_object* v_a_2805_; 
v_a_2805_ = lean_ctor_get(v_rx_2775_, 1);
lean_inc(v_a_2805_);
lean_dec_ref(v_rx_2775_);
v___y_2783_ = v_ry_2776_;
v___y_2784_ = v_a_2805_;
goto v___jp_2782_;
}
}
else
{
lean_object* v_a_2806_; 
v_a_2806_ = lean_ctor_get(v_rx_2775_, 1);
lean_inc(v_a_2806_);
lean_dec_ref(v_rx_2775_);
v___y_2783_ = v_ry_2776_;
v___y_2784_ = v_a_2806_;
goto v___jp_2782_;
}
v___jp_2777_:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = l_Lake_JobState_merge(v___y_2778_, v___y_2779_);
v___x_2781_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2774_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
return v___x_2781_;
}
v___jp_2782_:
{
lean_object* v_a_2785_; 
v_a_2785_ = lean_ctor_get(v___y_2783_, 1);
lean_inc(v_a_2785_);
lean_dec_ref(v___y_2783_);
v___y_2778_ = v___y_2784_;
v___y_2779_ = v_a_2785_;
goto v___jp_2777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(lean_object* v_b_2807_, lean_object* v___x_2808_, uint8_t v___x_2809_, lean_object* v_rx_2810_){
_start:
{
lean_object* v_task_2811_; lean_object* v___f_2812_; lean_object* v___x_2813_; 
v_task_2811_ = lean_ctor_get(v_b_2807_, 0);
lean_inc_ref(v_task_2811_);
lean_dec_ref(v_b_2807_);
lean_inc(v___x_2808_);
v___f_2812_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2812_, 0, v___x_2808_);
lean_closure_set(v___f_2812_, 1, v_rx_2810_);
v___x_2813_ = lean_task_map(v___f_2812_, v_task_2811_, v___x_2808_, v___x_2809_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed(lean_object* v_b_2814_, lean_object* v___x_2815_, lean_object* v___x_2816_, lean_object* v_rx_2817_){
_start:
{
uint8_t v___x_480__boxed_2818_; lean_object* v_res_2819_; 
v___x_480__boxed_2818_ = lean_unbox(v___x_2816_);
v_res_2819_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1(v_b_2814_, v___x_2815_, v___x_480__boxed_2818_, v_rx_2817_);
return v_res_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(lean_object* v_as_2820_, size_t v_i_2821_, size_t v_stop_2822_, lean_object* v_b_2823_){
_start:
{
uint8_t v___x_2824_; 
v___x_2824_ = lean_usize_dec_eq(v_i_2821_, v_stop_2822_);
if (v___x_2824_ == 0)
{
size_t v___x_2825_; size_t v___x_2826_; lean_object* v___x_2827_; lean_object* v_task_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2843_; 
v___x_2825_ = ((size_t)1ULL);
v___x_2826_ = lean_usize_sub(v_i_2821_, v___x_2825_);
v___x_2827_ = lean_array_uget(v_as_2820_, v___x_2826_);
v_task_2828_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; lean_object* v_unused_2845_; 
v_unused_2844_ = lean_ctor_get(v___x_2827_, 2);
lean_dec(v_unused_2844_);
v_unused_2845_ = lean_ctor_get(v___x_2827_, 1);
lean_dec(v_unused_2845_);
v___x_2830_ = v___x_2827_;
v_isShared_2831_ = v_isSharedCheck_2843_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_task_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2843_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; lean_object* v___x_2835_; lean_object* v___f_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2832_ = lean_box(0);
v___x_2833_ = lean_unsigned_to_nat(0u);
v___x_2834_ = 1;
v___x_2835_ = lean_box(v___x_2834_);
v___f_2836_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2836_, 0, v_b_2823_);
lean_closure_set(v___f_2836_, 1, v___x_2833_);
lean_closure_set(v___f_2836_, 2, v___x_2835_);
v___x_2837_ = lean_task_bind(v_task_2828_, v___f_2836_, v___x_2833_, v___x_2834_);
v___x_2838_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2831_ == 0)
{
lean_ctor_set(v___x_2830_, 2, v___x_2838_);
lean_ctor_set(v___x_2830_, 1, v___x_2832_);
lean_ctor_set(v___x_2830_, 0, v___x_2837_);
v___x_2840_ = v___x_2830_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___x_2832_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
lean_ctor_set_uint8(v___x_2840_, sizeof(void*)*3, v___x_2824_);
v_i_2821_ = v___x_2826_;
v_b_2823_ = v___x_2840_;
goto _start;
}
}
}
else
{
return v_b_2823_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg___boxed(lean_object* v_as_2846_, lean_object* v_i_2847_, lean_object* v_stop_2848_, lean_object* v_b_2849_){
_start:
{
size_t v_i_boxed_2850_; size_t v_stop_boxed_2851_; lean_object* v_res_2852_; 
v_i_boxed_2850_ = lean_unbox_usize(v_i_2847_);
lean_dec(v_i_2847_);
v_stop_boxed_2851_ = lean_unbox_usize(v_stop_2848_);
lean_dec(v_stop_2848_);
v_res_2852_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_2846_, v_i_boxed_2850_, v_stop_boxed_2851_, v_b_2849_);
lean_dec_ref(v_as_2846_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(lean_object* v_init_2853_, lean_object* v_l_2854_){
_start:
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; uint8_t v___x_2858_; 
v___x_2855_ = lean_array_mk(v_l_2854_);
v___x_2856_ = lean_array_get_size(v___x_2855_);
v___x_2857_ = lean_unsigned_to_nat(0u);
v___x_2858_ = lean_nat_dec_lt(v___x_2857_, v___x_2856_);
if (v___x_2858_ == 0)
{
lean_dec_ref(v___x_2855_);
return v_init_2853_;
}
else
{
size_t v___x_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v___x_2859_ = lean_usize_of_nat(v___x_2856_);
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v___x_2855_, v___x_2859_, v___x_2860_, v_init_2853_);
lean_dec_ref(v___x_2855_);
return v___x_2861_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList___redArg(lean_object* v_jobs_2862_, lean_object* v_traceCaption_2863_){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint8_t v___x_2868_; uint8_t v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_box(0);
v___x_2866_ = lean_unsigned_to_nat(0u);
v___x_2867_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2868_ = 0;
v___x_2869_ = 0;
v___x_2870_ = l_Lake_BuildTrace_nil(v_traceCaption_2863_);
v___x_2871_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2871_, 0, v___x_2867_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
lean_ctor_set(v___x_2871_, 2, v___x_2866_);
lean_ctor_set_uint8(v___x_2871_, sizeof(void*)*3, v___x_2868_);
lean_ctor_set_uint8(v___x_2871_, sizeof(void*)*3 + 1, v___x_2869_);
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v___x_2864_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = lean_task_pure(v___x_2872_);
v___x_2874_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2875_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2875_, 0, v___x_2873_);
lean_ctor_set(v___x_2875_, 1, v___x_2865_);
lean_ctor_set(v___x_2875_, 2, v___x_2874_);
lean_ctor_set_uint8(v___x_2875_, sizeof(void*)*3, v___x_2869_);
v___x_2876_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v___x_2875_, v_jobs_2862_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectList(lean_object* v_00_u03b1_2877_, lean_object* v_jobs_2878_, lean_object* v_traceCaption_2879_){
_start:
{
lean_object* v___x_2880_; 
v___x_2880_ = l_Lake_Job_collectList___redArg(v_jobs_2878_, v_traceCaption_2879_);
return v___x_2880_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lake_Job_collectList_spec__0(lean_object* v_00_u03b1_2881_, lean_object* v_init_2882_, lean_object* v_l_2883_){
_start:
{
lean_object* v___x_2884_; 
v___x_2884_ = l_List_foldrTR___at___00Lake_Job_collectList_spec__0___redArg(v_init_2882_, v_l_2883_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(lean_object* v_00_u03b1_2885_, lean_object* v_as_2886_, size_t v_i_2887_, size_t v_stop_2888_, lean_object* v_b_2889_){
_start:
{
lean_object* v___x_2890_; 
v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___redArg(v_as_2886_, v_i_2887_, v_stop_2888_, v_b_2889_);
return v___x_2890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2891_, lean_object* v_as_2892_, lean_object* v_i_2893_, lean_object* v_stop_2894_, lean_object* v_b_2895_){
_start:
{
size_t v_i_boxed_2896_; size_t v_stop_boxed_2897_; lean_object* v_res_2898_; 
v_i_boxed_2896_ = lean_unbox_usize(v_i_2893_);
lean_dec(v_i_2893_);
v_stop_boxed_2897_ = lean_unbox_usize(v_stop_2894_);
lean_dec(v_stop_2894_);
v_res_2898_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lake_Job_collectList_spec__0_spec__0(v_00_u03b1_2891_, v_as_2892_, v_i_boxed_2896_, v_stop_boxed_2897_, v_b_2895_);
lean_dec_ref(v_as_2892_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0(lean_object* v___x_2899_, lean_object* v_rx_2900_, lean_object* v_ry_2901_){
_start:
{
lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v___y_2908_; lean_object* v___y_2909_; 
if (lean_obj_tag(v_rx_2900_) == 0)
{
if (lean_obj_tag(v_ry_2901_) == 0)
{
lean_object* v_a_2911_; lean_object* v_a_2912_; lean_object* v_a_2913_; lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2923_; 
lean_dec(v___x_2899_);
v_a_2911_ = lean_ctor_get(v_rx_2900_, 0);
lean_inc(v_a_2911_);
v_a_2912_ = lean_ctor_get(v_rx_2900_, 1);
lean_inc(v_a_2912_);
lean_dec_ref(v_rx_2900_);
v_a_2913_ = lean_ctor_get(v_ry_2901_, 0);
v_a_2914_ = lean_ctor_get(v_ry_2901_, 1);
v_isSharedCheck_2923_ = !lean_is_exclusive(v_ry_2901_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2916_ = v_ry_2901_;
v_isShared_2917_ = v_isSharedCheck_2923_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_inc(v_a_2913_);
lean_dec(v_ry_2901_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2923_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2918_ = lean_array_push(v_a_2911_, v_a_2913_);
v___x_2919_ = l_Lake_JobState_merge(v_a_2912_, v_a_2914_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 1, v___x_2919_);
lean_ctor_set(v___x_2916_, 0, v___x_2918_);
v___x_2921_ = v___x_2916_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
else
{
lean_object* v_a_2924_; 
v_a_2924_ = lean_ctor_get(v_rx_2900_, 1);
lean_inc(v_a_2924_);
lean_dec_ref(v_rx_2900_);
v___y_2908_ = v_ry_2901_;
v___y_2909_ = v_a_2924_;
goto v___jp_2907_;
}
}
else
{
lean_object* v_a_2925_; 
v_a_2925_ = lean_ctor_get(v_rx_2900_, 1);
lean_inc(v_a_2925_);
lean_dec_ref(v_rx_2900_);
v___y_2908_ = v_ry_2901_;
v___y_2909_ = v_a_2925_;
goto v___jp_2907_;
}
v___jp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = l_Lake_JobState_merge(v___y_2903_, v___y_2904_);
v___x_2906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2899_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
return v___x_2906_;
}
v___jp_2907_:
{
lean_object* v_a_2910_; 
v_a_2910_ = lean_ctor_get(v___y_2908_, 1);
lean_inc(v_a_2910_);
lean_dec_ref(v___y_2908_);
v___y_2903_ = v___y_2909_;
v___y_2904_ = v_a_2910_;
goto v___jp_2902_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(lean_object* v___x_2926_, lean_object* v___x_2927_, uint8_t v___x_2928_, lean_object* v_rx_2929_){
_start:
{
lean_object* v_task_2930_; lean_object* v___f_2931_; lean_object* v___x_2932_; 
v_task_2930_ = lean_ctor_get(v___x_2926_, 0);
lean_inc_ref(v_task_2930_);
lean_dec_ref(v___x_2926_);
lean_inc(v___x_2927_);
v___f_2931_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__0), 3, 2);
lean_closure_set(v___f_2931_, 0, v___x_2927_);
lean_closure_set(v___f_2931_, 1, v_rx_2929_);
v___x_2932_ = lean_task_map(v___f_2931_, v_task_2930_, v___x_2927_, v___x_2928_);
return v___x_2932_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed(lean_object* v___x_2933_, lean_object* v___x_2934_, lean_object* v___x_2935_, lean_object* v_rx_2936_){
_start:
{
uint8_t v___x_411__boxed_2937_; lean_object* v_res_2938_; 
v___x_411__boxed_2937_ = lean_unbox(v___x_2935_);
v_res_2938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1(v___x_2933_, v___x_2934_, v___x_411__boxed_2937_, v_rx_2936_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(lean_object* v_as_2939_, size_t v_i_2940_, size_t v_stop_2941_, lean_object* v_b_2942_){
_start:
{
uint8_t v___x_2943_; 
v___x_2943_ = lean_usize_dec_eq(v_i_2940_, v_stop_2941_);
if (v___x_2943_ == 0)
{
lean_object* v_task_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2962_; 
v_task_2944_ = lean_ctor_get(v_b_2942_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_b_2942_);
if (v_isSharedCheck_2962_ == 0)
{
lean_object* v_unused_2963_; lean_object* v_unused_2964_; 
v_unused_2963_ = lean_ctor_get(v_b_2942_, 2);
lean_dec(v_unused_2963_);
v_unused_2964_ = lean_ctor_get(v_b_2942_, 1);
lean_dec(v_unused_2964_);
v___x_2946_ = v_b_2942_;
v_isShared_2947_ = v_isSharedCheck_2962_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_task_2944_);
lean_dec(v_b_2942_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2962_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; uint8_t v___x_2951_; lean_object* v___x_2952_; lean_object* v___f_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2957_; 
v___x_2948_ = lean_box(0);
v___x_2949_ = lean_array_uget_borrowed(v_as_2939_, v_i_2940_);
v___x_2950_ = lean_unsigned_to_nat(0u);
v___x_2951_ = 1;
v___x_2952_ = lean_box(v___x_2951_);
lean_inc(v___x_2949_);
v___f_2953_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_2953_, 0, v___x_2949_);
lean_closure_set(v___f_2953_, 1, v___x_2950_);
lean_closure_set(v___f_2953_, 2, v___x_2952_);
v___x_2954_ = lean_task_bind(v_task_2944_, v___f_2953_, v___x_2950_, v___x_2951_);
v___x_2955_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 2, v___x_2955_);
lean_ctor_set(v___x_2946_, 1, v___x_2948_);
lean_ctor_set(v___x_2946_, 0, v___x_2954_);
v___x_2957_ = v___x_2946_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2948_);
lean_ctor_set(v_reuseFailAlloc_2961_, 2, v___x_2955_);
v___x_2957_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
size_t v___x_2958_; size_t v___x_2959_; 
lean_ctor_set_uint8(v___x_2957_, sizeof(void*)*3, v___x_2943_);
v___x_2958_ = ((size_t)1ULL);
v___x_2959_ = lean_usize_add(v_i_2940_, v___x_2958_);
v_i_2940_ = v___x_2959_;
v_b_2942_ = v___x_2957_;
goto _start;
}
}
}
else
{
return v_b_2942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg___boxed(lean_object* v_as_2965_, lean_object* v_i_2966_, lean_object* v_stop_2967_, lean_object* v_b_2968_){
_start:
{
size_t v_i_boxed_2969_; size_t v_stop_boxed_2970_; lean_object* v_res_2971_; 
v_i_boxed_2969_ = lean_unbox_usize(v_i_2966_);
lean_dec(v_i_2966_);
v_stop_boxed_2970_ = lean_unbox_usize(v_stop_2967_);
lean_dec(v_stop_2967_);
v_res_2971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_2965_, v_i_boxed_2969_, v_stop_boxed_2970_, v_b_2968_);
lean_dec_ref(v_as_2965_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg(lean_object* v_jobs_2972_, lean_object* v_traceCaption_2973_){
_start:
{
lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; uint8_t v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v___x_2974_ = lean_array_get_size(v_jobs_2972_);
v___x_2975_ = lean_mk_empty_array_with_capacity(v___x_2974_);
v___x_2976_ = lean_box(0);
v___x_2977_ = lean_unsigned_to_nat(0u);
v___x_2978_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_2979_ = 0;
v___x_2980_ = 0;
v___x_2981_ = l_Lake_BuildTrace_nil(v_traceCaption_2973_);
v___x_2982_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2982_, 0, v___x_2978_);
lean_ctor_set(v___x_2982_, 1, v___x_2981_);
lean_ctor_set(v___x_2982_, 2, v___x_2977_);
lean_ctor_set_uint8(v___x_2982_, sizeof(void*)*3, v___x_2979_);
lean_ctor_set_uint8(v___x_2982_, sizeof(void*)*3 + 1, v___x_2980_);
v___x_2983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2983_, 0, v___x_2975_);
lean_ctor_set(v___x_2983_, 1, v___x_2982_);
v___x_2984_ = lean_task_pure(v___x_2983_);
v___x_2985_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_2986_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_2986_, 0, v___x_2984_);
lean_ctor_set(v___x_2986_, 1, v___x_2976_);
lean_ctor_set(v___x_2986_, 2, v___x_2985_);
lean_ctor_set_uint8(v___x_2986_, sizeof(void*)*3, v___x_2980_);
v___x_2987_ = lean_nat_dec_lt(v___x_2977_, v___x_2974_);
if (v___x_2987_ == 0)
{
return v___x_2986_;
}
else
{
uint8_t v___x_2988_; 
v___x_2988_ = lean_nat_dec_le(v___x_2974_, v___x_2974_);
if (v___x_2988_ == 0)
{
if (v___x_2987_ == 0)
{
return v___x_2986_;
}
else
{
size_t v___x_2989_; size_t v___x_2990_; lean_object* v___x_2991_; 
v___x_2989_ = ((size_t)0ULL);
v___x_2990_ = lean_usize_of_nat(v___x_2974_);
v___x_2991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_2972_, v___x_2989_, v___x_2990_, v___x_2986_);
return v___x_2991_;
}
}
else
{
size_t v___x_2992_; size_t v___x_2993_; lean_object* v___x_2994_; 
v___x_2992_ = ((size_t)0ULL);
v___x_2993_ = lean_usize_of_nat(v___x_2974_);
v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_jobs_2972_, v___x_2992_, v___x_2993_, v___x_2986_);
return v___x_2994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___redArg___boxed(lean_object* v_jobs_2995_, lean_object* v_traceCaption_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lake_Job_collectArray___redArg(v_jobs_2995_, v_traceCaption_2996_);
lean_dec_ref(v_jobs_2995_);
return v_res_2997_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray(lean_object* v_00_u03b1_2998_, lean_object* v_jobs_2999_, lean_object* v_traceCaption_3000_){
_start:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lake_Job_collectArray___redArg(v_jobs_2999_, v_traceCaption_3000_);
return v___x_3001_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectArray___boxed(lean_object* v_00_u03b1_3002_, lean_object* v_jobs_3003_, lean_object* v_traceCaption_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l_Lake_Job_collectArray(v_00_u03b1_3002_, v_jobs_3003_, v_traceCaption_3004_);
lean_dec_ref(v_jobs_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(lean_object* v_00_u03b1_3006_, lean_object* v_as_3007_, size_t v_i_3008_, size_t v_stop_3009_, lean_object* v_b_3010_){
_start:
{
lean_object* v___x_3011_; 
v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___redArg(v_as_3007_, v_i_3008_, v_stop_3009_, v_b_3010_);
return v___x_3011_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0___boxed(lean_object* v_00_u03b1_3012_, lean_object* v_as_3013_, lean_object* v_i_3014_, lean_object* v_stop_3015_, lean_object* v_b_3016_){
_start:
{
size_t v_i_boxed_3017_; size_t v_stop_boxed_3018_; lean_object* v_res_3019_; 
v_i_boxed_3017_ = lean_unbox_usize(v_i_3014_);
lean_dec(v_i_3014_);
v_stop_boxed_3018_ = lean_unbox_usize(v_stop_3015_);
lean_dec(v_stop_3015_);
v_res_3019_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lake_Job_collectArray_spec__0(v_00_u03b1_3012_, v_as_3013_, v_i_boxed_3017_, v_stop_boxed_3018_, v_b_3016_);
lean_dec_ref(v_as_3013_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Job_Monad_0__Lake_Job_collectVector_unsafe__1(lean_object* v_00_u03b1_3020_, lean_object* v_inst_3021_){
_start:
{
lean_object* v___x_3022_; 
v___x_3022_ = lean_box(0);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0(lean_object* v___x_3023_, lean_object* v_rx_3024_, lean_object* v_i_3025_, lean_object* v_ry_3026_){
_start:
{
lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3033_; lean_object* v___y_3034_; 
if (lean_obj_tag(v_rx_3024_) == 0)
{
if (lean_obj_tag(v_ry_3026_) == 0)
{
lean_object* v_a_3036_; lean_object* v_a_3037_; lean_object* v_a_3038_; lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3048_; 
lean_dec(v___x_3023_);
v_a_3036_ = lean_ctor_get(v_rx_3024_, 0);
lean_inc(v_a_3036_);
v_a_3037_ = lean_ctor_get(v_rx_3024_, 1);
lean_inc(v_a_3037_);
lean_dec_ref(v_rx_3024_);
v_a_3038_ = lean_ctor_get(v_ry_3026_, 0);
v_a_3039_ = lean_ctor_get(v_ry_3026_, 1);
v_isSharedCheck_3048_ = !lean_is_exclusive(v_ry_3026_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3041_ = v_ry_3026_;
v_isShared_3042_ = v_isSharedCheck_3048_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_inc(v_a_3038_);
lean_dec(v_ry_3026_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3048_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3046_; 
v___x_3043_ = lean_array_fset(v_a_3036_, v_i_3025_, v_a_3038_);
v___x_3044_ = l_Lake_JobState_merge(v_a_3037_, v_a_3039_);
if (v_isShared_3042_ == 0)
{
lean_ctor_set(v___x_3041_, 1, v___x_3044_);
lean_ctor_set(v___x_3041_, 0, v___x_3043_);
v___x_3046_ = v___x_3041_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3043_);
lean_ctor_set(v_reuseFailAlloc_3047_, 1, v___x_3044_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
else
{
lean_object* v_a_3049_; 
v_a_3049_ = lean_ctor_get(v_rx_3024_, 1);
lean_inc(v_a_3049_);
lean_dec_ref(v_rx_3024_);
v___y_3033_ = v_ry_3026_;
v___y_3034_ = v_a_3049_;
goto v___jp_3032_;
}
}
else
{
lean_object* v_a_3050_; 
v_a_3050_ = lean_ctor_get(v_rx_3024_, 1);
lean_inc(v_a_3050_);
lean_dec_ref(v_rx_3024_);
v___y_3033_ = v_ry_3026_;
v___y_3034_ = v_a_3050_;
goto v___jp_3032_;
}
v___jp_3027_:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3030_ = l_Lake_JobState_merge(v___y_3028_, v___y_3029_);
v___x_3031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3023_);
lean_ctor_set(v___x_3031_, 1, v___x_3030_);
return v___x_3031_;
}
v___jp_3032_:
{
lean_object* v_a_3035_; 
v_a_3035_ = lean_ctor_get(v___y_3033_, 1);
lean_inc(v_a_3035_);
lean_dec_ref(v___y_3033_);
v___y_3028_ = v___y_3034_;
v___y_3029_ = v_a_3035_;
goto v___jp_3027_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__0___boxed(lean_object* v___x_3051_, lean_object* v_rx_3052_, lean_object* v_i_3053_, lean_object* v_ry_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Lake_Job_collectVector___redArg___lam__0(v___x_3051_, v_rx_3052_, v_i_3053_, v_ry_3054_);
lean_dec(v_i_3053_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1(lean_object* v___x_3056_, lean_object* v___x_3057_, lean_object* v_i_3058_, uint8_t v___x_3059_, lean_object* v_rx_3060_){
_start:
{
lean_object* v_task_3061_; lean_object* v___f_3062_; lean_object* v___x_3063_; 
v_task_3061_ = lean_ctor_get(v___x_3056_, 0);
lean_inc_ref(v_task_3061_);
lean_dec_ref(v___x_3056_);
lean_inc(v___x_3057_);
v___f_3062_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_3062_, 0, v___x_3057_);
lean_closure_set(v___f_3062_, 1, v_rx_3060_);
lean_closure_set(v___f_3062_, 2, v_i_3058_);
v___x_3063_ = lean_task_map(v___f_3062_, v_task_3061_, v___x_3057_, v___x_3059_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__1___boxed(lean_object* v___x_3064_, lean_object* v___x_3065_, lean_object* v_i_3066_, lean_object* v___x_3067_, lean_object* v_rx_3068_){
_start:
{
uint8_t v___x_191__boxed_3069_; lean_object* v_res_3070_; 
v___x_191__boxed_3069_ = lean_unbox(v___x_3067_);
v_res_3070_ = l_Lake_Job_collectVector___redArg___lam__1(v___x_3064_, v___x_3065_, v_i_3066_, v___x_191__boxed_3069_, v_rx_3068_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2(lean_object* v_jobs_3071_, lean_object* v___x_3072_, lean_object* v_i_3073_, lean_object* v_h_3074_, lean_object* v_job_3075_){
_start:
{
lean_object* v_task_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3091_; 
v_task_3076_ = lean_ctor_get(v_job_3075_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_job_3075_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; lean_object* v_unused_3093_; 
v_unused_3092_ = lean_ctor_get(v_job_3075_, 2);
lean_dec(v_unused_3092_);
v_unused_3093_ = lean_ctor_get(v_job_3075_, 1);
lean_dec(v_unused_3093_);
v___x_3078_ = v_job_3075_;
v_isShared_3079_ = v_isSharedCheck_3091_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_task_3076_);
lean_dec(v_job_3075_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3091_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; uint8_t v___x_3082_; lean_object* v___x_3083_; lean_object* v___f_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; uint8_t v___x_3087_; lean_object* v___x_3089_; 
v___x_3080_ = lean_array_fget_borrowed(v_jobs_3071_, v_i_3073_);
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = 1;
v___x_3083_ = lean_box(v___x_3082_);
lean_inc(v___x_3080_);
v___f_3084_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__1___boxed), 5, 4);
lean_closure_set(v___f_3084_, 0, v___x_3080_);
lean_closure_set(v___f_3084_, 1, v___x_3081_);
lean_closure_set(v___f_3084_, 2, v_i_3073_);
lean_closure_set(v___f_3084_, 3, v___x_3083_);
v___x_3085_ = lean_task_bind(v_task_3076_, v___f_3084_, v___x_3081_, v___x_3082_);
v___x_3086_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3087_ = 0;
if (v_isShared_3079_ == 0)
{
lean_ctor_set(v___x_3078_, 2, v___x_3086_);
lean_ctor_set(v___x_3078_, 1, v___x_3072_);
lean_ctor_set(v___x_3078_, 0, v___x_3085_);
v___x_3089_ = v___x_3078_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v___x_3085_);
lean_ctor_set(v_reuseFailAlloc_3090_, 1, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3090_, 2, v___x_3086_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*3, v___x_3087_);
return v___x_3089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg___lam__2___boxed(lean_object* v_jobs_3094_, lean_object* v___x_3095_, lean_object* v_i_3096_, lean_object* v_h_3097_, lean_object* v_job_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lake_Job_collectVector___redArg___lam__2(v_jobs_3094_, v___x_3095_, v_i_3096_, v_h_3097_, v_job_3098_);
lean_dec_ref(v_jobs_3094_);
return v_res_3099_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector___redArg(lean_object* v_n_3100_, lean_object* v_jobs_3101_, lean_object* v_traceCaption_3102_){
_start:
{
lean_object* v_placeholder_3103_; lean_object* v___x_3104_; lean_object* v___f_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; uint8_t v___x_3109_; uint8_t v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v_placeholder_3103_ = lean_box(0);
v___x_3104_ = lean_box(0);
v___f_3105_ = lean_alloc_closure((void*)(l_Lake_Job_collectVector___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_3105_, 0, v_jobs_3101_);
lean_closure_set(v___f_3105_, 1, v___x_3104_);
lean_inc_n(v_n_3100_, 2);
v___x_3106_ = lean_mk_array(v_n_3100_, v_placeholder_3103_);
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = ((lean_object*)(l_Lake_Job_sync___redArg___closed__1));
v___x_3109_ = 0;
v___x_3110_ = 0;
v___x_3111_ = l_Lake_BuildTrace_nil(v_traceCaption_3102_);
v___x_3112_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3112_, 0, v___x_3108_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
lean_ctor_set(v___x_3112_, 2, v___x_3107_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*3, v___x_3109_);
lean_ctor_set_uint8(v___x_3112_, sizeof(void*)*3 + 1, v___x_3110_);
v___x_3113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3106_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = lean_task_pure(v___x_3113_);
v___x_3115_ = ((lean_object*)(l_panic___at___00Lake_Job_sync_spec__0___closed__0));
v___x_3116_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_3116_, 0, v___x_3114_);
lean_ctor_set(v___x_3116_, 1, v___x_3104_);
lean_ctor_set(v___x_3116_, 2, v___x_3115_);
lean_ctor_set_uint8(v___x_3116_, sizeof(void*)*3, v___x_3110_);
v___x_3117_ = l___private_Init_Data_Nat_Fold_0__Nat_foldTR_loop(lean_box(0), v_n_3100_, v___f_3105_, v_n_3100_, lean_box(0), v___x_3116_);
lean_dec(v_n_3100_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lake_Job_collectVector(lean_object* v_n_3118_, lean_object* v_00_u03b1_3119_, lean_object* v_inst_3120_, lean_object* v_jobs_3121_, lean_object* v_traceCaption_3122_){
_start:
{
lean_object* v___x_3123_; 
v___x_3123_ = l_Lake_Job_collectVector___redArg(v_n_3118_, v_jobs_3121_, v_traceCaption_3122_);
return v___x_3123_;
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
